package com.net2plan.general;
import java.io.File;

import com.net2plan.interfaces.networkDesign.Link;
import com.net2plan.interfaces.networkDesign.Net2PlanException;
import com.net2plan.interfaces.networkDesign.NetPlan;
import com.net2plan.interfaces.networkDesign.NetworkLayer;
import com.net2plan.utils.TimeTrace;

import cern.colt.matrix.tdouble.DoubleFactory2D;
import cern.colt.matrix.tdouble.DoubleMatrix1D;
import cern.colt.matrix.tdouble.DoubleMatrix2D;
import cern.colt.matrix.tdouble.algo.DenseDoubleAlgebra;
import cern.colt.matrix.tdouble.algo.decomposition.DenseDoubleEigenvalueDecomposition;
import cern.jet.math.tdouble.DoubleFunctions;

public class StatisticsCalculator_Algorithm 
{
	private static int S; // number of slots in every fiber link
	private static int B; // number of services
	private static int N;
	private int E;
	private static int C;
	DoubleMatrix2D occupancy_es;
	private static DoubleMatrix2D [] A_b;
	private static int [] slotsPerService;
	private static NetPlan np;
	private static NetworkLayer wdmLayer;
	private TimeTrace stat_connectivityEigenValuePerService; // simTimeOfChange ; new values of connectivity per service 	
	
	public StatisticsCalculator_Algorithm ()
	{		
	}
	
	public StatisticsCalculator_Algorithm (NetPlan np , NetworkLayer wdmLayer , int [] slotsPerService , int totalNumSlotsPerLink, int linkCapacity)
	{
		StatisticsCalculator_Algorithm.np = np;
		StatisticsCalculator_Algorithm.wdmLayer = wdmLayer;
		StatisticsCalculator_Algorithm.S = totalNumSlotsPerLink;
		StatisticsCalculator_Algorithm.N = np.getNumberOfNodes ();
		this.E = np.getNumberOfLinks(wdmLayer);
		StatisticsCalculator_Algorithm.B = slotsPerService.length; 					// Number of services
		StatisticsCalculator_Algorithm.setSlotsPerService(slotsPerService);			
		StatisticsCalculator_Algorithm.A_b = new DoubleMatrix2D [B];					// Adjacency Matrix for all the B services
		StatisticsCalculator_Algorithm.C = linkCapacity;
		for (int b = 0 ; b < B ; b ++)
		{
			final int numSlotsThisService = slotsPerService [b];
			A_b [b] = DoubleFactory2D.dense.make(N,N,totalNumSlotsPerLink - numSlotsThisService + 1);
			
		}
		this.occupancy_es = DoubleFactory2D.dense.make(E,S);
		this.stat_connectivityEigenValuePerService = new TimeTrace ();
	}

	
	public void setStatisticsCalculator (NetPlan np , NetworkLayer wdmLayer , int [] slotsPerService , int totalNumSlotsPerLink,int linkCapacity)
	{
		StatisticsCalculator_Algorithm.np = np;
		StatisticsCalculator_Algorithm.wdmLayer = wdmLayer;
		StatisticsCalculator_Algorithm.S = totalNumSlotsPerLink;
		StatisticsCalculator_Algorithm.N = np.getNumberOfNodes ();
		this.E = np.getNumberOfLinks(wdmLayer);
		StatisticsCalculator_Algorithm.B = slotsPerService.length; 					// Number of services
		StatisticsCalculator_Algorithm.setSlotsPerService(slotsPerService);			
		StatisticsCalculator_Algorithm.A_b = new DoubleMatrix2D [B];					// Adjacency Matrix for all the B services
		StatisticsCalculator_Algorithm.C = linkCapacity;
		for (int b = 0 ; b < B ; b ++)
		{
			final int numSlotsThisService = slotsPerService [b];
			A_b [b] = DoubleFactory2D.dense.make(N,N,totalNumSlotsPerLink - numSlotsThisService + 1);
			
		}
		this.occupancy_es = DoubleFactory2D.dense.make(E,S);
		this.stat_connectivityEigenValuePerService = new TimeTrace ();
	}
	
	
	public static double[] getAlgebraicConnectivityPerService (DoubleMatrix2D newOccupancy_es)
	{
		/* Initialize the adjacency matrices */
		for (int b = 0; b < B ; b ++) A_b [b] = DoubleFactory2D.dense.make(N,N);
		/* Update them according to the new occupancy state */
		for (Link link : np.getLinks(wdmLayer))
		{
			final int e = link.getIndex(); 
			final int a_e = link.getOriginNode().getIndex();
			final int b_e = link.getDestinationNode().getIndex();
			int lastOccupiedSlotFound = -1;
			for (int s = 0; s < S ; s ++)
			{
				if (newOccupancy_es.get(e, s) == 1)
				{
					final int sizeOfTheAllocationBlock = s - lastOccupiedSlotFound - 1;
					for (int b = 0; b < B ; b ++)
					{
						final int numSlotsThisService = getSlotsPerService() [b];
						final double numAllocationPossibilities = (sizeOfTheAllocationBlock < numSlotsThisService)? 0 : sizeOfTheAllocationBlock - numSlotsThisService + 1;
						A_b [b].set(a_e, b_e, A_b [b].get(a_e,b_e) + numAllocationPossibilities);
					}
					lastOccupiedSlotFound = s;
				}
			}
			/* At the end of the last slot, is as if we have one more slot occupied, closing the allocation block */
			final int sizeOfTheAllocationBlock = S - lastOccupiedSlotFound - 1;
			for (int b = 0; b < B ; b ++)
			{
				final int numSlotsThisService = getSlotsPerService() [b];
				final double numAllocationPossibilities = (sizeOfTheAllocationBlock < numSlotsThisService)? 0 : sizeOfTheAllocationBlock - numSlotsThisService + 1;
				A_b [b].set(a_e, b_e, A_b [b].get(a_e,b_e) + numAllocationPossibilities);
			}
		}
		
		/* This is for computing the eigenvalues of the matrices */
		DenseDoubleAlgebra alg = new DenseDoubleAlgebra ();
		double [] newValueOfConnectivity_b_Inputs = new double [B];
		double [] newValueOfConnectivity_b_Outputs = new double [B];
		double [] newValueOfConnectivity_b = new double[B];
		
		for (int b = 0 ; b < B ; b ++)
		{				
			DoubleMatrix2D laplMatrixIn = builtNormailizedLaplacianMatrix(C, A_b[b],"In");
			
	//		System.out.println("Incoming Laplacian Flag ");
			
			DenseDoubleEigenvalueDecomposition decIn = alg.eig(laplMatrixIn);
			DoubleMatrix1D realPartsIn = decIn.getRealEigenvalues().viewSorted();
			
			double auxAlgConnIn = 0.0;
			for (double realIn : realPartsIn.toArray())
			{
				if (realIn > 0.0000001){
					auxAlgConnIn = realIn;
					break; 
				}		
			}		
			newValueOfConnectivity_b_Inputs[b] = auxAlgConnIn;
			
			DoubleMatrix2D laplMatrixOut = builtNormailizedLaplacianMatrix(C,A_b[b],"Out");	
			
	//		System.out.println("Outgoing Laplacian Flag ");
			
			DenseDoubleEigenvalueDecomposition decOut = alg.eig(laplMatrixOut);
			DoubleMatrix1D realPartsOut = decOut.getRealEigenvalues().viewSorted();					
			
			double auxAlgConnOut = 0.0;
			for (double realOut : realPartsOut.toArray())
			{		
				if (realOut > 0.0000001)
				{
					auxAlgConnOut = realOut;
					break;
				}
			}
			newValueOfConnectivity_b_Outputs[b] = auxAlgConnOut;			

			// Return the mean between values of incoming and outgoing links connectivity
			newValueOfConnectivity_b[b] = (auxAlgConnOut+auxAlgConnIn)/2;	
			
	//		System.out.println("Ending Flag ");
				
		}
		return newValueOfConnectivity_b;				

	}


	private static DoubleMatrix2D builtNormailizedLaplacianMatrix(int linkCapacity, DoubleMatrix2D A, String InOut){
		
		DoubleMatrix2D lapMatrix = DoubleFactory2D.dense.make(N,N);
		DoubleMatrix2D diagK = DoubleFactory2D.dense.make(N,N);	
		
		DoubleMatrix2D aux = A.assign(DoubleFunctions.div(linkCapacity));
		
		for(int n = 0; n < N; n++)
		{
			if (InOut.equalsIgnoreCase("In"))
				diagK.set(n,n, aux.viewRow(n).zSum());	
			else if (InOut.equalsIgnoreCase("Out"))
				diagK.set(n,n, aux.viewColumn(n).zSum());		
			else
				throw new Net2PlanException("Wrong Input String");
		}
		lapMatrix = diagK.assign(aux,DoubleFunctions.minus);
		return lapMatrix;
	}
	
	public String finish (String fileInputs)
	{
		stat_connectivityEigenValuePerService.printToFile(new File (fileInputs));
		
		return "Done";
	}

	public static int [] getSlotsPerService() {
		return slotsPerService;
	}

	public static void setSlotsPerService(int [] slotsPerService) {
		StatisticsCalculator_Algorithm.slotsPerService = slotsPerService;
	}
}
