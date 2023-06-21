package mytweetyapp;

/*
 * The source code of the implementation of all algorithms for Computing and Verifying Scalable Approximate Preferences in the paper titled: "An Extension-based Approach for Computing and Verifying Preferences in Abstract Argumentation"
 * Submitted to Journal of Artificial Intelligence Research (JAIR) 2023.
 * Code author: Quratul-ain Mahesar, email: q.mahesar@hud.ac.uk
 * The code generates the data sets for the experiments on larger AAF sizes for checking the scalability of the Approximate algorithm.
 */

import java.io.BufferedWriter;
import java.io.File;
import java.io.FileWriter;
import java.io.IOException;
import java.util.ArrayList;
import java.util.Arrays;
import java.util.Collection;
import java.util.Collections;
import java.util.HashSet;
import java.util.Iterator;
import java.util.List;
import java.util.Random;
import java.util.Set;

import org.apache.commons.math3.util.Pair;
import org.apache.commons.math3.util.Precision;

import net.sf.tweety.arg.aba.syntax.Assumption;
import net.sf.tweety.arg.dung.*;
import net.sf.tweety.arg.dung.reasoner.AbstractExtensionReasoner;
import net.sf.tweety.arg.dung.semantics.Extension;
import net.sf.tweety.arg.dung.semantics.Semantics;
import net.sf.tweety.arg.dung.syntax.Argument;
import net.sf.tweety.arg.dung.syntax.Attack;
import net.sf.tweety.arg.dung.syntax.DungTheory;
import net.sf.tweety.arg.dung.util.DefaultDungTheoryGenerator;
import net.sf.tweety.arg.dung.util.DungTheoryGenerationParameters;
import net.sf.tweety.arg.dung.writer.TgfWriter;
import net.sf.tweety.commons.Formula;
import net.sf.tweety.commons.util.Triple;
import net.sf.tweety.logics.pl.sat.Sat4jSolver;
import net.sf.tweety.logics.pl.sat.SatSolver;

public class ArgumentationApproxPreferencesScale {
	
	
	public static boolean checkNoDefence(DungTheory at, Set<Argument> ext, Argument a, Argument b)
	{
		
		for (Argument c : ext)
		{
			if(c.equals(a) == false)
			{
				if(at.isAttackedBy(b, c) && (at.getAttackers(c).size() == 0))
				return false;
			}
		}
		return true;
		
	}
	
	public static boolean checkArgumentPreferences(DungTheory at, Argument c, Set<Set<Triple<Argument, String, Argument>>> prefSet)
	{		
		if(at.getAttackers(c).size() == 0)
			return true;
		for(Set<Triple<Argument, String, Argument>> pSet: prefSet)
		{
			for(Triple<Argument,String,Argument> p: pSet)
			{
				if(p.getFirst() == c)
				{
					return true;
				}
			}

		}
		
		return false;
	}
	
	public static boolean checkArgumentPreferencesApproximate(DungTheory at, Argument c, Set<Triple<Argument, String, Argument>> pSet)
	{		
		if(at.getAttackers(c).size() == 0)
			return true;
		for(Triple<Argument,String,Argument> p: pSet)
			{
				if(p.getFirst() == c)
				{
					return true;
				}
			}

		
		return false;
	}
	
	public static boolean checkNoDefence2(DungTheory at, Set<Argument> ext, Argument a, Argument b, Set<Set<Triple<Argument, String, Argument>>> prefSet)
	{
		
		for (Argument c : ext)
		{
			if( (c.equals(a) == false) && (checkArgumentPreferences(at, c,prefSet))  )
			{
				if(at.isAttackedBy(b, c))
				return false;
			}
		}
		return true;
		
	}
	
	
	public static boolean checkNoDefenceApproximate(DungTheory at, Set<Argument> ext, Argument a, Argument b, Set<Triple<Argument, String, Argument>> pSet)
	{
		
		for (Argument c : ext)
		{
			if( (c.equals(a) == false) && (checkArgumentPreferencesApproximate(at, c,pSet))  )
			{
				if(at.isAttackedBy(b, c))
				return false;
			}
		}
		return true;
		
	}
	
	//function to compute Case1 preferences
	
	public static Set<Triple<Argument, String, Argument>> computeCase1Preferences(DungTheory at, Set<Argument> ext)
	{
		
		
		//find all preferences a>b where b attacks a and there is no argument in extension that attacks b
		Set<Triple<Argument, String, Argument>> prefs = new HashSet<Triple<Argument, String, Argument>>();
				for (Argument a : ext) {
					for (Argument b : at.getAttackers(a)) {
				   if(checkNoDefence(at, ext, a, b))
				   {
						Triple<Argument, String, Argument> dPref1 = new Triple(a, ">", b);
						prefs.add(dPref1);
				   }
			}
		   
		}
		return prefs;
		
	}
	
	public static Set<Argument> getAttackedArguments(DungTheory at, Set<Argument> ext, Argument a)
	{
		Set<Argument> attackedArguments = new HashSet<Argument>();
		for (Argument b : at.getAttacked(a)) 
		{
			if(ext.contains(b)==false)
			{
				if(at.isAttackedBy(a, b) == false)
				{
					attackedArguments.add(b);
				}
			}
		}
		
		return attackedArguments;
	}
	
	//function to compute Case2 preferences combined together with Case1 preferences
	
	public static Set<Set<Triple<Argument, String, Argument>>> computeCase2Preferences(DungTheory at, Set<Argument> ext, Set<Triple<Argument, String, Argument>> prefs)
	{
		Set<Set<Triple<Argument, String, Argument>>> prefSet = new HashSet<Set<Triple<Argument, String, Argument>>>();

		prefSet.add(prefs);
		for (Argument a : ext) {
			for (Argument b : getAttackedArguments(at, ext, a)) 
			{
				Set<Set<Triple<Argument, String, Argument>>> prefSet1 = new HashSet<Set<Triple<Argument, String, Argument>>>();

				 for(Set<Triple<Argument, String, Argument>> pref: prefSet)
				   {
						Triple<Argument, String, Argument> dPref1 = new Triple(a, ">", b);
						Triple<Argument, String, Argument> dPref2 = new Triple(a, "=", b);
						
						 Set<Triple<Argument, String, Argument>> newpref1 = new HashSet<Triple<Argument, String, Argument>>();
						 Set<Triple<Argument, String, Argument>> newpref2 = new HashSet<Triple<Argument, String, Argument>>();
								
						Iterator iterator = pref.iterator();
						 while(iterator.hasNext())
						 {
						
						 Triple<Argument, String, Argument> p = (Triple<Argument, String, Argument>) iterator.next();
						 newpref1.add(p);
						 newpref2.add(p);
						 } 
				
						 newpref1.add(dPref1);
					
						newpref2.add(dPref2);
	
						 prefSet1.add(newpref1);
						 prefSet1.add(newpref2);
						 //System.out.println(prefSet1);
				   }
				 		prefSet = prefSet1;
	}
		}
		
		return prefSet;
	}
	
	
	public static boolean inPrefSet(Argument a, Argument b, Set<Set<Triple<Argument, String, Argument>>> prefSet)
	{
		for(Set<Triple<Argument, String, Argument>> pSet: prefSet)
		{
			for (Triple<Argument, String, Argument> p: pSet)
			{
				if ((p.getFirst() ==a) && (p.getThird()==b))
					return true;
				else if ((p.getFirst() ==b) && (p.getThird()==a))
					return true;
			}
		}
		return false;		
	}
	
	public static boolean inPrefs(Argument a, Argument b, Set<Triple<Argument, String, Argument>> pSet)
	{
			for (Triple<Argument, String, Argument> p: pSet)
			{
				if ((p.getFirst() ==a) && (p.getThird()==b))
					return true;
				else if ((p.getFirst() ==b) && (p.getThird()==a))
					return true;
			}
		return false;		
	}
	
	
	//function to compute Case3 preferences combined together with Case1 and Case2 preferences
	
	
	public static Set<Set<Triple<Argument, String, Argument>>> computeCase3Preferences(DungTheory at, Set<Argument> ext, Set<Set<Triple<Argument, String, Argument>>> prefSet)
	{
		for (Argument a : ext) {
			for (Argument b : at.getAttackers(a)) {
		   if((checkNoDefence2(at, ext, a, b, prefSet)==false) && (inPrefSet(a, b, prefSet)==false))
		   {
				Set<Set<Triple<Argument, String, Argument>>> prefSet1 = new HashSet<Set<Triple<Argument, String, Argument>>>();

				 for(Set<Triple<Argument, String, Argument>> pref: prefSet)
				   {
						Triple<Argument, String, Argument> dPref1 = new Triple(a, ">", b);
						Triple<Argument, String, Argument> dPref2 = new Triple(a, "=", b);
						Triple<Argument, String, Argument> dPref3 = new Triple(b, ">", a);
						
						 Set<Triple<Argument, String, Argument>> newpref1 = new HashSet<Triple<Argument, String, Argument>>();
						 Set<Triple<Argument, String, Argument>> newpref2 = new HashSet<Triple<Argument, String, Argument>>();
						 Set<Triple<Argument, String, Argument>> newpref3 = new HashSet<Triple<Argument, String, Argument>>();

		
						Iterator iterator = pref.iterator();
						 while(iterator.hasNext())
						 {

						 Triple<Argument, String, Argument> p = (Triple<Argument, String, Argument>) iterator.next();
						 newpref1.add(p);
						 newpref2.add(p);
						 newpref3.add(p);
						 } 

						 newpref1.add(dPref1);

						newpref2.add(dPref2);
						newpref3.add(dPref3);
						prefSet1.add(newpref1);
						prefSet1.add(newpref2);
						prefSet1.add(newpref3);
				   }
				 		prefSet = prefSet1;
		   }
	}
		}
		
		return prefSet;
	}
	
	//function that calls the functions for three cases to compute all preferences
	
	public static Set<Set<Triple<Argument, String, Argument>>> ComputeAllPreferences(DungTheory at, Set<Argument> ext)
	{

		Set<Triple<Argument, String, Argument>>  s1 = new HashSet<Triple<Argument, String, Argument>> ();

		s1= computeCase1Preferences(at, ext);

		Set<Set<Triple<Argument, String, Argument>>> s2 = new HashSet<Set<Triple<Argument, String, Argument>>>();
		s2 = computeCase2Preferences(at, ext, s1);
		
		Set<Set<Triple<Argument, String, Argument>>> s3 = new HashSet<Set<Triple<Argument, String, Argument>>>();
		s3 = computeCase3Preferences(at, ext, s2);

		return s3;
	

	}
	
	//function that computes and returns an approximate set of preferences between arguments
	
	public static Set<Triple<Argument, String, Argument>> ComputeApproximatePreferences(DungTheory at, Set<Argument> ext)
	{

		//Set<Triple<Argument, String, Argument>>  s1 = new HashSet<Triple<Argument, String, Argument>> ();
		

		//Compute Case 1 preferences
		
		//Find all preferences a>b where b attacks a and there is no argument in extension that attacks b
		Set<Triple<Argument, String, Argument>> prefs = new HashSet<Triple<Argument, String, Argument>>();
				for (Argument a : ext) {
					for (Argument b : at.getAttackers(a)) {
				   if(checkNoDefence(at, ext, a, b))
				   {
						Triple<Argument, String, Argument> dPref1 = new Triple(a, ">", b);
						prefs.add(dPref1);
				   }
			}
		   
		}

		
		//Compute Case 2 preferences		
				
				
				//Set<Set<Triple<Argument, String, Argument>>> prefSet = new HashSet<Set<Triple<Argument, String, Argument>>>();

				//prefSet.add(prefs);
				for (Argument a : ext) {
					for (Argument b : getAttackedArguments(at, ext, a)) 
					{
						List<Triple<Argument, String, Argument>> prefList = new ArrayList<Triple<Argument, String, Argument>>();
						Triple<Argument, String, Argument> dPref1 = new Triple(a, ">", b);
						Triple<Argument, String, Argument> dPref2 = new Triple(a, "=", b);
						
						prefList.add(dPref1);
						prefList.add(dPref2);
						
						Random rand = new Random();
					    Triple<Argument, String, Argument> randomPreference = prefList.get(rand.nextInt(prefList.size()));
					    
					    prefs.add(randomPreference);

					}
				}
		

				
	    //Compute Case 3 preferences		

				for (Argument a : ext) 
				{
					for (Argument b : at.getAttackers(a)) 
					{
						if((checkNoDefenceApproximate(at, ext, a, b, prefs)==false) && (inPrefs(a, b, prefs)==false))
						{
							List<Triple<Argument, String, Argument>> prefList = new ArrayList<Triple<Argument, String, Argument>>();
							Triple<Argument, String, Argument> dPref1 = new Triple(a, ">", b);
							Triple<Argument, String, Argument> dPref2 = new Triple(a, "=", b);
							Triple<Argument, String, Argument> dPref3 = new Triple(b, ">", a);
							prefList.add(dPref1);
							prefList.add(dPref2);
							prefList.add(dPref3);
						
							Random rand = new Random();
							Triple<Argument, String, Argument> randomPreference = prefList.get(rand.nextInt(prefList.size()));
					    
							prefs.add(randomPreference);					
						
						}
					}
				}
				
				

		return prefs;
	

	}
	
	/* function to print all preference sets */
	public static void printPreferenceSets(Set<Set<Triple<Argument, String, Argument>>> prefSet)
	{
		for(Set<Triple<Argument, String, Argument>> p: prefSet)
		{
			for( Triple<Argument, String, Argument> p1: p)
			{
				System.out.print("(" + p1.getFirst().toString() + " " + p1.getSecond().toString() + " " + p1.getThird().toString() + ")");
			}
			System.out.println(" ");
			System.out.println("-------------------------");
		}
	}
	
	/* function to print one preference set */
	public static void printOnePreferenceSet(Set<Triple<Argument, String, Argument>> prefSet)
	{

			for( Triple<Argument, String, Argument> p1: prefSet)
			{
				System.out.print("(" + p1.getFirst().toString() + " " + p1.getSecond().toString() + " " + p1.getThird().toString() + ")");
			}
			System.out.println(" ");
			System.out.println("-------------------------");

	}
	
	public static boolean isTripleEqual(Triple<Argument, String, Argument> pref1, Triple<Argument, String, Argument> pref2)
	{
		if(pref1.getFirst().toString().equals(pref2.getFirst().toString()) && pref1.getSecond().toString().equals(pref2.getSecond().toString())
				&& pref1.getThird().toString().equals(pref2.getThird().toString()))
			return true;
		else if(pref1.getFirst().toString().equals(pref2.getThird().toString()) 
				&& pref1.getThird().toString().equals(pref2.getFirst().toString())
				&& pref1.getSecond().toString().equals("=")
				&& pref2.getSecond().toString().equals("=")
				)
			return true;		
		else if(pref1.getFirst().toString().equals(pref2.getThird().toString()) 
				&& pref1.getThird().toString().equals(pref2.getFirst().toString())
				&& pref1.getSecond().toString().equals(">")
				&& pref2.getSecond().toString().equals("<")				
				)
			return true;
		else if(pref1.getFirst().toString().equals(pref2.getThird().toString()) 
					&& pref1.getThird().toString().equals(pref2.getFirst().toString())
					&& pref1.getSecond().toString().equals("<")
					&& pref2.getSecond().toString().equals(">")				
					)			
			return true;
		else
			return false;
	}
	
	// function to compute set of unique preferences, where inputs are two set of sets of preferences for two different extensions
	
	public static Set<Triple<Argument, String, Argument>> computeUniquePrefs(Set<Set<Triple<Argument, String, Argument>>> prefSet1, Set<Set<Triple<Argument, String, Argument>>> prefSet2)
	{
		boolean check = false;
		Set<Triple<Argument, String, Argument>> uniquePrefSet = new HashSet<Triple<Argument, String, Argument>> ();
		for( Set<Triple<Argument, String, Argument>> pSet1: prefSet1)
		{
			for( Triple<Argument, String, Argument> p1: pSet1)
			{
				check = false;
				for( Set<Triple<Argument, String, Argument>> pSet2: prefSet2)
				{
					for( Triple<Argument, String, Argument> p2: pSet2)
					{
						if(isTripleEqual(p1, p2)==true)
						{
							check = true;
							break;
						}
					}
				}
				if(check == false)
					uniquePrefSet.add(p1);
			}
		}
		return uniquePrefSet;
		
	}
	
	
	// function to compute set of common preferences, where inputs are two set of sets of preferences for two different extensions

	public static Set<Triple<Argument, String, Argument>> computeCommonPrefs(Set<Set<Triple<Argument, String, Argument>>> prefSet1, Set<Set<Triple<Argument, String, Argument>>> prefSet2)
	{
		Set<Triple<Argument, String, Argument>> commonPrefSet = new HashSet<Triple<Argument, String, Argument>> ();
		for( Set<Triple<Argument, String, Argument>> pSet1: prefSet1)
		{
			for( Triple<Argument, String, Argument> p1: pSet1)
			{
				
				for( Set<Triple<Argument, String, Argument>> pSet2: prefSet2)
				{
					for( Triple<Argument, String, Argument> p2: pSet2)
					{
						if(isTripleEqual(p1, p2)==true)
						{
							commonPrefSet.add(p1);
						}
					}
				}
					
			}
		}
		return commonPrefSet;
		
	}
	

	public static Set<Set<Argument>> collectionToSet(Collection<Extension> extension_sets)
	{
		Iterator<Extension> ei = extension_sets.iterator();
		Set<Set<Argument>> ext_sets = new HashSet<Set<Argument>>();
		while (ei.hasNext()) {
			Object[] extension_array = ei.next().toArray();
			Set<Object> ext_set = new HashSet<Object>(Arrays.asList(extension_array));
			Set<Argument> ext_set_argument = new HashSet<Argument>();
			    for (Object o : ext_set) {
			        ext_set_argument.add((Argument) o);
			    }
			 ext_sets.add(ext_set_argument);
	        }
		return ext_sets;
	}
	
	
	//function to apply preferences using the method of attack removal

	public static Pair<DungTheory, Set<Attack>> applyPreferenceSetRemoveAttack(DungTheory at_example, Set<Triple<Argument, String, Argument>> PrefSet)
	{
		Set<Attack> attacks = new HashSet<Attack>();
		for(Triple<Argument, String, Argument> Pref1: PrefSet)
		{
			Argument firstArgument = Pref1.getFirst();
			Argument secondArgument = Pref1.getThird();
			Attack attack1 = new Attack(secondArgument, firstArgument);
			if((Pref1.getSecond() == ">") && (at_example.containsAttack(attack1)))
			{
				at_example.remove(attack1);
				attacks.add(attack1);
			}
		}
		Pair<DungTheory, Set<Attack>> pair_da = new Pair<DungTheory, Set<Attack>>(at_example,attacks);
		return pair_da;
	}
	
	
	//function to apply preferences using the method of attack reversal

	public static Triple<DungTheory, Set<Attack>, Set<Attack>> applyPreferenceSetReverseAttack(DungTheory at_example, Set<Triple<Argument, String, Argument>> PrefSet)
	{
		Set<Attack> attacksAdd = new HashSet<Attack>();
		Set<Attack> attacksRemove = new HashSet<Attack>();
		for(Triple<Argument, String, Argument> Pref1: PrefSet)
		{
			Argument firstArgument = Pref1.getFirst();
			Argument secondArgument = Pref1.getThird();
			Attack attack1 = new Attack(secondArgument, firstArgument);
			Attack attack2 = new Attack(firstArgument, secondArgument);
			if((Pref1.getSecond() == ">") && (at_example.containsAttack(attack1)))
			{
				at_example.remove(attack1);
				attacksAdd.add(attack1);
				if(at_example.containsAttack(attack2)==false)
				{
					at_example.add(attack2);
					attacksRemove.add(attack2);
				}
			}
		}

		Triple<DungTheory, Set<Attack>, Set<Attack>> triple_da = new Triple<DungTheory, Set<Attack>, Set<Attack>>(at_example,attacksAdd, attacksRemove);
		return triple_da;
	}
	
	
	//function for verifying Approximate preferences using attack removal method
	
	public static boolean verifyApproximatePreferences1(DungTheory at, Set<Triple<Argument, String, Argument>> prefs, Set<Argument> ext)
	{
		
		boolean vcheck = false;
		
		Pair<DungTheory, Set<Attack>> pair_da = null;
		//for (Set<Triple<Argument, String, Argument>> Prefs: PrefSet)
		//{
		
		pair_da = applyPreferenceSetRemoveAttack(at, prefs);
		System.out.println(pair_da.getFirst());
		
		//AbstractExtensionReasoner preasoner2 = AbstractExtensionReasoner.getSimpleReasonerForSemantics(Semantics.PREFERRED_SEMANTICS);
		AbstractExtensionReasoner preasoner2 = AbstractExtensionReasoner.getSimpleReasonerForSemantics(Semantics.GROUNDED_SEMANTICS);
		//AbstractExtensionReasoner preasoner2 = AbstractExtensionReasoner.getSimpleReasonerForSemantics(Semantics.STABLE_SEMANTICS);
		Collection<Extension> extension_sets2 = new HashSet<Extension>();
		extension_sets2 = preasoner2.getModels(pair_da.getFirst());	
		
		Set<Set<Argument>> ext_sets = new HashSet<Set<Argument>>();
		ext_sets = collectionToSet(extension_sets2);
		Iterator<Set<Argument>> ext_iterator = ext_sets.iterator();
		
		 Set<Argument> ext_set_argument = new HashSet<Argument>();
		 ext_set_argument = ext_iterator.next();
		 
		 if(ext.equals(ext_set_argument) && (ext_sets.size()==1))
		 {
			System.out.println("Preferences are correct");
			vcheck = true;
		 }
		 else
			System.out.println("Preferences are incorrect");
		 
		 
			at.addAllAttacks(pair_da.getSecond());
		//}
		
		return vcheck;

	}	
	
	//function for verifying Approximate preferences using attack reversal method
	
	public static boolean verifyApproximatePreferences2(DungTheory at2, Set<Triple<Argument, String, Argument>> prefs, Set<Argument> ext)
	{
		DungTheory at = at2;
		boolean vcheck = false;
		
		Triple<DungTheory, Set<Attack>, Set<Attack>> triple_da = null;
		//for (Set<Triple<Argument, String, Argument>> Prefs: PrefSet)
		//{
		triple_da = applyPreferenceSetReverseAttack(at, prefs);
		System.out.println(at);
		
		//AbstractExtensionReasoner preasoner2 = AbstractExtensionReasoner.getSimpleReasonerForSemantics(Semantics.PREFERRED_SEMANTICS);
		AbstractExtensionReasoner preasoner2 = AbstractExtensionReasoner.getSimpleReasonerForSemantics(Semantics.GROUNDED_SEMANTICS);
		//AbstractExtensionReasoner preasoner2 = AbstractExtensionReasoner.getSimpleReasonerForSemantics(Semantics.STABLE_SEMANTICS);
		System.out.println("Preferred Extensions:" + preasoner2.getModels(triple_da.getFirst()));
		Collection<Extension> extension_sets2 = new HashSet<Extension>();
		extension_sets2 = preasoner2.getModels(triple_da.getFirst());	
				
		System.out.println("All Preffered Extensions: " + extension_sets2);
		System.out.println("Input Extension: " + ext);
		
		Set<Set<Argument>> ext_sets = new HashSet<Set<Argument>>();
		ext_sets = collectionToSet(extension_sets2);
		Iterator<Set<Argument>> ext_iterator = ext_sets.iterator();
		
		 Set<Argument> ext_set_argument = new HashSet<Argument>();
		 ext_set_argument = ext_iterator.next();
		 
		 if(ext.equals(ext_set_argument) && (ext_sets.size()==1))
		 {
			System.out.println("Preferences are correct");
			vcheck = true;
		 }
		 else
			System.out.println("Preferences are incorrect");
		
			
		 at.addAllAttacks(triple_da.getSecond());
		 for(Attack attackRemove: triple_da.getThird())
		 {
			at.remove(attackRemove);
		 }
		//}

		return vcheck;
	}	
	
	
	
	//function for verifying preferences using attack removal method
	
	public static int[] verifyPreferences1(DungTheory at, Set<Set<Triple<Argument, String, Argument>>> PrefSet, Set<Argument> ext)
	{
		
		int count1 = 0;
		int count2 = 0;
		int count3 = 0;
		int count4 = 0;
		
		Pair<DungTheory, Set<Attack>> pair_da = null;
		for (Set<Triple<Argument, String, Argument>> Prefs: PrefSet)
		{
		
		pair_da = applyPreferenceSetRemoveAttack(at, Prefs);
		System.out.println(pair_da.getFirst());
		
		//AbstractExtensionReasoner preasoner2 = AbstractExtensionReasoner.getSimpleReasonerForSemantics(Semantics.PREFERRED_SEMANTICS);
		AbstractExtensionReasoner preasoner2 = AbstractExtensionReasoner.getSimpleReasonerForSemantics(Semantics.GROUNDED_SEMANTICS);
		//AbstractExtensionReasoner preasoner2 = AbstractExtensionReasoner.getSimpleReasonerForSemantics(Semantics.STABLE_SEMANTICS);
		Collection<Extension> extension_sets2 = new HashSet<Extension>();
		extension_sets2 = preasoner2.getModels(pair_da.getFirst());	
		
		Set<Set<Argument>> ext_sets = new HashSet<Set<Argument>>();
		ext_sets = collectionToSet(extension_sets2);
		Iterator<Set<Argument>> ext_iterator = ext_sets.iterator();
		
		 Set<Argument> ext_set_argument = new HashSet<Argument>();
		 ext_set_argument = ext_iterator.next();
		 
		 if(ext.equals(ext_set_argument) && (ext_sets.size()==1))
		 {
			System.out.println("Preferences are correct");
			count1++;
		 }
		 else if(ext_set_argument.containsAll(ext) && (ext_sets.size()==1))
		 {
			System.out.println("Preferences are correct");
			count2++;
		 }
		 else if(ext_sets.contains(ext) && (ext_sets.size()!=1))
		 {
			System.out.println("Preferences are correct");
			count3++;
		 }
		 else if(ext_sets.size()!=1)
		 {
			boolean c = false;
			for(Set<Argument> ext_set: ext_sets)
			{
				if(ext_set.containsAll(ext)) {
					c = true;
					break;
				}
			}
			if(c==true)
			{
				System.out.println("Preferences are correct");
				count4++;
			}
		 }
		 else
			System.out.println("Preferences are incorrect");
		 
		 
			at.addAllAttacks(pair_da.getSecond());
		}
		

		
		int[] countArray = {count1, count2, count3, count4};
		return countArray;

	}
	
	
	//function for verifying preferences using attack reversal method
	
	public static int[] verifyPreferences2(DungTheory at2, Set<Set<Triple<Argument, String, Argument>>> PrefSet, Set<Argument> ext)
	{
		DungTheory at = at2;
		int count1 = 0;
		int count2 = 0;
		int count3 = 0;
		int count4 = 0;
		Triple<DungTheory, Set<Attack>, Set<Attack>> triple_da = null;
		for (Set<Triple<Argument, String, Argument>> Prefs: PrefSet)
		{
		triple_da = applyPreferenceSetReverseAttack(at, Prefs);
		System.out.println(at);
		
		//AbstractExtensionReasoner preasoner2 = AbstractExtensionReasoner.getSimpleReasonerForSemantics(Semantics.PREFERRED_SEMANTICS);
		AbstractExtensionReasoner preasoner2 = AbstractExtensionReasoner.getSimpleReasonerForSemantics(Semantics.GROUNDED_SEMANTICS);
		//AbstractExtensionReasoner preasoner2 = AbstractExtensionReasoner.getSimpleReasonerForSemantics(Semantics.STABLE_SEMANTICS);
		System.out.println("Preferred Extensions:" + preasoner2.getModels(triple_da.getFirst()));
		Collection<Extension> extension_sets2 = new HashSet<Extension>();
		extension_sets2 = preasoner2.getModels(triple_da.getFirst());	
				
		System.out.println("All Preffered Extensions: " + extension_sets2);
		System.out.println("Input Extension: " + ext);
		
		Set<Set<Argument>> ext_sets = new HashSet<Set<Argument>>();
		ext_sets = collectionToSet(extension_sets2);
		Iterator<Set<Argument>> ext_iterator = ext_sets.iterator();
		
		 Set<Argument> ext_set_argument = new HashSet<Argument>();
		 ext_set_argument = ext_iterator.next();
		 
		 if(ext.equals(ext_set_argument) && (ext_sets.size()==1))
		 {
			System.out.println("Preferences are correct");
			count1++;
		 }
		 else if(ext_set_argument.containsAll(ext) && (ext_sets.size()==1))
		 {
			System.out.println("Preferences are correct");
			count2++;
		 }
		 else if(ext_sets.contains(ext) && (ext_sets.size()!=1))
		 {
			System.out.println("Preferences are correct");
			count3++;
		 }
		 else if(ext_sets.size()!=1)
		 {
			boolean c = false;
			for(Set<Argument> ext_set: ext_sets)
			{
				if(ext_set.containsAll(ext)) {
					c = true;
					break;
				}
			}
			if(c==true)
			{
				System.out.println("Preferences are correct");
				count4++;
			}
		 }
		 else
			System.out.println("Preferences are incorrect");
		
			
		 at.addAllAttacks(triple_da.getSecond());
		 for(Attack attackRemove: triple_da.getThird())
		 {
			at.remove(attackRemove);
		}
		}
		
		
		int[] countArray = {count1, count2, count3, count4};
		return countArray;
	}	
	
	
	
			
	public static void main(String[] args) throws IOException {
		

		
		SatSolver mySolver = new Sat4jSolver();
		SatSolver.setDefaultSolver(mySolver);
		
		int size = 20; //set abstract argumentation framework size
		double att_prob = 0.25; //set attack probability
	
		//initialize variables
		double avg_attsno = 0.0;
		double avg_extsize = 0.0;		
		double a_avg_prefs = 0.0;
		double a_avg_prefSets = 0.0;
		double a_avg_computing_time = 0.0;
		double a_avg_verifying_time1 = 0.0;
		double a_avg_verifying_time2 = 0.0;		
		int af_size = 0;
		int pe_size = 0;
		
	
		boolean[] checkArray1 = new boolean[10];
		boolean[] checkArray2 = new boolean[10];		
		List checkList1 = new ArrayList();
		List checkList2 = new ArrayList();
	    List a_checkList1 = new ArrayList();
	    List a_checkList2 = new ArrayList();
		String pathname = "grounded1";
		

		BufferedWriter resultsFileWriter = new BufferedWriter(new FileWriter("/Users/quratul-ainmahesar/results/approximate-scale/" + pathname + "/size" +size+"/results-prefs-" + size + ".txt"));
		for (int i = 0; i < 10; i ++)
		{	
		DungTheoryGenerationParameters params = new DungTheoryGenerationParameters();
		params.numberOfArguments = size;
		params.attackProbability = att_prob;
		params.enforceTreeShape = false;
		DefaultDungTheoryGenerator tgen = new DefaultDungTheoryGenerator(params);
		System.out.println(tgen);
		DungTheory at_example ;
		boolean check = true;

		// choose the semantics 
		//AbstractExtensionReasoner greasoner = AbstractExtensionReasoner.getSimpleReasonerForSemantics(Semantics.PREFERRED_SEMANTICS);  //preferred semantics
		//AbstractExtensionReasoner greasoner = AbstractExtensionReasoner.getSimpleReasonerForSemantics(Semantics.STABLE_SEMANTICS);   //stable semantics
		AbstractExtensionReasoner greasoner = AbstractExtensionReasoner.getSimpleReasonerForSemantics(Semantics.GROUNDED_SEMANTICS);  //grounded semantics
		
		Collection<Extension> extension_set = new HashSet<Extension>();
		do {
			at_example = tgen.next();
			System.out.println(at_example);
		
		System.out.println("Extensions:" + greasoner.getModels(at_example));
		extension_set = new HashSet<Extension>();
		extension_set = greasoner.getModels(at_example);	

		//check for grounded extension uncomment
		
		
		if(extension_set.isEmpty() == true)
			check = false;
		else if(extension_set.iterator().next().size() == 0)
			check = false;
		else
			check = true;
		
		
		} while(check == false);
		
		
		//check for preferred and stable extension uncomment
		
		/*
		if(extension_set.isEmpty() == true)
			check = false;
		else if(extension_set.size() < 2)
			check = false;
		else if(extension_set.iterator().next().size() == 0)
			check = false;
		else
			check = true;
		
		
		} while(check == false);
		*/
		
	
		pe_size = extension_set.size();
		
		Set<Set<Argument>> ext_sets = new HashSet<Set<Argument>>();
		ext_sets = collectionToSet(extension_set);
		Iterator<Set<Argument>> ext_iterator = ext_sets.iterator();
		
		 Set<Argument> ext_set_argument = new HashSet<Argument>();
		 ext_set_argument = ext_iterator.next();
	
		System.out.println("Maximum Extension: " + ext_set_argument);
		
		Set<Set<Triple<Argument, String, Argument>>> prefSets = new HashSet<Set<Triple<Argument, String, Argument>>>();
		
		//Initialize prefs for an approximate preference set
		Set<Triple<Argument, String, Argument>> prefs = new HashSet<Triple<Argument, String, Argument>>();
		
		// code for computing an approximate preference set
		final double a_startTime = System.currentTimeMillis();
		prefs = ComputeApproximatePreferences(at_example, ext_set_argument);
		final double a_endTime = System.currentTimeMillis();
		final double a_computing_time = a_endTime - a_startTime;
		printOnePreferenceSet(prefs);	
		
		
		final double a_vstartTime1 = System.currentTimeMillis();
		boolean vcheck1 = verifyApproximatePreferences1(at_example, prefs, ext_set_argument);
		final double a_vendTime1 = System.currentTimeMillis();
		final double a_verifying_time1 = a_vendTime1 - a_vstartTime1;
		if(vcheck1 == true)
			a_checkList1.add(true);
		else
			a_checkList1.add(false);
		
		final double a_vstartTime2 = System.currentTimeMillis();
		boolean vcheck2 = verifyApproximatePreferences2(at_example, prefs, ext_set_argument);
		final double a_vendTime2 = System.currentTimeMillis();
		final double a_verifying_time2 = a_vendTime2 - a_vstartTime2;
		if(vcheck2 == true)
			a_checkList2.add(true);
		else
			a_checkList2.add(false);		
		
		
		System.out.println("Number of arguments in AAF:" + at_example.getNumberOfNodes());
		System.out.println("Number of attacks in AAF:" + at_example.getAttacks().size());
		System.out.println("Preferred extension size:"+ ext_set_argument.size());
		
		resultsFileWriter.write("Number of arguments in AAF:" + at_example.getNumberOfNodes());
		resultsFileWriter.newLine();
		resultsFileWriter.write("Preferred extension size:"+ ext_set_argument.size());
		resultsFileWriter.newLine();
		resultsFileWriter.write("Attack Probability:" + att_prob);
		resultsFileWriter.newLine();
		resultsFileWriter.write("Number of attacks in AAF:" + at_example.getAttacks().size());
		resultsFileWriter.flush();
		
		
		// code for average computations of 10 instances 
		
		avg_attsno = avg_attsno + at_example.getAttacks().size();
		avg_extsize = avg_extsize + ext_set_argument.size();

		
		a_avg_prefs = a_avg_prefs + prefs.size();
		a_avg_prefSets = 1.0;
		a_avg_computing_time = a_avg_computing_time + a_computing_time;
		a_avg_verifying_time1 = a_avg_verifying_time1 + a_verifying_time1;
		a_avg_verifying_time2 = a_avg_verifying_time2 + a_verifying_time2;		
		
		
		
		
		}
		
		
		BufferedWriter avgresultsFileWriter = new BufferedWriter(new FileWriter("/Users/quratul-ainmahesar/results/approximate-scale/" + pathname + "/size"+size+"/average-results-prefs-" + size + ".txt"));
		
		avg_attsno = Math.round(avg_attsno/10);
		avg_extsize = Math.round(avg_extsize/10);		
		
		a_avg_prefs = Math.round(a_avg_prefs/10);
		a_avg_computing_time = Math.round(a_avg_computing_time/10);
		a_avg_verifying_time1 = Math.round(a_avg_verifying_time1/10);		
		a_avg_verifying_time2 = Math.round(a_avg_verifying_time2/10);	
		

		String a_checkString1 = "All correct";
		String a_checkString2 = "All correct";
		
			
		if(a_checkList1.contains(false))
			a_checkString1 = "Not correct";
		
		if(a_checkList2.contains(false))
			a_checkString2 = "Not correct";		
		
		avgresultsFileWriter.write("Number of arguments in AAF:" + size);
		avgresultsFileWriter.newLine();
		avgresultsFileWriter.write("Preferred extension size:" + avg_extsize);
		avgresultsFileWriter.newLine();		
		avgresultsFileWriter.write("Attack Probability:" + att_prob);
		avgresultsFileWriter.newLine();
		avgresultsFileWriter.write("Number of attacks in AAF:" + avg_attsno);				
		avgresultsFileWriter.newLine();				
		avgresultsFileWriter.write("--------------------------------------------------------");
		avgresultsFileWriter.newLine();
		
		avgresultsFileWriter.flush();
		avgresultsFileWriter.close();
		
		// code for writing to excel file
		
		FileWriter csvWriter = null;
		if(size==5)	
		{
			csvWriter = new FileWriter("/Users/quratul-ainmahesar/results/approximate-scale/" + pathname +"/results.csv");
			csvWriter.append("AAF_Size");			// abstract argumentation framework size
			csvWriter.append(",");
			csvWriter.append("Avg_Ext_Size");       // average extension size
			csvWriter.append(",");
			csvWriter.append("Att_Prob");           // attack probability
			csvWriter.append(",");
			csvWriter.append("Avg_Att_No");	        // average number of attacks
			csvWriter.append(",");
			csvWriter.append("A_Avg_PrefSets_No");	// approximate average number of preference sets
			csvWriter.append(",");
			csvWriter.append("A_Avg_Prefs_No");	    // approximate average number of preferences
			csvWriter.append(",");
			csvWriter.append("A_C_AvgTime_ms");		// approximate average time for computing preferences	
			csvWriter.append(",");
			csvWriter.append("A_V1_AvgTime_ms");		// approximate average time for verifying preferences (attack removal)
			csvWriter.append(",");
			csvWriter.append("A_V2_AvgTime_ms");		// approximate average time for verifying preferences (attack reversal)
			csvWriter.append(",");
			csvWriter.append("A_V1_check");		// approximate check all preferences verified correctly (attack removal)	
			csvWriter.append(",");
			csvWriter.append("A_V2_check");		// approximate check all preferences verified correctly (attack reversal)	
			csvWriter.append("\n");			
		}
		else
			csvWriter = new FileWriter("/Users/quratul-ainmahesar/results/approximate-scale/" + pathname +"/results.csv", true);
		
		csvWriter.append(String.valueOf(size));			
		csvWriter.append(",");	
		csvWriter.append(String.valueOf(avg_extsize));	
		csvWriter.append(",");		
		csvWriter.append(String.valueOf(att_prob));	
		csvWriter.append(",");	
		csvWriter.append(String.valueOf(avg_attsno));	
		csvWriter.append(",");	
		csvWriter.append(String.valueOf(a_avg_prefSets));	
		csvWriter.append(",");	
		csvWriter.append(String.valueOf(a_avg_prefs));	
		csvWriter.append(",");			
		csvWriter.append(String.valueOf(a_avg_computing_time));	
		csvWriter.append(",");		
		csvWriter.append(String.valueOf(a_avg_verifying_time1));		
		csvWriter.append(",");			
		csvWriter.append(String.valueOf(a_avg_verifying_time2));		
		csvWriter.append(",");		
		csvWriter.append(String.valueOf(a_checkString1));		
		csvWriter.append(",");	
		csvWriter.append(String.valueOf(a_checkString2));		
		csvWriter.append(",");	
	    csvWriter.append("\n");
		csvWriter.flush();
		csvWriter.close();

	    
		
		}

}
