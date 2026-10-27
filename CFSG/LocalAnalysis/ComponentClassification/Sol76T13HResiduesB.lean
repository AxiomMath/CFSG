module

public import CFSG.LocalAnalysis.ComponentClassification.Sol76T13NarrowResidues
public import CFSG.LocalAnalysis.ComponentClassification.Sol76T13HNPrime

public section

namespace CFSG.ComponentClassification.Sol76T13

open CFSG Subgroup CFSG.ComponentClassification.FooteLit CFSG.ComponentClassification.Sol76

theorem lemma313NarrowInputFor_simple_of_schreier
    (hS : CFSG.LocalAnalysis.ComponentInitial.SchreierFor Blueprint.Catalog) :
    Lemma313NarrowInputFor simpleAmbient :=
  lemma313NarrowInputFor_of_schreier hS Hq4.quasisimpleTwoPartInput_holds
    fun _ _ _ hG => kStarKProper_of_simpleAmbient hG

theorem solomonThm13Simple_of_schreier
    (hS : CFSG.LocalAnalysis.ComponentInitial.SchreierFor Blueprint.Catalog)
    (hb : Lemma315bInputFor simpleAmbient) : SolomonThm13Simple :=
  solomonThm13Simple_of_narrow (lemma313NarrowInputFor_simple_of_schreier hS) hb

end CFSG.ComponentClassification.Sol76T13
