module

public import CFSG.HardMathSupport.Curtis.NaturalModuleCensus.CentCyc.Cells
public import CFSG.HardMathSupport.Curtis.NaturalModuleCensus.CentCyc.TwistedAOut
public import CFSG.HardMathSupport.Curtis.NaturalModuleCensus.CentCyc.TwistedATorus

public section

namespace CFSG.HardMathSupport.Curtis.NaturalModuleCensus.CentCyc

open CFSG.Open CFSG.QuasithinUnique CFSG.AGLEmbedding CFSG.Assembly.LowTwoRank
  CFSG.RankThree.PartOne.OutStructure
open CFSG.HardMathSupport.Curtis.NaturalModuleCensus

theorem centCycCell_twistedA : CentCycCell (IsLieOf IdxTwistedA) := by
  intro Y _ _ L J hCP hX p hp hp5 D hDp hDJ hDcyc hDpart x hxD hxp hxC hxW E hEN hEp
  have : Group.IsPerfect ↥L := Group.isPerfect_def.mpr hCP.comp.2.2.1
  obtain ⟨ρ, hρker, hρJ, v, hv⟩ := exists_centCycBar hCP hp hDp hDJ hDcyc hDpart hxD hxp hxC hxW
  rcases isLieOf_split (p := p) hX with hTF | hT
  · refine ⟨exists_cyclic_mod_of_outPChain (outPChain_twistedA hp hp5 hTF) hEp hEN,
      fun hEJ _ => ?_⟩
    refine exists_cover_mod_centralizer ρ hρker hEJ ?_
    refine isCyclic_of_centCycBar_hub hv
      (perfectJoinHub_of_torusFree_classical (Or.inr (Or.inl rfl)) hp hp5 hTF) ?_
      ((hEp.comap_subtype (K := J ⊔ Subgroup.centralizer (L : Set Y))).map ρ)
    rintro _ ⟨g, -, rfl⟩
    exact hρJ g
  · exact (false_of_centCycBar_torus_twistedA hp hp5 hT hv).elim

end CFSG.HardMathSupport.Curtis.NaturalModuleCensus.CentCyc
