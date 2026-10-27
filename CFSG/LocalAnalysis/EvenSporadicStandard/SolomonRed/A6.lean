module

public import CFSG.LocalAnalysis.EvenSporadicStandard.SolomonRed.GenA
public import CFSG.LocalAnalysis.EvenSporadicStandard.Fin76b.Inputs
public import CFSG.LocalAnalysis.QuasithinUnique.Unconstrained.L2_5_8A6
public import CFSG.LocalAnalysis.QuasithinUnique.Constrained.DoubleA3.A6Aut

public section

namespace CFSG.EvenSporadicStandard.SolomonRed

open Subgroup

theorem outSq_psl29 : OutSq ↥CFSG.QuasithinUnique.A6Models.psl29 := by
  intro α
  obtain ⟨g, hg⟩ := CFSG.QuasithinUnique.Unc25A6.sq_inner α
  refine ⟨g, fun x => ?_⟩
  have h1 := congrArg (fun φ : MulAut ↥CFSG.QuasithinUnique.A6Models.psl29 => φ x) hg
  simpa [pow_two, MulAut.conj_apply] using h1.symm

theorem outSq_alternatingGroup_six : OutSq (alternatingGroup (Fin 6)) := by
  obtain ⟨ψ, -⟩ := CFSG.QuasithinUnique.DoubleA3.exists_psl_equiv
  exact OutSq.of_mulEquiv ψ outSq_psl29

theorem solomonZ2A6_of_cat (h : CatNoAlmostSimpleZ2 (alternatingGroup (Fin 6))) :
    Fin76b.SolomonZ2A6 := by
  have : IsSimpleGroup (alternatingGroup (Fin 6)) := alternatingGroup.isSimpleGroup (by simp)
  have hc : Subgroup.center (alternatingGroup (Fin 6)) = ⊥ :=
    alternatingGroup.center_eq_bot (by simp)
  exact solomonGen_of_cat (exists_noncommute_of_center_eq_bot hc) outSq_alternatingGroup_six h

end CFSG.EvenSporadicStandard.SolomonRed
