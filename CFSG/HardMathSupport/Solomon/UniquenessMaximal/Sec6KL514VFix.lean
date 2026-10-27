module

public import CFSG.HardMathSupport.Solomon.UniquenessMaximal.Sec6KFixMain
public import CFSG.HardMathSupport.Solomon.Coordinator.InndiagProxy

public section

namespace CFSG.HardMathSupport.Solomon.UniquenessMaximal

open CFSG.RankThree.PartTwo.KFacts CFSG.LocalAnalysis.ComponentInitial.LinearFlag
  CFSG.ClassicalGroups.UnitaryFlag CFSG.HardMathSupport.Solomon.Coordinator
  CFSG.HardMathSupport.Solomon.LocalBalance
  CFSG.HardMathSupport.Solomon.LocalBalance.Lemma514CoverNs

@[deprecated (since := "2026-10-15")]
alias l514V_map_mem_commutator := map_mem_commutator_mulAut

@[deprecated "use `innerAut_le_commutator_of_perfect`" (since := "2026-10-15")]
theorem l514V_innerAut_le_commutator (Y : Type) [Group Y] [Group.IsPerfect Y] :
    LocalBalance.innerAut Y ≤ commutator (MulAut Y) :=
  innerAut_le_commutator_of_perfect Group.IsPerfect.commutator_eq_top

@[deprecated "use `innAutDerivedVocab_le_commutator`" (since := "2026-10-15")]
theorem l514V_innDiag_le_commutator (Y : Type) [Group Y] [Finite Y]
    (hY : CFSG.Open.IsQuasisimple Y) : innAutDerivedVocab.innDiag Y ≤ commutator (MulAut Y) :=
  innAutDerivedVocab_le_commutator hY

theorem eq_one_of_mem_commutator_of_field {Y : Type} [Group Y] [Finite Y]
    (hY : CFSG.Open.IsQuasisimple Y) {α : MulAut Y} (hc : α ∈ commutator (MulAut Y))
    (hf : IsFieldAutThree α) : α = 1 := by
  rcases hf with h | hL | hU
  · exact h
  · obtain ⟨F, _, _, e, σ, γ, he⟩ := fieldAutPSL3_data hL
    refine eq_one_of_inndiag_model hY (goodPinned_psl F) e ?_ (Or.inr (Or.inl hL))
    exact (goodPinned_psl F).down
      (map_mem_commutator_mulAut ((MulAut.congr e).toMonoidHom.comp (centerDescend Y)) hc)
  · obtain ⟨p, f, F, _, hF, e, σ, γ, -, he⟩ := fieldAutPSU3_data hU
    have hq := two_lt_pow_of_quasisimple hY hF e
    refine eq_one_of_inndiag_model hY (goodPinned_psu hF hq) e ?_ (Or.inr (Or.inr hU))
    exact (goodPinned_psu hF hq).down
      (map_mem_commutator_mulAut ((MulAut.congr e).toMonoidHom.comp (centerDescend Y)) hc)

theorem inndiagFieldTrivial_l514V : InndiagFieldTrivial innAutDerivedVocab :=
  fun _ _ _ hY _ hf hmem =>
    eq_one_of_mem_commutator_of_field hY (innAutDerivedVocab_le_commutator hY hmem) hf

theorem inputL3fix_l514V : InputL3fix innAutDerivedVocab :=
  inputL3fix_of_inndiagFieldTrivial inndiagFieldTrivial_l514V

end CFSG.HardMathSupport.Solomon.UniquenessMaximal
