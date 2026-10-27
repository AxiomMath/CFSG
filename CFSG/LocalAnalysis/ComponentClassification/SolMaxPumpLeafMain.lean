module

public import CFSG.LocalAnalysis.ComponentClassification.SolMaxPumpLeaf
public import CFSG.LocalAnalysis.ComponentClassification.SolMaxPumpReduce

public section

namespace CFSG.ComponentClassification.SolMax

open CFSG Subgroup CFSG.Blueprint CFSG.Assembly.LowTwoRank
  CFSG.ComponentClassification.CatLeaf

theorem altPumpOutcome_of_alternating {S : Type} [Group S] [Finite S] {n : ℕ} (hn : 5 ≤ n)
    (θ : S ≃* alternatingGroup (Fin n)) {σ : MulAut S} {P : Subgroup S}
    (h : ProperFixedComponent σ P) {m : ℕ} (hm : Odd m) (hm7 : 7 ≤ m)
    (eP : P ⧸ Open.fusionZStar P ≃* alternatingGroup (Fin m)) : AltPumpOutcome S m := by
  obtain ⟨hmn, hpar⟩ := alt_outcome_of_alternating hn θ h hm7 eP
  refine Or.inl ⟨n, ?_, hmn, ⟨θ⟩⟩
  rw [Nat.odd_iff] at hm ⊢
  omega

theorem altPumpLeaf_of_clauses
    (hGLS : GLS3OddLieAutComponentsInput) (hO : LieOrderFormulasInput)
    (hEO : EvenLieOuterTwoComponentsInput) (hspor : AltPumpSporadicClause) : AltPumpLeaf := by
  intro S _ _ hs hna hcat σ P h hPex m hm hm7 ⟨eP⟩
  have : IsSimpleGroup S := hs
  have hodd : OddLieType S → False := fun ho => false_of_oddLie_alt hGLS hO hna ho h hm hm7 eP
  have hheld : Nonempty (S ≃* NativeSporadic.He) → AltPumpOutcome S m := fun ⟨eH⟩ =>
    Or.inr ⟨eq_seven_of_held hna eH h hm hm7 eP, ⟨eH⟩⟩
  rcases (Milestones.ct_catalog_nonabelian_type_partition S hna).mp hcat with
    ⟨n, hn, ⟨θ⟩⟩ | ho | he | ⟨s, ⟨e⟩⟩
  · exact altPumpOutcome_of_alternating hn θ h hm hm7 eP
  · exact (hodd ho).elim
  · rcases uList_of_evenLie_alt hEO hGLS hO hna he h hm hm7 eP with ho | ⟨n, -, hn7, ⟨θ⟩⟩ | hH
    · exact (hodd ho).elim
    · exact altPumpOutcome_of_alternating (by omega) θ h hm hm7 eP
    · exact hheld hH
  · by_cases hHe : s = .He
    · subst hHe
      exact hheld ⟨e⟩
    · exact (hspor S hna s hHe ⟨e⟩ σ P h hPex m hm hm7 ⟨eP⟩).elim

end CFSG.ComponentClassification.SolMax
