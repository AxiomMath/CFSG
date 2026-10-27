module

public import CFSG.LocalAnalysis.ComponentInitial.SmallLinearIsomorphisms
public import CFSG.LocalAnalysis.ComponentInitial.FieldNineAlternatingSix

public section

namespace CFSG.LocalAnalysis.ComponentInitial

open CFSG.Assembly.LowTwoRank CFSG.ClassicalModels Matrix

theorem statedClassicalModel_psl_two_five_of_alternating_five (X : Type) [Group X]
    (h : Nonempty (X ≃* alternatingGroup (Fin 5))) : StatedClassicalModel X .PSL 2 5 1 := by
  obtain ⟨e⟩ := h
  have : Fact (Nat.Prime 5) := ⟨Nat.prime_five⟩
  obtain ⟨e5⟩ := nonempty_statedLinearModel_equiv_alternating_five (ZMod 5)
    (Or.inr (Nat.card_zmod 5))
  exact ⟨⟨Nat.prime_five, le_rfl, le_rfl, by decide, by decide⟩, ZMod 5, inferInstance,
    inferInstance, by rw [Nat.card_zmod, pow_one], ⟨e.trans e5.symm⟩⟩

theorem statedClassicalModel_psl_two_nine_of_alternating_six (X : Type) [Group X]
    (h : Nonempty (X ≃* alternatingGroup (Fin 6))) : StatedClassicalModel X .PSL 2 3 2 := by
  obtain ⟨e⟩ := h
  have : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  have hcard : Nat.card (GaloisField 3 2) = 3 ^ 2 := GaloisField.card 3 2 (by norm_num)
  let : Fintype (GaloisField 3 2) := Fintype.ofFinite _
  have hK : Fintype.card (GaloisField 3 2) = 9 := by
    rw [← Nat.card_eq_fintype_card, hcard]
    norm_num
  obtain ⟨e6⟩ := unique_field_nine_projective_linear_alternating_six_isomorphism
    (GaloisField 3 2) hK
  exact ⟨⟨Nat.prime_three, by norm_num, le_rfl, by decide, by decide⟩, GaloisField 3 2,
    inferInstance, inferInstance, hcard,
    ⟨(e.trans e6.symm).trans (projectiveSpecialLinearGroupEquivStatedProj 2 _)⟩⟩

theorem small_models_odd_linear_two_aliases (L : Type) [Group L]
    (h : Nonempty (L ≃* alternatingGroup (Fin 5)) ∨ Nonempty (L ≃* alternatingGroup (Fin 6)) ∨
      StatedClassicalModel L .PSL 2 2 2 ∨ StatedClassicalModel L .PSL 3 2 1) :
    ∃ ℓ e : ℕ, ℓ.Prime ∧ Odd ℓ ∧ 1 ≤ e ∧ StatedClassicalModel L .PSL 2 ℓ e := by
  have hmem : (StatedLieTag.PSL) ∈ CFSG.Blueprint.classicalTags := by decide
  rcases h with h | h | h | h
  · exact ⟨5, 1, Nat.prime_five, by decide, le_rfl,
      statedClassicalModel_psl_two_five_of_alternating_five L h⟩
  · exact ⟨3, 2, Nat.prime_three, by decide, by norm_num,
      statedClassicalModel_psl_two_nine_of_alternating_six L h⟩
  · exact ⟨5, 1, Nat.prime_five, by decide, le_rfl,
      statedClassicalModel_psl_two_five_of_alternating_five L
        (PSL2_four_alternating_five_model L (Or.inl ⟨hmem, h⟩))⟩
  · rcases PSL3_two_PSL2_seven_paired_isomorphism L (Or.inl ⟨hmem, h⟩) with
      ⟨-, hc⟩ | ⟨-, ht, -⟩ | ⟨-, ht, -⟩ | ⟨-, ht, -⟩
    · exact ⟨7, 1, Nat.prime_seven, by decide, le_rfl, hc⟩
    all_goals exact absurd ht (by decide)

end CFSG.LocalAnalysis.ComponentInitial
