module

public import CFSG.LocalAnalysis.RankThreeUC.AGL81S15RowStmts
import CFSG.RankThree.PartOne.N143.Inspect613Even
import CFSG.LargeExtraspecial.DW2AOut

public section

namespace CFSG.LocalAnalysis.RankThreeUC.S15

@[expose] def KOutLin : Prop :=
  ∀ (S : Type) [Group S] [Finite S], (IsLinTwo 6 S ∨ IsLinTwo 7 S) → ∀ φ : MulAut S,
    ∃ k : ℕ, φ ^ (2 ^ k) ∈ (MulAut.conj : S →* MulAut S).range

theorem KOutLin_aux_card_two {Q : TauCeti.PrimePower} (h : Q.card = 2) :
    Q.p = 2 ∧ Q.exponent = 1 := by
  rw [TauCeti.PrimePower.card_def] at h
  exact (Nat.Prime.pow_eq_iff Nat.prime_two).mp h

theorem KOutLin_aux_of_isPGroup {S : Type} [Group S]
    (h : IsPGroup 2 (CFSG.ComponentClassification.OuterAutomorphisms.Outer S)) (φ : MulAut S) :
    ∃ k : ℕ, φ ^ (2 ^ k) ∈ (MulAut.conj : S →* MulAut S).range := by
  obtain ⟨k, hk⟩ := h (QuotientGroup.mk φ)
  refine ⟨k, ?_⟩
  have h1 : (QuotientGroup.mk (φ ^ 2 ^ k) :
      CFSG.ComponentClassification.OuterAutomorphisms.Outer S) = 1 := by
    rw [QuotientGroup.mk_pow]
    exact hk
  exact (QuotientGroup.eq_one_iff
    (N := CFSG.ComponentClassification.OuterAutomorphisms.inner S) _).1 h1

theorem KOutLin_holds : KOutLin := by
  intro S _ _ hS φ
  refine KOutLin_aux_of_isPGroup ?_ φ
  rcases hS with ⟨Q, hQ2, hQc, d, hd, ⟨e⟩⟩ | ⟨Q, hQ2, hQc, d, hd, ⟨e⟩⟩
  · obtain ⟨d1, hv⟩ := d
    simp only at hd
    subst hd
    have hm := CFSG.RankThree.PartOne.N143.statedClassicalModel_of_isoLie_A hv e
    obtain ⟨hp, he⟩ := KOutLin_aux_card_two hQc
    rw [hp, he] at hm
    have h : CFSG.Blueprint.LieModel S .PSL (5 + 1) 2 1 := Or.inl ⟨by decide, hm⟩
    exact CFSG.LargeExtraspecial.DW.isPGroup_outer_psl (by norm_num) h
  · obtain ⟨d1, hv⟩ := d
    simp only at hd
    subst hd
    have hm := CFSG.RankThree.PartOne.N143.statedClassicalModel_of_isoLie_A hv e
    obtain ⟨hp, he⟩ := KOutLin_aux_card_two hQc
    rw [hp, he] at hm
    have h : CFSG.Blueprint.LieModel S .PSL (6 + 1) 2 1 := Or.inl ⟨by decide, hm⟩
    exact CFSG.LargeExtraspecial.DW.isPGroup_outer_psl (by norm_num) h

end CFSG.LocalAnalysis.RankThreeUC.S15
