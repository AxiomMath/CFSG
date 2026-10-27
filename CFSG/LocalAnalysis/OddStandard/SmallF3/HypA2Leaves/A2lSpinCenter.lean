module

public import CFSG.LocalAnalysis.OddStandard.SmallF3.HypA2Leaves.A2lRowOmegaE

public section

namespace CFSG.OddStandard.SmallF3.HypA2Leaves

open Subgroup CFSG.LieType.Universal.Spin CFSG.ClassicalGroups.Orthogonal CFSG.LieType.Steinberg
open CFSG.Blueprint (LieModel)
open CFSG.Open (StatedScalars StatedOmega StatedQuadMinus)
open scoped MatrixGroups

section Splits

variable {F : Type} [Field F] [Finite F]

theorem a2l_splits_spinOdd (hk : ringChar F ≠ 2) {n : ℕ} (hn : 3 ≤ n) :
    a2lSplits (spinGroup (quadOdd n F)) := by
  intro E _ _ π hπ hker h2
  obtain ⟨σ, hσ, -, -⟩ := spinOdd_central_two_extension_splitting hn hk hπ hker h2
  exact ⟨σ, hσ⟩

theorem a2l_splits_spinPlus (hk : ringChar F ≠ 2) {n : ℕ} (hn : 3 ≤ n) :
    a2lSplits (spinGroup (quadPlus n F)) := by
  intro E _ _ π hπ hker h2
  obtain ⟨σ, hσ, -, -⟩ := spinPlus_central_two_extension_splitting hn hk hπ hker h2
  exact ⟨σ, hσ⟩

theorem a2l_splits_spinMinus (hk : ringChar F ≠ 2) {b c : F}
    (hirr : ∀ s : F, s ^ 2 + b * s + c ≠ 0) {n : ℕ} (hn : 4 ≤ n) :
    a2lSplits (spinGroup (quadMinus n F b c)) := by
  intro E _ _ π hπ hker h2
  obtain ⟨σ, hσ, -, -⟩ := spinMinus_central_two_extension_splitting hn hk hirr hπ hker h2
  exact ⟨σ, hσ⟩

end Splits

section Odd

variable {F : Type} [Field F]

theorem a2l_center_spinOdd_le_ker (h2 : (2 : F) ≠ 0) {n : ℕ} (hn : 3 ≤ n) :
    center (spinGroup (quadOdd n F)) ≤ (spinMatrix (quadOdd n F)).ker := by
  obtain ⟨-, hkerC, hkerZ⟩ := spinToStatedProj_quadOdd h2 hn
  rw [← hkerZ, hkerC]
  have hodd : Odd (Fintype.card (Fin n ⊕ Fin n ⊕ Unit)) := by
    simp only [Fintype.card_sum, Fintype.card_fin, Fintype.card_unit]
    exact ⟨n, by ring⟩
  exact comap_statedScalars_le_ker_of_odd hodd h2 (coe_quadOdd n F)
    (exists_map_ne_zero_of_hypPair _ (oddPair F (⟨0, by omega⟩ : Fin n)))
    (range_spinMatrix_quadOdd h2 hn)

theorem a2l_finite_spinOdd [Finite F] (h2 : (2 : F) ≠ 0) (n : ℕ) :
    Finite (spinGroup (quadOdd n F)) :=
  finite_spinGroup_of_ker _ (coe_ker_spinMatrix_quadOdd h2)

theorem a2l_card_center_spinOdd_le_two [Finite F] (h2 : (2 : F) ≠ 0) {n : ℕ} (hn : 3 ≤ n) :
    Nat.card (center (spinGroup (quadOdd n F))) ≤ 2 := by
  haveI := a2l_finite_spinOdd h2 n
  exact (Subgroup.card_le_of_le (a2l_center_spinOdd_le_ker h2 hn)).trans
    (card_ker_spinMatrix_le_two _ (coe_ker_spinMatrix_quadOdd h2))

end Odd

section Minus

variable {F : Type} [Field F] {b c : F}

theorem a2l_neg_not_mem_elementary_quadMinus_four [Finite F]
    (hirr : ∀ s : F, s ^ 2 + b * s + c ≠ 0) (h2 : (2 : F) ≠ 0) :
    (LinearEquiv.neg F : (Fin (4 - 1) ⊕ Fin (4 - 1) ⊕ Fin 2 → F) ≃ₗ[F]
        (Fin (4 - 1) ⊕ Fin (4 - 1) ⊕ Fin 2 → F)) ∉ elementaryGroup (quadMinus 4 F b c) := by
  rw [CFSG.ClassicalInvolution.neg_mem_elementaryGroup_quadMinus_iff h2 hirr le_rfl]
  rintro ⟨r, hr⟩
  have h : (-1 : F) ^ (4 - 1) * (4 * c - b ^ 2) = b ^ 2 - 4 * c := by
    norm_num
  rw [h] at hr
  apply hirr ((r - b) / 2)
  field_simp
  linear_combination -hr

theorem a2l_center_spinMinus_four_le_ker [Finite F] (hirr : ∀ s : F, s ^ 2 + b * s + c ≠ 0)
    (h2 : (2 : F) ≠ 0) :
    center (spinGroup (quadMinus 4 F b c)) ≤ (spinMatrix (quadMinus 4 F b c)).ker := by
  intro z hz
  have hn : 4 ≤ 4 := le_rfl
  obtain ⟨-, hkerC, hkerZ⟩ := spinToStatedProj_quadMinus (K := F) (b := b) (c := c) hn hirr
  have hz' : z ∈ (StatedScalars _ F).comap (spinMatrix (quadMinus 4 F b c)) := by
    rw [← hkerC, hkerZ]
    exact hz
  obtain ⟨s, hs⟩ : spinMatrix (quadMinus 4 F b c) z ∈ StatedScalars _ F := hz'
  have hR := range_spinMatrix_quadMinus (K := F) (b := b) (c := c) hn hirr
  have hmem : Matrix.GeneralLinearGroup.scalar _ s ∈
      StatedOmega (StatedQuadMinus 4 F b c) := by
    rw [hs, ← hR]
    exact ⟨_, rfl⟩
  have hv : ∃ v, quadMinus 4 F b c v ≠ 0 :=
    exists_map_ne_zero_of_hypPair _ (minusPair F b c (⟨0, by omega⟩ : Fin (4 - 1)))
  have hsq := sq_eq_one_of_scalar_mem_statedOmega (coe_quadMinus 4 F b c) hv hmem
  have hs1 : (s : F) = 1 := by
    rcases (mul_self_eq_one_iff (a := (s : F))).1 (by rw [← pow_two]; exact hsq) with h | h
    · exact h
    · exfalso
      refine a2l_neg_not_mem_elementary_quadMinus_four hirr h2 ?_
      have hE := commutator_orthogonalGroup_quadMinus (K := F) (b := b) (c := c) hn hirr
      have hy := (statedOmegaEquiv (coe_quadMinus 4 F b c) hE ⟨_, hmem⟩).2
      rw [coe_statedOmegaEquiv] at hy
      convert hy using 1
      refine LinearEquiv.ext fun v => ?_
      ext i
      rw [toLinEquiv_apply, Matrix.GeneralLinearGroup.coe_scalar, Matrix.scalar_apply,
        Matrix.mulVec_diagonal]
      simp [h]
  rw [MonoidHom.mem_ker, ← hs]
  exact Units.ext (by rw [Matrix.GeneralLinearGroup.coe_scalar, hs1, map_one, Units.val_one])

theorem a2l_finite_spinMinus [Finite F] (hirr : ∀ s : F, s ^ 2 + b * s + c ≠ 0) (n : ℕ) :
    Finite (spinGroup (quadMinus n F b c)) :=
  finite_spinGroup_of_ker _ (coe_ker_spinMatrix_quadMinus hirr)

theorem a2l_card_center_spinMinus_four_le_two [Finite F]
    (hirr : ∀ s : F, s ^ 2 + b * s + c ≠ 0) (h2 : (2 : F) ≠ 0) :
    Nat.card (center (spinGroup (quadMinus 4 F b c))) ≤ 2 := by
  haveI := a2l_finite_spinMinus hirr 4
  exact (Subgroup.card_le_of_le (a2l_center_spinMinus_four_le_ker hirr h2)).trans
    (card_ker_spinMatrix_le_two _ (coe_ker_spinMatrix_quadMinus hirr))

end Minus

theorem a2l_not_inChev2_pOmegaOdd33 (hC : HypA2.ChevOddInChev2) {S : Type} [Group S] [Finite S]
    (h : LieModel S .POmegaOdd 3 3 1) : ¬ GH74.GLS.InChev2 S := fun hI =>
  a2l_false_of_card (hC S 3 Nat.prime_three (by norm_num) ⟨.POmegaOdd, 3, 1, h⟩ hI)
    (c := Open.ordBC 3 (3 ^ 1))
    ((CFSG.ClassicalInvolution.card_statedClassicalModel_of_ne_two (by norm_num)
      (GH74.statedClassicalModel_of_lieModel (by norm_num) h)).2.2.2.1 rfl) (by decide)

theorem a2l_not_inChev2_pOmegaMinus43 (hC : HypA2.ChevOddInChev2) {S : Type} [Group S] [Finite S]
    (h : LieModel S .POmegaMinus 4 3 1) : ¬ GH74.GLS.InChev2 S := fun hI =>
  a2l_false_of_card (hC S 3 Nat.prime_three (by norm_num) ⟨.POmegaMinus, 4, 1, h⟩ hI)
    (c := Open.ordTwistedD 4 (3 ^ 1))
    ((CFSG.ClassicalInvolution.card_statedClassicalModel_of_ne_two (by norm_num)
      (GH74.statedClassicalModel_of_lieModel (by norm_num) h)).2.2.2.2.2 rfl) (by decide)

end CFSG.OddStandard.SmallF3.HypA2Leaves
