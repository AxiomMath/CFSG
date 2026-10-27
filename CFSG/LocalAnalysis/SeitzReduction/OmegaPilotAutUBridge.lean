module

import CFSG.RankThree.Classical.SteinbergBJOrthogonalHighWitt
public import CFSG.LocalAnalysis.SeitzReduction.OmegaPilotPerp

public section

namespace CFSG.SeitzReduction.OmegaPilot

open Subgroup QuadraticMap CFSG.ClassicalGroups.Orthogonal
open CFSG.RankThree.Classical2 (orthDerived)
open CFSG.ComponentClassification.CatalogueBOrthogonalSemilinear

section HypCoord

variable {K : Type*} [Field K] {ι : Type*} [DecidableEq ι] {Q : QuadraticForm K (ι → K)}
  {a b : ι}

structure PairDisjoint (a b a' b' : ι) : Prop where
  left_ne_left : a' ≠ a
  left_ne_right : a' ≠ b
  right_ne_left : b' ≠ a
  right_ne_right : b' ≠ b

omit [DecidableEq ι] in
theorem PairDisjoint.symm {a b a' b' : ι} (h : PairDisjoint a b a' b') :
    PairDisjoint a' b' a b :=
  ⟨h.left_ne_left.symm, h.right_ne_left.symm, h.left_ne_right.symm, h.right_ne_right.symm⟩

omit [DecidableEq ι] in
theorem PairDisjoint.swap_left {a b a' b' : ι} (h : PairDisjoint a b a' b') :
    PairDisjoint b a a' b' :=
  ⟨h.left_ne_right, h.left_ne_left, h.right_ne_right, h.right_ne_left⟩

omit [DecidableEq ι] in
theorem PairDisjoint.swap_right {a b a' b' : ι} (h : PairDisjoint a b a' b') :
    PairDisjoint a b b' a' :=
  ⟨h.right_ne_left, h.right_ne_right, h.left_ne_left, h.left_ne_right⟩

theorem IsHypCoord.symm (h : IsHypCoord Q a b) : IsHypCoord Q b a :=
  ⟨h.ne.symm, h.map_right, h.map_left, h.polar_right, h.polar_left⟩

@[expose] def IsHypCoord.hypPair (h : IsHypCoord Q a b) : HypPair Q :=
  ⟨Pi.single a 1, Pi.single b 1, h.map_left, h.map_right, by rw [h.polar_left]; simp⟩

@[simp] theorem IsHypCoord.hypPair_e (h : IsHypCoord Q a b) : h.hypPair.e = Pi.single a 1 := rfl

@[simp] theorem IsHypCoord.hypPair_f (h : IsHypCoord Q a b) : h.hypPair.f = Pi.single b 1 := rfl

theorem IsHypCoord.orth (h : IsHypCoord Q a b) {a' b' : ι} (h' : IsHypCoord Q a' b')
    (hd : PairDisjoint a b a' b') : h.hypPair.Orth h'.hypPair where
  ee := by rw [hypPair_e, hypPair_e, h.polar_left, Pi.single_eq_of_ne hd.left_ne_right.symm]
  ef := by rw [hypPair_e, hypPair_f, h.polar_left, Pi.single_eq_of_ne hd.right_ne_right.symm]
  fe := by rw [hypPair_f, hypPair_e, h.polar_right, Pi.single_eq_of_ne hd.left_ne_left.symm]
  ff := by rw [hypPair_f, hypPair_f, h.polar_right, Pi.single_eq_of_ne hd.right_ne_left.symm]

theorem IsHypCoord.polar_eq (h : IsHypCoord Q a b) (x y : ι → K) :
    polar Q x y = y a * x b + y b * x a + polar Q x (perpPart a b y) := by
  conv_lhs => rw [eq_add_perpPart a b y]
  rw [polar_add_right, polar_add_right, polar_smul_right, polar_smul_right,
    polar_comm Q x (Pi.single a 1), h.polar_left, polar_comm Q x (Pi.single b 1), h.polar_right,
    smul_eq_mul, smul_eq_mul]

theorem IsHypCoord.polarNondegOn_perpSub (hQ : (polarBilin Q).Nondegenerate)
    (h : IsHypCoord Q a b) : PolarNondegOn Q (perpSub K a b) := by
  intro x hx hxU
  apply eq_zero_of_polar_eq_zero hQ
  intro y
  rw [h.polar_eq x y, hx.1, hx.2, hxU _ (perpPart_mem h.ne y)]
  ring

theorem single_mem_perpSub {c : ι} (hca : c ≠ a) (hcb : c ≠ b) :
    (Pi.single c (1 : K) : ι → K) ∈ perpSub K a b :=
  ⟨Pi.single_eq_of_ne hca.symm 1, Pi.single_eq_of_ne hcb.symm 1⟩

theorem IsHypCoord.hypPair_mem_perpSub {a' b' : ι} (h' : IsHypCoord Q a' b')
    (hd : PairDisjoint a b a' b') :
    h'.hypPair.e ∈ perpSub K a b ∧ h'.hypPair.f ∈ perpSub K a b :=
  ⟨single_mem_perpSub hd.left_ne_left hd.left_ne_right,
    single_mem_perpSub hd.right_ne_left hd.right_ne_right⟩

theorem IsHypCoord.eichler_mem_stabSub (h : IsHypCoord Q a b) {u w : ι → K}
    (hu : u ∈ perpSub K a b) (hw : w ∈ perpSub K a b) : eichler Q u w ∈ stabSub a b :=
  ⟨eichler_apply_of_polar_eq_zero (by rw [h.polar_left]; exact hu.2)
      (by rw [h.polar_left]; exact hw.2),
    eichler_apply_of_polar_eq_zero (by rw [h.polar_right]; exact hu.1)
      (by rw [h.polar_right]; exact hw.1)⟩

theorem exists_threeSingular_of_isHypCoord {a₁ b₁ a₂ b₂ : ι} (h : IsHypCoord Q a b)
    (h₁ : IsHypCoord Q a₁ b₁) (h₂ : IsHypCoord Q a₂ b₂) (d₁ : PairDisjoint a b a₁ b₁)
    (d₂ : PairDisjoint a b a₂ b₂) (d₁₂ : PairDisjoint a₁ b₁ a₂ b₂) :
    ∃ T : Submodule K (ι → K), Module.finrank K T = 3 ∧ ∀ x ∈ T, Q x = 0 :=
  exists_totallySingular_of_hypPairs (h.orth h₁ d₁) (h.orth h₂ d₂) (h₁.orth h₂ d₁₂)

end HypCoord

section Bridge

variable {K : Type*} [Field K] {d : ℕ} {Q : QuadraticForm K (Fin d → K)}

abbrev simMap (g : similarityPairs Q) : (Fin d → K) ≃+ (Fin d → K) :=
  coordinateSemilinearMap g.val

theorem simMap_smul (g : similarityPairs Q) (c : K) (v : Fin d → K) :
    simMap g (c • v) = g.val.right c • simMap g v :=
  coordinateSemilinearMap_smul g.val c v

theorem map_simMap (g : similarityPairs Q) (v : Fin d → K) :
    Q (simMap g v) = (multiplier Q g : K) * g.val.right (Q v) :=
  multiplier_spec Q g v

theorem exists_conj_orthDerived (g : similarityPairs Q) (E : orthDerived Q) :
    ∃ E' : orthDerived Q,
      (∀ y, simMap g ((E : (Fin d → K) ≃ₗ[K] (Fin d → K)) y) =
        (E' : (Fin d → K) ≃ₗ[K] (Fin d → K)) (simMap g y)) ∧
      matrixProjectiveConjugation Q g (projHom Q E) = projHom Q E' := by
  set A := (derivedEquiv Q).symm E with hA
  refine ⟨derivedEquiv Q (matrixDerivedConjugation Q g A), fun y => ?_, ?_⟩
  · have hAE : matrixLinearEquiv A.val = (E : (Fin d → K) ≃ₗ[K] (Fin d → K)) := by
      change ((derivedEquiv Q A : orthDerived Q) : (Fin d → K) ≃ₗ[K] (Fin d → K)) = _
      rw [hA, MulEquiv.apply_symm_apply]
    rw [coe_derivedEquiv]
    change _ = matrixLinearEquiv (matrixConjugation g.val A.val) (simMap g y)
    rw [matrixConjugation_vector, AddEquiv.symm_apply_apply, hAE]
  · change matrixProjectiveConjugation Q g (matrixProjectiveProjection Q A) =
      matrixProjectiveProjection Q ((derivedEquiv Q).symm
        (derivedEquiv Q (matrixDerivedConjugation Q g A)))
    rw [MulEquiv.symm_apply_apply, matrixProjectiveConjugation_mk]

theorem commute_of_kappa_projHom_eq [CharP K 2] (hQ : ∃ v, Q v ≠ 0) (g : similarityPairs Q)
    {E : orthDerived Q} (h : matrixProjectiveConjugation Q g (projHom Q E) = projHom Q E)
    (y : Fin d → K) :
    simMap g ((E : (Fin d → K) ≃ₗ[K] (Fin d → K)) y) =
      (E : (Fin d → K) ≃ₗ[K] (Fin d → K)) (simMap g y) := by
  obtain ⟨E', h1, h2⟩ := exists_conj_orthDerived g E
  rw [h2] at h
  rw [h1 y, projHom_injective hQ h]

theorem kappa_eq_conj_of_eq_smul (g : similarityPairs Q) (X : orthDerived Q) {γ : K}
    (hγ : γ ≠ 0)
    (h : ∀ y, simMap g y = γ • (X : (Fin d → K) ≃ₗ[K] (Fin d → K)) y) :
    matrixProjectiveConjugation Q g = MulAut.conj (projHom Q X) := by
  apply MulEquiv.ext
  intro p
  obtain ⟨E, rfl⟩ := projHom_surjective Q p
  obtain ⟨E', h1, h2⟩ := exists_conj_orthDerived g E
  rw [h2, MulAut.conj_apply, ← map_inv, ← map_mul, ← map_mul]
  congr 1
  apply Subtype.ext
  apply LinearEquiv.ext
  intro v
  have hX : ∀ y, (E' : (Fin d → K) ≃ₗ[K] (Fin d → K))
      ((X : (Fin d → K) ≃ₗ[K] (Fin d → K)) y) =
      (X : (Fin d → K) ≃ₗ[K] (Fin d → K)) ((E : (Fin d → K) ≃ₗ[K] (Fin d → K)) y) := by
    intro y
    have h3 := h1 y
    rw [h, h, LinearEquiv.map_smul] at h3
    exact (smul_right_injective _ hγ h3).symm
  have hv := hX (((X : (Fin d → K) ≃ₗ[K] (Fin d → K)))⁻¹ v)
  rw [LinearEquiv.apply_inv_apply'] at hv
  rw [hv]
  rfl

theorem elementaryGroup_le_orthDerived [Finite K] (hQ : (polarBilin Q).Nondegenerate)
    (hT : ∃ T : Submodule K (Fin d → K), Module.finrank K T = 3 ∧ ∀ x ∈ T, Q x = 0) :
    elementaryGroup Q ≤ orthDerived Q :=
  (CFSG.RankThree.Classical.orthDerived_eq_and_le_closure hQ hT).1.ge

theorem eichler_mem_orthDerived [Finite K] (hQ : (polarBilin Q).Nondegenerate)
    (hT : ∃ T : Submodule K (Fin d → K), Module.finrank K T = 3 ∧ ∀ x ∈ T, Q x = 0)
    (u w : Fin d → K) : eichler Q u w ∈ orthDerived Q := by
  rw [(CFSG.RankThree.Classical.orthDerived_eq_and_le_closure hQ hT).1]
  exact eichler_mem_elementaryGroup Q u w

end Bridge

section CoordinatePairs

open CFSG.ComponentClassification.CatalogueBOrthogonalPointData (plusIndexEquiv minusIndexEquiv)

theorem pairDisjoint_plus {n : ℕ} {i j : Fin n} (hij : i ≠ j) :
    PairDisjoint (plusIndexEquiv n (.inl i)) (plusIndexEquiv n (.inr i))
      (plusIndexEquiv n (.inl j)) (plusIndexEquiv n (.inr j)) where
  left_ne_left h := hij (Sum.inl_injective ((plusIndexEquiv n).injective h)).symm
  left_ne_right h := Sum.inl_ne_inr ((plusIndexEquiv n).injective h)
  right_ne_left h := Sum.inr_ne_inl ((plusIndexEquiv n).injective h)
  right_ne_right h := hij (Sum.inr_injective ((plusIndexEquiv n).injective h)).symm

theorem pairDisjoint_minus {n : ℕ} (hn : 1 ≤ n) {i j : Fin (n - 1)} (hij : i ≠ j) :
    PairDisjoint (minusIndexEquiv n hn (.inl i)) (minusIndexEquiv n hn (.inr (.inl i)))
      (minusIndexEquiv n hn (.inl j)) (minusIndexEquiv n hn (.inr (.inl j))) where
  left_ne_left h := hij (Sum.inl_injective ((minusIndexEquiv n hn).injective h)).symm
  left_ne_right h := Sum.inl_ne_inr ((minusIndexEquiv n hn).injective h)
  right_ne_left h := Sum.inr_ne_inl ((minusIndexEquiv n hn).injective h)
  right_ne_right h :=
    hij (Sum.inl_injective (Sum.inr_injective ((minusIndexEquiv n hn).injective h))).symm

theorem one_le_of_four_le {n : ℕ} (hn : 4 ≤ n) : 1 ≤ n := le_trans (by decide) hn

theorem exists_two_ne {n : ℕ} (hn : 3 ≤ n) (k : Fin n) : ∃ i j : Fin n, i ≠ k ∧ j ≠ k ∧ i ≠ j := by
  have hcard : 2 ≤ ((Finset.univ : Finset (Fin n)).erase k).card := by
    rw [Finset.card_erase_of_mem (Finset.mem_univ k), Finset.card_univ, Fintype.card_fin]
    omega
  obtain ⟨i, hi, j, hj, hij⟩ := Finset.one_lt_card.1 hcard
  exact ⟨i, j, Finset.ne_of_mem_erase hi, Finset.ne_of_mem_erase hj, hij⟩

end CoordinatePairs

end CFSG.SeitzReduction.OmegaPilot
