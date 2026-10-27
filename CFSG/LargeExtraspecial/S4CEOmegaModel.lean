module

public import CFSG.LargeExtraspecial.S4CEOmegaSpin
public import CFSG.LocalAnalysis.ComponentClassification.UnbalancedCatalogQuadraticNormalForms
public import CFSG.Timmesfeld.Orders.ClassicalOrthogonal

public section

attribute [-instance] instAddCommGroupOfIsSimpleAddGroupOfIsNilpotent
  instCommGroupOfIsSimpleGroupOfIsNilpotent

namespace CFSG.LargeExtraspecial.S4

open Subgroup Module QuadraticMap CFSG.ClassicalGroups.Orthogonal
  CFSG.RankThree.OrthogonalInvolutions CFSG.LieType.Universal.Spin

variable {V : Type*} [AddCommGroup V] [Module (ZMod 2) V] [FiniteDimensional (ZMod 2) V]
  {Q : QuadraticForm (ZMod 2) V}

theorem exists_isometry_model (hQ : Q.polarBilin.Nondegenerate) {n : ℕ} (hn : 1 ≤ n)
    (hdim : finrank (ZMod 2) V = 2 * n) :
    (∃ L : V ≃ₗ[ZMod 2] (Fin n ⊕ Fin n → ZMod 2), ∀ v, quadPlus n (ZMod 2) (L v) = Q v) ∨
      ∃ b c : ZMod 2, (∀ s : ZMod 2, s ^ 2 + b * s + c ≠ 0) ∧
        ∃ L : V ≃ₗ[ZMod 2] (Fin (n - 1) ⊕ Fin (n - 1) ⊕ Fin 2 → ZMod 2),
          ∀ v, quadMinus n (ZMod 2) b c (L v) = Q v := by
  rcases (CFSG.ComponentClassification.UnbalancedCatalog.finite_even_regular_quadratic_normal_forms
    Q hQ).2.2.1 n hn hdim with ⟨b, hb⟩ | ⟨β, γ, -, hroot, b, hb⟩
  · refine Or.inl ⟨b.equivFun, fun w => ?_⟩
    have hw : w = ∑ i, b.repr w (.inl i) • b (.inl i) + ∑ i, b.repr w (.inr i) • b (.inr i) := by
      conv_lhs => rw [← b.sum_repr w]
      rw [Fintype.sum_sum_type]
    conv_rhs => rw [hw]
    rw [hb, quadPlus_apply]
    rfl
  · refine Or.inr ⟨β, γ, hroot, b.equivFun, fun w => ?_⟩
    have hw : w = ∑ i, b.repr w (.inl i) • b (.inl i) +
        ∑ i, b.repr w (.inr (.inl i)) • b (.inr (.inl i)) +
          b.repr w (.inr (.inr 0)) • b (.inr (.inr 0)) +
            b.repr w (.inr (.inr 1)) • b (.inr (.inr 1)) := by
      conv_lhs => rw [← b.sum_repr w]
      rw [Fintype.sum_sum_type, Fintype.sum_sum_type, Fin.sum_univ_two]
      abel
    conv_rhs => rw [hw]
    rw [hb, quadMinus_apply]
    rfl

theorem odd_prod_two_pow_sub_one (m : ℕ) :
    Odd (∏ i ∈ Finset.Icc 1 m, ((2 : ℤ) ^ (2 * i) - 1)) :=
  Finset.prod_induction _ Odd (fun _ _ ha hb => ha.mul hb) odd_one fun i hi =>
    (even_two.pow_of_ne_zero (by have := (Finset.mem_Icc.mp hi).1; omega)).sub_odd odd_one

theorem card_omegaGroup_eq (hQ : Q.polarBilin.Nondegenerate) {n : ℕ} (hn : 1 ≤ n)
    (hdim : finrank (ZMod 2) V = 2 * n) :
    ∃ M : ℕ, Odd M ∧ Nat.card (omegaGroup Q hQ) = 2 ^ (n * (n - 1)) * M := by
  have : Nontrivial V := Module.nontrivial_of_finrank_pos (R := ZMod 2) (by omega)
  have hidx := Subgroup.relIndex_mul_card (omegaGroup Q hQ)
    (TauCeti.QuadraticMap.orthogonalGroup Q)
  rw [inf_eq_left.mpr (omegaGroup_le Q hQ), relIndex_omegaGroup] at hidx
  obtain ⟨m, rfl⟩ : ∃ m, n = m + 1 := ⟨n - 1, by omega⟩
  have key : ∃ M : ℤ, Odd M ∧
      (Nat.card (TauCeti.QuadraticMap.orthogonalGroup Q) : ℤ) = 2 * 2 ^ (m * (m + 1)) * M := by
    rcases exists_isometry_model hQ hn hdim with ⟨L, hL⟩ | ⟨b, c, hirr, L, hL⟩
    · refine ⟨(2 ^ (m + 1) - 1) * ∏ i ∈ Finset.Icc 1 m, ((2 : ℤ) ^ (2 * i) - 1),
        ((even_two.pow_of_ne_zero (by omega)).sub_odd odd_one).mul
          (odd_prod_two_pow_sub_one m), ?_⟩
      rw [CFSG.Timmesfeld.ClassicalOrders.card_orthogonalGroup_congr
        (⟨L, hL⟩ : Q.IsometryEquiv (quadPlus (m + 1) (ZMod 2))),
        (CFSG.Timmesfeld.ClassicalOrders.card_quadPlus m).2, Nat.card_zmod]
      push_cast
      ring
    · refine ⟨(2 ^ (m + 1) + 1) * ∏ i ∈ Finset.Icc 1 m, ((2 : ℤ) ^ (2 * i) - 1),
        ((even_two.pow_of_ne_zero (by omega)).add_odd odd_one).mul
          (odd_prod_two_pow_sub_one m), ?_⟩
      rw [CFSG.Timmesfeld.ClassicalOrders.card_orthogonalGroup_congr
        (⟨L, hL⟩ : Q.IsometryEquiv (quadMinus (m + 1) (ZMod 2) b c)),
        (CFSG.Timmesfeld.ClassicalOrders.card_quadMinus m hirr).2, Nat.card_zmod]
      push_cast
      ring
  obtain ⟨M, hModd, hM⟩ := key
  have hM' : (Nat.card (omegaGroup Q hQ) : ℤ) = 2 ^ (m * (m + 1)) * M := by
    have h1 : ((2 * Nat.card (omegaGroup Q hQ) : ℕ) : ℤ) =
        (Nat.card (TauCeti.QuadraticMap.orthogonalGroup Q) : ℤ) := by rw [hidx]
    rw [hM] at h1
    push_cast at h1
    have h2 : (2 : ℤ) ≠ 0 := by norm_num
    exact mul_left_cancel₀ h2 (by rw [h1]; ring)
  have hM0 : 0 ≤ M := by
    have h0 : 0 ≤ (2 : ℤ) ^ (m * (m + 1)) * M := hM' ▸ Nat.cast_nonneg _
    exact (mul_nonneg_iff_of_pos_left (by positivity)).mp h0
  refine ⟨M.natAbs, Int.natAbs_odd.mpr hModd, ?_⟩
  have hk : (m + 1) * (m + 1 - 1) = m * (m + 1) := by
    rw [Nat.add_sub_cancel, mul_comm]
  rw [hk]
  apply Nat.cast_injective (R := ℤ)
  rw [Nat.cast_mul, Nat.cast_pow, Int.natAbs_of_nonneg hM0, hM']
  norm_num

namespace CEHyp

variable {K : Type*} [Group K] {π : K →* (V ≃ₗ[ZMod 2] V)} {E : Subgroup K} {a : V}
  {X : Subgroup (V ≃ₗ[ZMod 2] V)}

theorem isPGroup_two (hQ : Q.polarBilin.Nondegenerate) (ha0 : a ≠ 0) (ha : Q a = 0)
    (h : CEHyp π E a X (pointRadical Q a)) : IsPGroup 2 E := by
  intro e
  refine ⟨1, Subtype.ext ?_⟩
  have hπe : π e ∈ pointRadical Q a := h.map_eq ▸ ⟨e, e.2, rfl⟩
  obtain ⟨u, hu, he⟩ := (mem_pointRadical_iff hQ ha0 ha).mp hπe
  have hsq : π ((e : K) ^ 2) = π 1 := by
    rw [map_pow, he, pow_two, CFSG.LargeExtraspecial.eichler_mul_self hu, map_one]
  simpa using h.eq_of_mem (pow_mem e.2 2) (one_mem E) hsq

theorem ker_eq_bot_of_omega_of_odd
    [Finite K] {E₀ : Subgroup (V ≃ₗ[ZMod 2] V)} (hQ : Q.polarBilin.Nondegenerate)
    (h6 : 6 ≤ finrank (ZMod 2) V) (h : CEHyp π E a (omegaGroup Q hQ) E₀) (h2 : IsPGroup 2 E)
    (hodd : Odd (Nat.card π.ker)) : π.ker = ⊥ := by
  obtain ⟨n, hn⟩ := CFSG.ComponentClassification.UnbalancedCatalog.even_finrank_of_charTwo Q hQ
  have hdim : finrank (ZMod 2) V = 2 * n := by omega
  have hn3 : 3 ≤ n := by omega
  rcases exists_isometry_model hQ (by omega) hdim with ⟨L, hL⟩ | ⟨b, c, hirr, L, hL⟩
  · refine h.ker_eq_bot_of_injective_of_split h2 hodd
      ((O62.conjL L).symm.toMonoidHom.comp (spinAction (quadPlus n (ZMod 2))))
      ((O62.conjL L).symm.injective.comp (spinAction_quadPlus_injective n))
      (range_conjL_symm_comp_eq_omegaGroup hQ _ hL
        (range_spinAction_quadPlus_eq_omegaGroup hn3)) fun ρ hρ hker hodd' => ?_
    obtain ⟨σ, hσ, -⟩ :=
      CFSG.SectionRank.EvenCover.even_spinPlus_central_odd_extension_splitting hn3 hρ hker hodd'
    exact ⟨σ, hσ⟩
  · refine h.ker_eq_bot_of_injective_of_split h2 hodd
      ((O62.conjL L).symm.toMonoidHom.comp (spinAction (quadMinus n (ZMod 2) b c)))
      ((O62.conjL L).symm.injective.comp (spinAction_quadMinus_injective n hirr))
      (range_conjL_symm_comp_eq_omegaGroup hQ _ hL
        (range_spinAction_quadMinus_eq_omegaGroup hn3 hirr)) fun ρ hρ hker hodd' => ?_
    rcases Nat.lt_or_ge n 4 with hn4 | hn4
    · obtain rfl : n = 3 := by omega
      exact spinMinusThree_central_odd_extension_splitting hirr hρ hker hodd'
    · obtain ⟨σ, hσ, -⟩ := CFSG.SectionRank.EvenCover.even_spinMinus_central_odd_extension_splitting
        hn4 hirr hρ hker hodd'
      exact ⟨σ, hσ⟩

end CEHyp

end CFSG.LargeExtraspecial.S4
