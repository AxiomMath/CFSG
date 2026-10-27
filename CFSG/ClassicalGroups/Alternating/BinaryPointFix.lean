module

public import CFSG.LocalAnalysis.ComponentInitial.BinarySymplecticTransvection
public import CFSG.ClassicalGroups.Alternating.Transvections

public section

namespace CFSG.ClassicalGroups.Alternating.BinaryPointFix

open Module Submodule CFSG.LocalAnalysis.ComponentInitial
open CFSG.LocalAnalysis.ComponentInitial.BinarySymplecticTransvection

variable {V : Type*} [AddCommGroup V] [Module (ZMod 2) V] {B : LinearMap.BilinForm (ZMod 2) V}

theorem apply_eq_zero_of_mul_apply_eq (hB : B.IsAlt) {u w y : V} (huw : B u w = 1)
    (hy : ((binarySymplecticTransvection B hB u * binarySymplecticTransvection B hB w :
      LinearMap.GeneralLinearGroup (ZMod 2) V) : V →ₗ[ZMod 2] V) y = y) :
    B y u = 0 ∧ B y w = 0 := by
  rw [gl_mul_apply, binarySymplecticTransvection_apply, binarySymplecticTransvection_apply,
    map_add, map_smul, LinearMap.add_apply, LinearMap.smul_apply, smul_eq_mul, add_assoc] at hy
  have h0 : (B y u + B y w * B w u) • u + B y w • w = 0 := by
    rw [add_comm]
    exact add_left_cancel (hy.trans (add_zero y).symm)
  obtain ⟨h1, h2⟩ :=
    LinearIndependent.pair_iff.mp (linearIndependent_pair_of_apply_eq_one hB huw) _ _ h0
  refine ⟨?_, h2⟩
  rwa [h2, zero_mul, add_zero] at h1

theorem mul_pow_three (hB : B.IsAlt) (hBn : B.Nondegenerate) {u w : V} (huw : B u w = 1) :
    (binarySymplecticTransvection B hB u * binarySymplecticTransvection B hB w) ^ 3 = 1 := by
  rw [← orderOf_mul_of_eq_one hB hBn huw]
  exact pow_orderOf_eq_one _

theorem mul_apply_of_apply_eq_zero (hB : B.IsAlt) {u w v : V} (hu : B v u = 0)
    (hw : B v w = 0) :
    ((binarySymplecticTransvection B hB u * binarySymplecticTransvection B hB w :
      LinearMap.GeneralLinearGroup (ZMod 2) V) : V →ₗ[ZMod 2] V) v = v := by
  have h1 : (binarySymplecticTransvection B hB w : V →ₗ[ZMod 2] V) v = v := by
    rw [binarySymplecticTransvection_apply, hw, zero_smul, add_zero]
  rw [gl_mul_apply, h1, binarySymplecticTransvection_apply, hu, zero_smul, add_zero]

theorem linearIndependent_pair_of_ne {a b : V} (ha : a ≠ 0) (hb : b ≠ 0) (hab : a ≠ b) :
    LinearIndependent (ZMod 2) ![a, b] := by
  rw [LinearIndependent.pair_iff]
  intro s t hst
  rcases zmod_two_cases s with rfl | rfl <;> rcases zmod_two_cases t with rfl | rfl
  · exact ⟨rfl, rfl⟩
  · rw [zero_smul, one_smul, zero_add] at hst
    exact absurd hst hb
  · rw [zero_smul, one_smul, add_zero] at hst
    exact absurd hst ha
  · rw [one_smul, one_smul] at hst
    refine absurd ?_ hab
    rw [← sub_eq_zero, sub_eq_add_neg, ZModModule.neg_eq_self, hst]

theorem eq_zero_or_eq_of_forall [FiniteDimensional (ZMod 2) V] (hB : B.IsAlt)
    (hBn : B.Nondegenerate) (hdim : 3 ≤ finrank (ZMod 2) V) {v₀ y : V} (hv₀ : v₀ ≠ 0)
    (h : ∀ u w, B v₀ u = 0 → B v₀ w = 0 → B u w = 1 → B y u = 0) : y = 0 ∨ y = v₀ := by
  by_contra hne
  rw [not_or] at hne
  obtain ⟨hy0, hyv⟩ := hne
  obtain ⟨u, hu0, hyu, hu_ne0, hu_ne⟩ : ∃ u, B v₀ u = 0 ∧ B y u = 1 ∧ u ≠ 0 ∧ u ≠ v₀ := by
    rcases zmod_two_cases (B v₀ y) with hvy | hvy
    · obtain ⟨u, hu⟩ :=
        alternating_pairing_surjectivity hBn (linearIndependent_pair_of_ne hv₀ hy0 (Ne.symm hyv))
          ![0, 1]
      have h0 := congrFun hu 0
      have h1 := congrFun hu 1
      simp only [LinearMap.pi_apply, Matrix.cons_val_zero, Matrix.cons_val_one] at h0 h1
      refine ⟨u, h0, h1, ?_, ?_⟩
      · rintro rfl
        rw [map_zero] at h1
        exact absurd h1 (by decide)
      · rintro rfl
        rw [symm_apply hB, hvy] at h1
        exact absurd h1 (by decide)
    · obtain ⟨-, hsplit⟩ := alternating_hyperbolic_splitting hB hBn hv₀
      obtain ⟨-, -, hmem, -, -, hfin⟩ := hsplit y hvy
      have hne : B.orthogonal (span (ZMod 2) {v₀, y}) ≠ ⊥ := by
        intro hbot
        rw [hbot, finrank_bot] at hfin
        omega
      obtain ⟨t, ht, ht0⟩ := Submodule.exists_mem_ne_zero_of_ne_bot hne
      have htv : B t v₀ = 0 := (hmem t).mp ht v₀ (subset_span (by simp))
      have hty : B t y = 0 := (hmem t).mp ht y (subset_span (by simp))
      refine ⟨v₀ + t, ?_, ?_, ?_, ?_⟩
      · rw [map_add, hB.self_eq_zero, zero_add, ← symm_apply hB, htv]
      · rw [map_add, symm_apply hB v₀ y, hvy, ← symm_apply hB, hty, add_zero]
      · intro h0
        have htv' : t = v₀ := by
          rw [← sub_eq_zero, sub_eq_add_neg, ZModModule.neg_eq_self, add_comm, h0]
        rw [htv', hvy] at hty
        exact absurd hty (by decide)
      · intro h0
        exact ht0 (by simpa using h0)
  obtain ⟨w, hw⟩ :=
    alternating_pairing_surjectivity hBn (linearIndependent_pair_of_ne hv₀ hu_ne0 (Ne.symm hu_ne))
      ![0, 1]
  have hw0 := congrFun hw 0
  have hw1 := congrFun hw 1
  simp only [LinearMap.pi_apply, Matrix.cons_val_zero, Matrix.cons_val_one] at hw0 hw1
  have := h u w hu0 hw0 hw1
  rw [hyu] at this
  exact absurd this (by decide)

theorem eq_transvection_of_forall_fix [FiniteDimensional (ZMod 2) V] (hB : B.IsAlt)
    (hBn : B.Nondegenerate) (hdim : 3 ≤ finrank (ZMod 2) V)
    {A : LinearMap.GeneralLinearGroup (ZMod 2) V} (hA : A ∈ bilinIsometryGroup B)
    (hA2 : A ^ 2 = 1) (hA1 : A ≠ 1) {v₀ : V} (hv₀ : v₀ ≠ 0)
    (h : ∀ g ∈ bilinIsometryGroup B, g ^ 3 = 1 → (g : V →ₗ[ZMod 2] V) v₀ = v₀ →
      ∀ x, (g : V →ₗ[ZMod 2] V) ((A : V →ₗ[ZMod 2] V) x - x) = (A : V →ₗ[ZMod 2] V) x - x) :
    A = binarySymplecticTransvection B hB v₀ := by
  have hcomm : ∀ x, (A : V →ₗ[ZMod 2] V) x - x = 0 ∨ (A : V →ₗ[ZMod 2] V) x - x = v₀ := by
    intro x
    refine eq_zero_or_eq_of_forall hB hBn hdim hv₀ fun u w hu hw huw => ?_
    have hg := h _ (mul_mem (transvection_mem_bilinIsometryGroup hB u)
      (transvection_mem_bilinIsometryGroup hB w)) (mul_pow_three hB hBn huw)
      (mul_apply_of_apply_eq_zero hB hu hw) x
    exact (apply_eq_zero_of_mul_apply_eq hB huw hg).1
  have hle : LinearMap.range ((A : V →ₗ[ZMod 2] V) - 1) ≤ span (ZMod 2) {v₀} := by
    rintro _ ⟨x, rfl⟩
    rw [LinearMap.sub_apply, Module.End.one_apply]
    rcases hcomm x with h0 | h0
    · rw [h0]
      exact zero_mem _
    · rw [h0]
      exact mem_span_singleton_self v₀
  have hrank : finrank (ZMod 2) (LinearMap.range ((A : V →ₗ[ZMod 2] V) - 1)) ≤ 1 :=
    (Submodule.finrank_mono hle).trans (finrank_span_singleton hv₀).le
  rcases eq_one_or_eq_transvection hB hBn hA hA2 hrank with h1 | ⟨b, hb, rfl⟩
  · exact absurd h1 hA1
  · obtain ⟨x, hx⟩ := exists_apply_eq_one hBn hb
    rcases hcomm x with h0 | h0 <;>
      rw [binarySymplecticTransvection_apply, hx, one_smul, add_sub_cancel_left] at h0
    · exact absurd h0 hb
    · rw [h0]

theorem orderOf_mul_ne_four (hB : B.IsAlt) (hBn : B.Nondegenerate) (a b : V) :
    orderOf (binarySymplecticTransvection B hB a * binarySymplecticTransvection B hB b) ≠ 4 := by
  rcases zmod_two_cases (B a b) with h | h
  · have hcomm : binarySymplecticTransvection B hB a * binarySymplecticTransvection B hB b *
        binarySymplecticTransvection B hB a = binarySymplecticTransvection B hB b := by
      rw [mul_mul_self, symm_apply hB a b, h, zero_smul, add_zero]
    have hsq : (binarySymplecticTransvection B hB a * binarySymplecticTransvection B hB b) ^ 2 =
        1 := by
      rw [sq, ← mul_assoc, hcomm, mul_self]
    intro h4
    have := orderOf_dvd_of_pow_eq_one hsq
    rw [h4] at this
    exact absurd this (by decide)
  · rw [orderOf_mul_of_eq_one hB hBn h]
    decide

end CFSG.ClassicalGroups.Alternating.BinaryPointFix
