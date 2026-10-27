module

public import CFSG.LocalAnalysis.GLTheoremA.CatC.KD264LieRowXUnStructGrp
public import Mathlib.LinearAlgebra.Matrix.GeneralLinearGroup.Card
public import Mathlib.NumberTheory.Multiplicity
public import Mathlib.Algebra.Order.Field.Basic
public import Mathlib.Tactic.Positivity.Finset

public section

namespace CFSG.LocalAnalysis.GLTheoremA.KD264Lie.RowXUn.Struct

open scoped commutatorElement

variable {K : Type*} [Field K] {V : Type*} [AddCommGroup V] [Module K V]

@[expose] def scalars (K : Type*) [Field K] (V : Type*) [AddCommGroup V] [Module K V] :
    Subgroup (V ≃ₗ[K] V) :=
  (DistribMulAction.toModuleAut K V : Kˣ →* (V ≃ₗ[K] V)).range

theorem mem_scalars_iff {g : V ≃ₗ[K] V} :
    g ∈ scalars K V ↔ ∃ c : Kˣ, ∀ v, g v = (c : K) • v := by
  constructor
  · rintro ⟨c, rfl⟩
    exact ⟨c, fun v => rfl⟩
  · rintro ⟨c, hc⟩
    exact ⟨c, LinearEquiv.ext fun v => (hc v).symm⟩

theorem card_units_eq_three [Finite K] (hK : Nat.card K = 4) : Nat.card Kˣ = 3 := by
  rw [Nat.card_units, hK]

theorem units_pow_three [Finite K] (hK : Nat.card K = 4) (c : Kˣ) : c ^ 3 = 1 := by
  have := pow_card_eq_one' (G := Kˣ) (x := c)
  rwa [card_units_eq_three hK] at this

theorem scalarLike_scalars [Finite K] (hK : Nat.card K = 4) : ScalarLike (scalars K V) where
  central := by
    intro s hs
    rw [Subgroup.mem_center_iff]
    intro g
    obtain ⟨c, hc⟩ := mem_scalars_iff.1 hs
    refine LinearEquiv.ext fun v => ?_
    simp only [LinearEquiv.mul_apply]
    rw [hc, hc, map_smul]
  cube := by
    rintro _ ⟨c, rfl⟩
    rw [← map_pow, units_pow_three hK, map_one]
  card_le := by
    have h := Nat.card_le_card_of_surjective
      ((DistribMulAction.toModuleAut K V : Kˣ →* (V ≃ₗ[K] V)).rangeRestrict)
      (MonoidHom.rangeRestrict_surjective _)
    exact h.trans (card_units_eq_three hK).le

theorem card_linearEquiv_eq (hK : Nat.card K = 4) {N : Type*} [AddCommGroup N] [Module K N]
    [Module.Finite K N] {m : ℕ} (hN : Module.finrank K N = m) :
    Nat.card (N ≃ₗ[K] N) = ∏ i : Fin m, (4 ^ m - 4 ^ (i : ℕ)) := by
  have : Finite K := Nat.finite_of_card_ne_zero (by omega)
  have : Fintype K := Fintype.ofFinite K
  have hq : Fintype.card K = 4 := by rw [← Nat.card_eq_fintype_card]; exact hK
  let b := Module.finBasisOfFinrankEq K N hN
  have h := Matrix.card_GL_field (𝔽 := K) m
  rw [hq] at h
  rw [← h]
  exact (Nat.card_congr ((Matrix.GeneralLinearGroup.toLin' b).trans
    (LinearMap.GeneralLinearGroup.generalLinearEquiv K N)).toEquiv).symm

theorem prod_range_succ_gl (m : ℕ) :
    ∏ i ∈ Finset.range (m + 1), (4 ^ (m + 1) - 4 ^ i) =
      4 ^ m * (∏ i ∈ Finset.range m, (4 ^ m - 4 ^ i)) * (4 ^ (m + 1) - 1) := by
  rw [Finset.prod_range_succ']
  have h : ∀ i ∈ Finset.range m, (4 ^ (m + 1) - 4 ^ (i + 1)) = 4 * (4 ^ m - 4 ^ i) := by
    intro i _
    rw [Nat.mul_sub, pow_succ' 4 m, pow_succ' 4 i]
  rw [Finset.prod_congr rfl h, Finset.prod_mul_distrib, Finset.prod_const, Finset.card_range]
  simp only [pow_zero, mul_comm]

theorem padicValNat_prod_eq (m : ℕ) :
    padicValNat 3 (∏ i ∈ Finset.range m, (4 ^ m - 4 ^ i)) = m + padicValNat 3 m.factorial := by
  haveI : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  induction m with
  | zero => simp
  | succ m ih =>
    rw [prod_range_succ_gl]
    have h1 : 4 ^ m ≠ 0 := by positivity
    have h2 : ∏ i ∈ Finset.range m, (4 ^ m - 4 ^ i) ≠ 0 :=
      Finset.prod_ne_zero_iff.2 fun i hi => by
        have := Nat.pow_lt_pow_right (by norm_num : 1 < 4) (Finset.mem_range.1 hi)
        omega
    have h3 : 4 ^ (m + 1) - 1 ≠ 0 := by
      have : 1 < 4 ^ (m + 1) := Nat.one_lt_pow (by omega) (by norm_num)
      omega
    rw [padicValNat.mul (mul_ne_zero h1 h2) h3, padicValNat.mul h1 h2, ih]
    have h4 : padicValNat 3 (4 ^ m) = 0 :=
      padicValNat.eq_zero_of_not_dvd (fun h => by
        have := (Nat.Prime.dvd_of_dvd_pow Nat.prime_three h)
        omega)
    have h5 : padicValNat 3 (4 ^ (m + 1) - 1) = 1 + padicValNat 3 (m + 1) := by
      have := padicValNat.pow_sub_pow (p := 3) (by decide : Odd 3) (x := 4) (y := 1)
        (by norm_num) (by norm_num) (by norm_num) (n := m + 1) (by omega)
      simpa using this
    have h6 : padicValNat 3 (m + 1).factorial =
        padicValNat 3 (m + 1) + padicValNat 3 m.factorial := by
      rw [Nat.factorial_succ]
      exact padicValNat.mul (Nat.succ_ne_zero m) (Nat.factorial_ne_zero m)
    omega

theorem finite_linearEquiv [Finite K] {N : Type*} [AddCommGroup N] [Module K N]
    [Module.Finite K N] : Finite (N ≃ₗ[K] N) := by
  have : Finite N := Module.finite_of_finite K
  exact Finite.of_injective (fun f : N ≃ₗ[K] N => (f : N → N)) DFunLike.coe_injective

theorem card_le_of_isPGroup (hK : Nat.card K = 4) {N : Type*} [AddCommGroup N] [Module K N]
    [Module.Finite K N] {m : ℕ} (hN : Module.finrank K N = m) (H : Subgroup (N ≃ₗ[K] N))
    (hH : IsPGroup 3 H) : Nat.card H ≤ 3 ^ (m + m / 2) := by
  haveI : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  have hfin : Finite K := Nat.finite_of_card_ne_zero (by omega)
  haveI : Finite (N ≃ₗ[K] N) := finite_linearEquiv
  obtain ⟨n, hn⟩ := hH.exists_card_eq
  have hdvd : 3 ^ n ∣ Nat.card (N ≃ₗ[K] N) := hn ▸ Subgroup.card_subgroup_dvd_card H
  rw [card_linearEquiv_eq hK hN,
    Fin.prod_univ_eq_prod_range (fun i => 4 ^ m - 4 ^ i) m] at hdvd
  have hne : ∏ i ∈ Finset.range m, (4 ^ m - 4 ^ i) ≠ 0 :=
    Finset.prod_ne_zero_iff.2 fun i hi => by
      have := Nat.pow_lt_pow_right (by norm_num : 1 < 4) (Finset.mem_range.1 hi)
      omega
  have hle := (padicValNat_dvd_iff_le hne).1 hdvd
  rw [padicValNat_prod_eq] at hle
  have hleg := sub_one_mul_padicValNat_factorial (p := 3) m
  have h2 : padicValNat 3 m.factorial ≤ m / 2 := by omega
  rw [hn]
  exact Nat.pow_le_pow_right (by norm_num) (by omega)

end CFSG.LocalAnalysis.GLTheoremA.KD264Lie.RowXUn.Struct

end
