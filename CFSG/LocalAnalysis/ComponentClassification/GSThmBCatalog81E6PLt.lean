module

public import CFSG.LocalAnalysis.ComponentClassification.GSThmBCatalog81E6PSp
public import CFSG.LocalAnalysis.ComponentInitial.LinearHigherAutomorphismGeneration
public import CFSG.LocalAnalysis.ComponentInitial.LinearHigherOuterQuotients

public section

namespace CFSG.ComponentClassification.GSThmB.P211

open CFSG Subgroup Matrix CFSG.LocalAnalysis.ComponentInitial.LinearFlag
open scoped commutatorElement

section Twist

variable {n : ℕ} {K : Type*} [Field K]

theorem twist_mem_center' (θ : MulAut (SpecialLinearGroup (Fin n) K))
    {β : MulAut (projectiveSL n K)} (hβ : ∀ g, β (proj n K g) = proj n K (θ g))
    {g : SpecialLinearGroup (Fin n) K} (hg : β (proj n K g) = proj n K g) :
    θ g * g⁻¹ ∈ center (SpecialLinearGroup (Fin n) K) := by
  apply scalars_le_center
  rw [← proj_eq_one_iff, map_mul, map_inv, ← hβ, hg, mul_inv_cancel]

theorem perfect_le_map_fixOf_proj (θ : MulAut (SpecialLinearGroup (Fin n) K))
    {β : MulAut (projectiveSL n K)} (hβ : ∀ g, β (proj n K g) = proj n K (θ g))
    {M : Subgroup (projectiveSL n K)} (hM : ⁅M, M⁆ = M) (hfix : ∀ x ∈ M, β x = x) :
    M ≤ (CatFactsSp4.fixOf θ).map (proj n K) := by
  set N := M.comap (proj n K)
  let τ : N →* center (SpecialLinearGroup (Fin n) K) :=
    { toFun := fun g => ⟨θ g * (g : SpecialLinearGroup (Fin n) K)⁻¹,
        twist_mem_center' θ hβ (hfix _ g.2)⟩
      map_one' := Subtype.ext (by simp)
      map_mul' := fun g h => by
        apply Subtype.ext
        have hc := mem_center_iff.mp
          (twist_mem_center' θ hβ (hfix _ h.2)) (g : SpecialLinearGroup (Fin n) K)⁻¹
        simp only [Subgroup.coe_mul, map_mul, _root_.mul_inv_rev]
        calc θ g * θ h * ((h : SpecialLinearGroup (Fin n) K)⁻¹ *
              (g : SpecialLinearGroup (Fin n) K)⁻¹) =
            θ g * ((θ h * (h : SpecialLinearGroup (Fin n) K)⁻¹) *
              (g : SpecialLinearGroup (Fin n) K)⁻¹) := by group
          _ = θ g * ((g : SpecialLinearGroup (Fin n) K)⁻¹ *
              (θ h * (h : SpecialLinearGroup (Fin n) K)⁻¹)) := by rw [hc]
          _ = θ g * (g : SpecialLinearGroup (Fin n) K)⁻¹ *
              (θ h * (h : SpecialLinearGroup (Fin n) K)⁻¹) := by group }
  have hcomm : ⁅N, N⁆ ≤ CatFactsSp4.fixOf θ := by
    rw [Subgroup.commutator_le]
    intro x hx y hy
    have h1 : τ ⁅(⟨x, hx⟩ : N), ⟨y, hy⟩⁆ = 1 := by
      rw [map_commutatorElement, commutatorElement_eq_one_iff_mul_comm]
      exact Subtype.ext (mem_center_iff.mp (τ ⟨y, hy⟩).2 _)
    have h2 := congrArg Subtype.val h1
    change θ ⁅x, y⁆ * ⁅x, y⁆⁻¹ = 1 at h2
    rw [CatFactsSp4.mem_fixOf]
    exact mul_inv_eq_one.mp h2
  have hNM : N.map (proj n K) = M := map_comap_eq_self_of_surjective (proj_surjective n K) M
  calc M = ⁅M, M⁆ := hM.symm
    _ = (⁅N, N⁆).map (proj n K) := by rw [Subgroup.map_commutator, hNM]
    _ ≤ (CatFactsSp4.fixOf θ).map (proj n K) := Subgroup.map_mono hcomm

theorem perfect_le_map_commutator {C : Subgroup (SpecialLinearGroup (Fin n) K)}
    {M : Subgroup (projectiveSL n K)} (hM : ⁅M, M⁆ = M) (hMC : M ≤ C.map (proj n K)) :
    M ≤ (⁅C, C⁆).map (proj n K) := by
  rw [Subgroup.map_commutator, ← hM]
  exact Subgroup.commutator_mono hMC hMC

end Twist

theorem derivedSeries_three_le_projectiveSL_n {n : ℕ} (hn : 3 ≤ n) {k : Type*} [Field k]
    [Finite k] :
    derivedSeries (MulAut (projectiveSL n k)) 3 ≤
      (MulAut.conj : projectiveSL n k →* MulAut (projectiveSL n k)).range := by
  have hR := (automorphism_generation (K := k) (n := n) hn).1
  have h := (standard_outer_quotients (K := k) (n := n)).2.2.2.2.2.2.2.2.2
  rw [hR] at h
  simpa only [derivedSeries_succ, derivedSeries_zero] using h

theorem v2_cube_sub_one {q : ℕ} (hq : Odd q) (hq3 : 3 ≤ q) :
    padicValNat 2 (q ^ 3 - 1) = padicValNat 2 (q - 1) := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have h1 : q ^ 3 - 1 = (q - 1) * (q ^ 2 + q + 1) := by
    have : 1 ≤ q := by omega
    zify [this, Nat.one_le_pow 3 q (by omega)]
    ring
  have hodd : Odd (q ^ 2 + q + 1) := by
    obtain ⟨k, rfl⟩ := hq
    exact ⟨2 * k * k + 3 * k + 1, by ring⟩
  rw [h1, padicValNat.mul (by omega) (by positivity), v2_odd hodd, add_zero]

theorem ordA_three_mul (q : ℕ) (hq : 1 ≤ q) :
    Open.ordA 3 q * Nat.gcd 4 (q - 1) = q ^ 6 * ((q ^ 2 - 1) * (q ^ 3 - 1) * (q ^ 4 - 1)) := by
  have hdvd : Nat.gcd 4 (q - 1) ∣ q ^ 6 * ((q ^ 2 - 1) * (q ^ 3 - 1) * (q ^ 4 - 1)) := by
    refine (Nat.gcd_dvd_right 4 (q - 1)).trans (Dvd.dvd.mul_left ?_ _)
    refine Dvd.dvd.mul_right (Dvd.dvd.mul_right ?_ _) _
    have : q ^ 2 - 1 = (q - 1) * (q + 1) := by
      zify [hq, Nat.one_le_pow 2 q hq]
      ring
    rw [this]
    exact Dvd.intro _ rfl
  have hprod : ∏ i ∈ Finset.Icc 2 (3 + 1), (q ^ i - 1) =
      (q ^ 2 - 1) * (q ^ 3 - 1) * (q ^ 4 - 1) := by
    rw [show Finset.Icc 2 (3 + 1) = {2, 3, 4} by rfl, Finset.prod_insert (by decide),
      Finset.prod_pair (by decide), mul_assoc]
  rw [Open.ordA, show 3 * (3 + 1) / 2 = 6 by rfl, hprod]
  exact Nat.div_mul_cancel hdvd

theorem v2_ordA_three {q : ℕ} (hq : Odd q) (hq3 : 3 ≤ q) (h8 : q % 8 ≠ 1) :
    padicValNat 2 (Open.ordA 3 q) = 2 * padicValNat 2 (q ^ 2 - 1) + 1 := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hx := ordA_three_mul q (by omega)
  have h2 : q ^ 2 - 1 ≠ 0 := by
    have : 9 ≤ q ^ 2 := by nlinarith
    omega
  have h3 : q ^ 3 - 1 ≠ 0 := by
    have : 27 ≤ q ^ 3 := by
      calc 27 = 3 ^ 3 := by norm_num
        _ ≤ q ^ 3 := Nat.pow_le_pow_left hq3 3
    omega
  have h4 : q ^ 4 - 1 ≠ 0 := by
    have : 81 ≤ q ^ 4 := by
      calc 81 = 3 ^ 4 := by norm_num
        _ ≤ q ^ 4 := Nat.pow_le_pow_left hq3 4
    omega
  have hg0 : Nat.gcd 4 (q - 1) ≠ 0 := Nat.gcd_ne_zero_left (by norm_num)
  have hx0 : Open.ordA 3 q ≠ 0 := by
    intro h
    rw [h, zero_mul] at hx
    exact Nat.mul_ne_zero (by positivity) (Nat.mul_ne_zero (Nat.mul_ne_zero h2 h3) h4) hx.symm
  have hv := congrArg (padicValNat 2) hx
  rw [padicValNat.mul hx0 hg0, padicValNat.mul (by positivity)
      (Nat.mul_ne_zero (Nat.mul_ne_zero h2 h3) h4), padicValNat.pow, v2_odd hq, mul_zero,
    zero_add, padicValNat.mul (Nat.mul_ne_zero h2 h3) h4, padicValNat.mul h2 h3,
    v2_cube_sub_one hq hq3, v2_four hq hq3] at hv
  obtain ⟨k, rfl⟩ := hq
  rcases (show k % 2 = 1 ∨ k % 4 = 2 by omega) with hk | hk
  ·
    obtain ⟨j, rfl⟩ : ∃ j, k = 2 * j + 1 := ⟨k / 2, by omega⟩
    have hq1 : 2 * (2 * j + 1) + 1 - 1 = 2 * (2 * j + 1) := by omega
    have hg : Nat.gcd 4 (2 * (2 * j + 1) + 1 - 1) = 2 := by
      rw [hq1, show (4 : ℕ) = 2 * 2 by rfl, Nat.gcd_mul_left,
        Nat.Coprime.gcd_eq_one (Nat.coprime_two_left.mpr ⟨j, rfl⟩)]
    have hv1 : padicValNat 2 (2 * (2 * j + 1) + 1 - 1) = 1 := by
      rw [hq1, padicValNat.mul (by norm_num) (by omega), padicValNat.self (by norm_num),
        v2_odd ⟨j, rfl⟩]
    rw [hg, hv1, padicValNat.self (by norm_num)] at hv
    omega
  ·
    obtain ⟨j, rfl⟩ : ∃ j, k = 4 * j + 2 := ⟨k / 4, by omega⟩
    have h4' : padicValNat 2 4 = 2 := by
      rw [show (4 : ℕ) = 2 ^ 2 by rfl, padicValNat.prime_pow]
    have hq1 : 2 * (4 * j + 2) + 1 - 1 = 4 * (2 * j + 1) := by omega
    have hg : Nat.gcd 4 (2 * (4 * j + 2) + 1 - 1) = 4 := by
      rw [hq1]
      exact Nat.gcd_mul_right_right _ 4
    have hv1 : padicValNat 2 (2 * (4 * j + 2) + 1 - 1) = 2 := by
      rw [hq1, padicValNat.mul (by norm_num) (by omega), v2_odd ⟨j, rfl⟩, h4']
    have hn : padicValNat 2 ((2 * (4 * j + 2) + 1) ^ 2 - 1) = 3 := by
      rw [show (2 * (4 * j + 2) + 1) ^ 2 - 1 = 8 * ((2 * j + 1) * (4 * j + 3)) by ring_nf; omega,
        padicValNat.mul (by norm_num) (by positivity), show (8 : ℕ) = 2 ^ 3 by rfl,
        padicValNat.prime_pow,
        v2_odd (q := (2 * j + 1) * (4 * j + 3)) (Nat.odd_mul.mpr ⟨⟨j, rfl⟩, ⟨2 * j + 1, by ring⟩⟩)]
    rw [hg, hv1, h4', hn] at hv
    rw [hn]
    omega

end CFSG.ComponentClassification.GSThmB.P211
