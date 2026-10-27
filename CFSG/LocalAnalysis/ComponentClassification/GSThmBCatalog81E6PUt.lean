module

public import CFSG.LocalAnalysis.ComponentClassification.GSThmBCatalog81E6PSp

public section

namespace CFSG.ComponentClassification.GSThmB.P211

open CFSG Subgroup
open scoped commutatorElement

section Twist

variable {G Q : Type*} [Group G] [Group Q] {π : G →* Q}

theorem perfect_le_map_eqLocus (hπ : Function.Surjective π) (hker : π.ker ≤ center G)
    (ψ : G →* G) {β : Q →* Q} (hβ : ∀ g, β (π g) = π (ψ g)) {M : Subgroup Q} (hM : ⁅M, M⁆ = M)
    (hfix : ∀ x ∈ M, β x = x) : M ≤ (ψ.eqLocus (MonoidHom.id G)).map π := by
  set N := M.comap π with hN
  have hc : ∀ g : N, ψ g * (g : G)⁻¹ ∈ center G := fun g => by
    apply hker
    rw [MonoidHom.mem_ker, map_mul, map_inv, ← hβ, hfix _ g.2, mul_inv_cancel]
  let τ : N →* center G :=
    { toFun := fun g => ⟨ψ g * (g : G)⁻¹, hc g⟩
      map_one' := Subtype.ext (by simp)
      map_mul' := fun g g' => by
        apply Subtype.ext
        have hcg := mem_center_iff.mp (hc g') (g : G)⁻¹
        simp only [Subgroup.coe_mul, map_mul, _root_.mul_inv_rev]
        calc ψ g * ψ g' * ((g' : G)⁻¹ * (g : G)⁻¹) =
            ψ g * ((ψ g' * (g' : G)⁻¹) * (g : G)⁻¹) := by group
          _ = ψ g * ((g : G)⁻¹ * (ψ g' * (g' : G)⁻¹)) := by rw [hcg]
          _ = ψ g * (g : G)⁻¹ * (ψ g' * (g' : G)⁻¹) := by group }
  have hcomm : ⁅N, N⁆ ≤ ψ.eqLocus (MonoidHom.id G) := by
    rw [Subgroup.commutator_le]
    intro x hx y hy
    have h1 : τ ⁅(⟨x, hx⟩ : N), ⟨y, hy⟩⁆ = 1 := by
      rw [map_commutatorElement, commutatorElement_eq_one_iff_mul_comm]
      exact Subtype.ext (mem_center_iff.mp (τ ⟨y, hy⟩).2 _)
    have h2 := congrArg Subtype.val h1
    change ψ ⁅x, y⁆ * ⁅x, y⁆⁻¹ = 1 at h2
    exact mul_inv_eq_one.mp h2
  have hNM : N.map π = M := map_comap_eq_self_of_surjective hπ M
  calc M = ⁅M, M⁆ := hM.symm
    _ = (⁅N, N⁆).map π := by rw [Subgroup.map_commutator, hNM]
    _ ≤ (ψ.eqLocus (MonoidHom.id G)).map π := Subgroup.map_mono hcomm

theorem two_mul_card_map_dvd {R : Subgroup G} {z : G} (hzR : z ∈ R) (hz : π z = 1)
    (hz2 : orderOf z = 2) : 2 * Nat.card (R.map π) ∣ Nat.card R := by
  set φ := π.comp R.subtype with hφ
  have hrange : φ.range = R.map π := by
    rw [hφ, MonoidHom.range_comp, Subgroup.range_subtype]
  have hx : (⟨z, hzR⟩ : R) ∈ φ.ker := by
    rw [MonoidHom.mem_ker, hφ, MonoidHom.comp_apply, Subgroup.coe_subtype]
    exact hz
  have ho : orderOf (⟨⟨z, hzR⟩, hx⟩ : φ.ker) = 2 := by
    rw [← Subgroup.orderOf_coe, ← Subgroup.orderOf_coe]
    exact hz2
  have h2k : 2 ∣ Nat.card φ.ker := ho ▸ orderOf_dvd_natCard _
  rw [← Subgroup.card_ker_mul_card_range φ, hrange]
  exact Nat.mul_dvd_mul h2k dvd_rfl

end Twist

theorem ordTwistedA_three_mul (q : ℕ) (hq : 1 ≤ q) :
    Open.ordTwistedA 3 q * Nat.gcd 4 (q + 1) =
      q ^ 6 * ((q ^ 2 - 1) * (q ^ 3 + 1) * (q ^ 4 - 1)) := by
  have h2 : 1 ≤ q ^ 2 := Nat.one_le_pow _ _ hq
  have h4 : 1 ≤ q ^ 4 := Nat.one_le_pow _ _ hq
  have hprod : ∏ i ∈ Finset.Icc 2 (3 + 1), ((q : ℤ) ^ i - (-1 : ℤ) ^ i).toNat =
      (q ^ 2 - 1) * (q ^ 3 + 1) * (q ^ 4 - 1) := by
    rw [show Finset.Icc 2 (3 + 1) = {2, 3, 4} by rfl, Finset.prod_insert (by decide),
      Finset.prod_pair (by decide), ← mul_assoc]
    have e2 : ((q : ℤ) ^ 2 - (-1 : ℤ) ^ 2).toNat = q ^ 2 - 1 := by
      rw [show ((q : ℤ) ^ 2 - (-1 : ℤ) ^ 2) = ((q ^ 2 - 1 : ℕ) : ℤ) by push_cast [h2]; ring,
        Int.toNat_natCast]
    have e3 : ((q : ℤ) ^ 3 - (-1 : ℤ) ^ 3).toNat = q ^ 3 + 1 := by
      rw [show ((q : ℤ) ^ 3 - (-1 : ℤ) ^ 3) = ((q ^ 3 + 1 : ℕ) : ℤ) by push_cast; ring,
        Int.toNat_natCast]
    have e4 : ((q : ℤ) ^ 4 - (-1 : ℤ) ^ 4).toNat = q ^ 4 - 1 := by
      rw [show ((q : ℤ) ^ 4 - (-1 : ℤ) ^ 4) = ((q ^ 4 - 1 : ℕ) : ℤ) by push_cast [h4]; ring,
        Int.toNat_natCast]
    rw [e2, e3, e4]
  have hdvd : Nat.gcd 4 (q + 1) ∣ q ^ 6 * ((q ^ 2 - 1) * (q ^ 3 + 1) * (q ^ 4 - 1)) := by
    refine (Nat.gcd_dvd_right 4 (q + 1)).trans (Dvd.dvd.mul_left ?_ _)
    refine Dvd.dvd.mul_right (Dvd.dvd.mul_left ?_ _) _
    exact ⟨q ^ 2 - q + 1, by
      have : q ≤ q ^ 2 := Nat.le_self_pow (by norm_num) q
      zify [this]
      ring⟩
  rw [Open.ordTwistedA, show 3 * (3 + 1) / 2 = 6 by rfl, show (3 + 1 : ℕ) = 3 + 1 from rfl,
    hprod, show (3 : ℕ) + 1 = 4 from rfl]
  exact Nat.div_mul_cancel hdvd

theorem v2_cube_add_one {q : ℕ} (hq : Odd q) :
    padicValNat 2 (q ^ 3 + 1) = padicValNat 2 (q + 1) := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hq1 : q ≤ q ^ 2 := Nat.le_self_pow (by norm_num) q
  have h1 : q ^ 3 + 1 = (q + 1) * (q ^ 2 - q + 1) := by
    zify [hq1]
    ring
  have hodd : Odd (q ^ 2 - q + 1) := by
    obtain ⟨k, rfl⟩ := hq
    refine ⟨2 * k * k + k, ?_⟩
    have : 2 * k + 1 ≤ (2 * k + 1) ^ 2 := Nat.le_self_pow (by norm_num) _
    zify [this]
    ring
  rw [h1, padicValNat.mul (by omega) (by omega), v2_odd hodd, add_zero]

theorem v2_ordTwistedA_three {q : ℕ} (hq : Odd q) (hq3 : 3 ≤ q) (h8 : q % 8 ≠ 7) :
    padicValNat 2 (Open.ordTwistedA 3 q) = 2 * padicValNat 2 (q ^ 2 - 1) + 1 := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hx := ordTwistedA_three_mul q (by omega)
  have h2 : q ^ 2 - 1 ≠ 0 := by
    have : 9 ≤ q ^ 2 := by nlinarith
    omega
  have h3 : q ^ 3 + 1 ≠ 0 := by positivity
  have h4 : q ^ 4 - 1 ≠ 0 := by
    have : 81 ≤ q ^ 4 := by
      calc 81 = 3 ^ 4 := by norm_num
        _ ≤ q ^ 4 := Nat.pow_le_pow_left hq3 4
    omega
  have hg0 : Nat.gcd 4 (q + 1) ≠ 0 := Nat.gcd_ne_zero_left (by norm_num)
  have hx0 : Open.ordTwistedA 3 q ≠ 0 := by
    intro h
    rw [h, zero_mul] at hx
    exact Nat.mul_ne_zero (by positivity) (Nat.mul_ne_zero (Nat.mul_ne_zero h2 h3) h4) hx.symm
  have hv := congrArg (padicValNat 2) hx
  rw [padicValNat.mul hx0 hg0, padicValNat.mul (by positivity)
      (Nat.mul_ne_zero (Nat.mul_ne_zero h2 h3) h4), padicValNat.pow, v2_odd hq, mul_zero,
    zero_add, padicValNat.mul (Nat.mul_ne_zero h2 h3) h4, padicValNat.mul h2 h3,
    v2_cube_add_one hq, v2_four hq hq3] at hv
  obtain ⟨k, rfl⟩ := hq
  rcases (show k % 2 = 0 ∨ k % 4 = 1 by omega) with hk | hk
  ·
    obtain ⟨j, rfl⟩ : ∃ j, k = 2 * j := ⟨k / 2, by omega⟩
    have hq1 : 2 * (2 * j) + 1 + 1 = 2 * (2 * j + 1) := by ring
    have hg : Nat.gcd 4 (2 * (2 * j) + 1 + 1) = 2 := by
      rw [hq1, show (4 : ℕ) = 2 * 2 by rfl, Nat.gcd_mul_left,
        Nat.Coprime.gcd_eq_one (Nat.coprime_two_left.mpr ⟨j, rfl⟩)]
    have hv1 : padicValNat 2 (2 * (2 * j) + 1 + 1) = 1 := by
      rw [hq1, padicValNat.mul (by norm_num) (by omega), padicValNat.self (by norm_num),
        v2_odd ⟨j, rfl⟩]
    rw [hg, hv1, padicValNat.self (by norm_num)] at hv
    omega
  ·
    obtain ⟨j, rfl⟩ : ∃ j, k = 4 * j + 1 := ⟨k / 4, by omega⟩
    have h4' : padicValNat 2 4 = 2 := by
      rw [show (4 : ℕ) = 2 ^ 2 by rfl, padicValNat.prime_pow]
    have hq1 : 2 * (4 * j + 1) + 1 + 1 = 4 * (2 * j + 1) := by ring
    have hg : Nat.gcd 4 (2 * (4 * j + 1) + 1 + 1) = 4 := by
      rw [hq1]
      exact Nat.gcd_mul_right_right _ 4
    have hv1 : padicValNat 2 (2 * (4 * j + 1) + 1 + 1) = 2 := by
      rw [hq1, padicValNat.mul (by norm_num) (by omega), v2_odd ⟨j, rfl⟩, h4']
    rw [hg, hv1, h4'] at hv
    omega

end CFSG.ComponentClassification.GSThmB.P211
