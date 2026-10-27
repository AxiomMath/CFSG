module

public import CFSG.LocalAnalysis.OddStandard.Solomon75Sec5QGrp
public import CFSG.Adapters.ProjectiveSpecialLinear
public import CFSG.Assembly.ComponentTypeDefs
public import CFSG.GH74.GLS.Basic
public import CFSG.LocalAnalysis.OddStandard.Solomon75Basic
public import CFSG.LocalAnalysis.RankTwoShapes.UnitaryFour.Bridge

public section

namespace CFSG.OddStandard.Solomon75

open Equiv Equiv.Perm Subgroup CFSG CFSG.GH74.GLS

open scoped commutatorElement

section Sup

variable {X : Type} [Group X]

theorem exists_mul_of_mem_sup_of_le_normalizer {H K : Subgroup X}
    (hK : K ≤ normalizer (H : Set X)) {x : X} (hx : x ∈ H ⊔ K) :
    ∃ h ∈ H, ∃ k ∈ K, x = h * k := by
  let T : Subgroup X :=
    { carrier := {x | ∃ h ∈ H, ∃ k ∈ K, x = h * k}
      one_mem' := ⟨1, one_mem _, 1, one_mem _, by simp⟩
      mul_mem' := by
        rintro _ _ ⟨h, hh, k, hk, rfl⟩ ⟨h', hh', k', hk', rfl⟩
        refine ⟨h * (k * h' * k⁻¹), mul_mem hh ((Subgroup.mem_normalizer_iff.1 (hK hk) h').1 hh'),
          k * k', mul_mem hk hk', ?_⟩
        group
      inv_mem' := by
        rintro _ ⟨h, hh, k, hk, rfl⟩
        refine ⟨k⁻¹ * h⁻¹ * k, ?_, k⁻¹, inv_mem hk, by group⟩
        have := (Subgroup.mem_normalizer_iff.1 (hK (inv_mem hk)) h⁻¹).1 (inv_mem hh)
        simpa using this }
  have hHT : H ≤ T := fun h hh => ⟨h, hh, 1, one_mem _, by simp⟩
  have hKT : K ≤ T := fun k hk => ⟨1, one_mem _, k, hk, by simp⟩
  exact (sup_le hHT hKT) hx

theorem comm_mem_oddCoreOf_of_sup {r s : X} (hrs : r * s = s * r)
    (hsup : centralizer ({r} : Set X) = oddCoreOf (centralizer ({r} : Set X)) ⊔
      (centralizer ({s} : Set X) ⊓ centralizer ({r} : Set X))) :
    ∀ c ∈ centralizer ({r} : Set X), ⁅c, s⁆ ∈ oddCoreOf (centralizer ({r} : Set X)) := by
  intro c hc
  have hsr : s ∈ centralizer ({r} : Set X) := Subgroup.mem_centralizer_singleton_iff.2 hrs.symm
  have hK : centralizer ({s} : Set X) ⊓ centralizer ({r} : Set X) ≤
      normalizer (oddCoreOf (centralizer ({r} : Set X)) : Set X) :=
    inf_le_right.trans fun y hy => le_normalizer_oddCoreOf _ hy
  rw [hsup] at hc
  obtain ⟨o, ho, y, hy, rfl⟩ := exists_mul_of_mem_sup_of_le_normalizer hK hc
  have hys : y * s = s * y := Subgroup.mem_centralizer_singleton_iff.1 hy.1
  have e1 : ⁅o * y, s⁆ = o * (s * o⁻¹ * s⁻¹) := by
    simp only [commutatorElement_def]
    calc o * y * s * (o * y)⁻¹ * s⁻¹ = o * (y * s) * y⁻¹ * o⁻¹ * s⁻¹ := by group
      _ = o * (s * y) * y⁻¹ * o⁻¹ * s⁻¹ := by rw [hys]
      _ = o * (s * o⁻¹ * s⁻¹) := by group
  rw [e1]
  exact mul_mem ho ((Subgroup.mem_normalizer_iff.1 (le_normalizer_oddCoreOf _ hsr) o⁻¹).1
    (inv_mem ho))

end Sup

section Pow

variable {G : Type*} [Group G]

theorem exists_involution_pow {r : G} {j : ℕ} (hj : r ^ (2 ^ j) = 1) (hr : r ≠ 1) :
    ∃ i : ℕ, orderOf (r ^ (2 ^ i)) = 2 := by
  have hfact : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  obtain ⟨m, -, hm⟩ := (Nat.dvd_prime_pow Nat.prime_two).1 (orderOf_dvd_of_pow_eq_one hj)
  have hm1 : 1 ≤ m := by
    by_contra h0
    have : m = 0 := by omega
    rw [this, pow_zero, orderOf_eq_one_iff] at hm
    exact hr hm
  refine ⟨m - 1, ?_⟩
  rw [orderOf_pow_of_dvd (by positivity) (by rw [hm]; exact pow_dvd_pow 2 (by omega)), hm]
  have : 2 ^ m = 2 ^ (m - 1) * 2 := by
    rw [← pow_succ]
    congr 1
    omega
  rw [this, Nat.mul_div_cancel_left _ (by positivity)]

end Pow

theorem map_mem_zpowers {G K : Type*} [Group G] [Group K] (f : G →* K) {y w : G}
    (hw : w ∈ zpowers y) : f w ∈ zpowers (f y) := by
  obtain ⟨k, rfl⟩ := Subgroup.mem_zpowers_iff.1 hw
  rw [map_zpow]
  exact Subgroup.zpow_mem_zpowers _ _

section Lift

variable {G K : Type} [Group G] [Finite G] [Group K]

theorem exists_involution_lift (f : G →* K) {R : Subgroup G}
    (hker : ∀ r ∈ R, f r = 1 → ∀ j : ℕ, r ^ (2 ^ j) = 1 → r = 1) {r₀ : G} (hr₀ : r₀ ∈ R)
    (ht2 : f r₀ * f r₀ = 1) (ht1 : f r₀ ≠ 1) :
    ∃ r ∈ R, r * r = 1 ∧ r ≠ 1 ∧ f r = f r₀ := by
  obtain ⟨u, v, hu, hv, huv, ⟨j, hj⟩, hvodd⟩ := exists_twoPart r₀
  have huR : u ∈ R := by
    obtain ⟨k, rfl⟩ := Subgroup.mem_zpowers_iff.1 hu
    exact zpow_mem hr₀ k
  have hfv : f v = 1 := by
    have hv' := map_mem_zpowers f hv
    obtain ⟨k, hk⟩ := Subgroup.mem_zpowers_iff.1 hv'
    have hsq : f v * f v = 1 := by
      rw [← hk, ← (Commute.refl (f r₀)).mul_zpow, ht2, one_zpow]
    have h2 : orderOf (f v) ∣ 2 := orderOf_dvd_of_pow_eq_one (by rw [sq]; exact hsq)
    have h3 : Odd (orderOf (f v)) := Odd.of_dvd_nat hvodd (orderOf_map_dvd f v)
    rcases (Nat.dvd_prime Nat.prime_two).1 h2 with h4 | h4
    · exact orderOf_eq_one_iff.1 h4
    · rw [h4] at h3
      exact absurd h3 (by decide)
  have hfu : f u = f r₀ := by
    have h1 : f r₀ = f u * f v := by rw [← map_mul, ← huv]
    rw [h1, hfv, mul_one]
  have huu : u * u = 1 := by
    refine hker (u * u) (mul_mem huR huR) ?_ (j + 1) ?_
    · rw [map_mul, hfu, ht2]
    · have : (u * u) ^ 2 ^ (j + 1) = (u ^ 2 ^ j) ^ 4 := by
        rw [← sq, ← pow_mul, ← pow_mul]
        congr 1
        ring
      rw [this, hj, one_pow]
  refine ⟨u, huR, huu, ?_, hfu⟩
  intro hu1
  rw [hu1, map_one] at hfu
  exact ht1 hfu.symm

theorem exists_odd_pow_lift (f : G →* K) (y : G) (hodd : Odd (orderOf (f y))) :
    ∃ v ∈ zpowers y, Odd (orderOf v) ∧ f v = f y := by
  obtain ⟨u, v, hu, hv, huv, ⟨j, hj⟩, hvodd⟩ := exists_twoPart y
  have hfu : f u = 1 := by
    have hu' := map_mem_zpowers f hu
    obtain ⟨k, hk⟩ := Subgroup.mem_zpowers_iff.1 hu'
    have h1 : orderOf (f u) ∣ orderOf (f y) := by
      refine orderOf_dvd_of_pow_eq_one ?_
      rw [← hk, ← zpow_natCast, ← zpow_mul, mul_comm, zpow_mul, zpow_natCast, pow_orderOf_eq_one,
        one_zpow]
    have h2 : orderOf (f u) ∣ 2 ^ j := by
      refine orderOf_dvd_of_pow_eq_one ?_
      rw [← map_pow, hj, map_one]
    obtain ⟨m, -, hm⟩ := (Nat.dvd_prime_pow Nat.prime_two).1 h2
    have h3 : Odd (orderOf (f u)) := Odd.of_dvd_nat hodd h1
    by_cases hm0 : m = 0
    · rw [hm0, pow_zero] at hm
      exact orderOf_eq_one_iff.1 hm
    · rw [hm] at h3
      exact absurd h3 (by simp [Nat.not_odd_iff_even, Nat.even_pow, hm0])
  refine ⟨v, hv, hvodd, ?_⟩
  have h1 : f y = f u * f v := by rw [← map_mul, ← huv]
  rw [h1, hfu, one_mul]

end Lift

end CFSG.OddStandard.Solomon75
