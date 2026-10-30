module

public import CFSG.LocalAnalysis.OddStandard.SmallF3.Omega.Sec10KS1
public import CFSG.LocalAnalysis.OddStandard.SmallF3.Omega.Sec10KS2a

public section

namespace CFSG.OddStandard.SmallF3.Omega

open Subgroup CFSG.Blueprint

variable {G : Type} [Group G]

private theorem mem_twoCoreIn_of_mem_pCore {X : Subgroup G} {x : ↥X}
    (hx : x ∈ CFSG.pCore 2 ↥X) : (x : G) ∈ twoCoreIn X := by
  unfold twoCoreIn CFSG.inSubgroup
  exact Subgroup.mem_map.mpr ⟨x, hx, rfl⟩

private theorem mem_pCore_of_map_mem_pCore {X : Subgroup G} (e : ↥X ≃* SL23) {x : ↥X}
    (hx : e x ∈ CFSG.pCore 2 SL23) : x ∈ CFSG.pCore 2 ↥X := by
  rw [← CFSG.pCore_map_iso 2 e] at hx
  obtain ⟨y, hy, hye⟩ := Subgroup.mem_map.mp hx
  have hyx : y = x := e.injective hye
  rwa [hyx] at hy

private theorem map_w_eq_neg_one {X : Subgroup G} (e : ↥X ≃* SL23) {w : G} (hw : w ∈ X)
    (hw2 : orderOf w = 2) : e ⟨w, hw⟩ = -1 := by
  have hsq : (⟨w, hw⟩ : ↥X) * ⟨w, hw⟩ = 1 := by
    apply Subtype.ext
    change (w : G) * w = 1
    have h := pow_orderOf_eq_one w
    rw [hw2] at h
    simpa [pow_two] using h
  have hsq' : e ⟨w, hw⟩ * e ⟨w, hw⟩ = 1 := by
    rw [← map_mul, hsq, map_one]
  rcases sl23_unique_involution _ hsq' with h | h
  · exfalso
    have hw1 : (⟨w, hw⟩ : ↥X) = 1 := by
      apply e.injective
      rw [h, map_one]
    have hwG : w = 1 := by simpa using congrArg Subtype.val hw1
    have : orderOf w = 1 := by rw [hwG]; exact orderOf_one
    omega
  · exact h

private theorem mem_pCore_of_pow_four {y : SL23} (hy : y ^ 4 = 1) :
    y ∈ CFSG.pCore 2 SL23 := by
  rw [sl23_pCore_eq_Q8, mem_sl23Q8]
  exact hy

private theorem symm_mem_twoCoreIn_of_pow4 {X : Subgroup G} (e : ↥X ≃* SL23) {y : SL23}
    (hy : y ^ 4 = 1) : ((e.symm y : ↥X) : G) ∈ twoCoreIn X :=
  mem_twoCoreIn_of_mem_pCore
    (mem_pCore_of_map_mem_pCore e (by
      rw [e.apply_symm_apply]
      exact mem_pCore_of_pow_four hy))

private theorem orderOf_dvd_eight_of_dvd_pow24 {o m : ℕ} (h1 : o ∣ 2 ^ m) (h2 : o ∣ 24) :
    o ∣ 8 := by
  obtain ⟨k, -, hk⟩ := (Nat.dvd_prime_pow Nat.prime_two).mp h1
  have h2' : 2 ^ k ∣ 24 := hk ▸ h2
  have hk3 : k ≤ 3 := by
    by_contra h
    push Not at h
    have h16 : 2 ^ 4 ∣ 24 := (pow_dvd_pow 2 (by omega)).trans h2'
    norm_num at h16
  rw [hk, show (8 : ℕ) = 2 ^ 3 by norm_num]
  exact pow_dvd_pow 2 hk3

theorem sec10T_two_elem_Q1 [Finite G] (hP5 : Asc82FactPockets5) (hC5 : Asc82FactCentZ5)
    {t : G} {L S : Subgroup G} {z : G} {K1 K2 : Subgroup G} (hpsp : IsPSp43 L)
    (hctx : Sec10Ctx G t L S z K1 K2) {a : G} (ha : a ∈ K1) (ha2 : ∃ m : ℕ, a ^ (2 ^ m) = 1) :
    a ∈ twoCoreIn K1 := by
  obtain ⟨e⟩ := (sec10KS_equiv hP5 hC5 hpsp hctx).1
  obtain ⟨m, hm⟩ := ha2
  have hpow : (e ⟨a, ha⟩) ^ (2 ^ m) = 1 := by
    have helem : (⟨a, ha⟩ : ↥K1) ^ (2 ^ m) = 1 := by
      apply Subtype.ext
      change a ^ (2 ^ m) = (1 : G)
      exact hm
    rw [← map_pow, helem, map_one]
  have hdvd_pow : orderOf (e ⟨a, ha⟩) ∣ 2 ^ m :=
    orderOf_dvd_iff_pow_eq_one.mpr hpow
  have hdvd_card : orderOf (e ⟨a, ha⟩) ∣ 24 := by
    have h24 : Fintype.card SL23 = 24 := by decide
    simpa [h24] using orderOf_dvd_natCard (e ⟨a, ha⟩)
  have h8 : orderOf (e ⟨a, ha⟩) ∣ 8 :=
    orderOf_dvd_eight_of_dvd_pow24 hdvd_pow hdvd_card
  have h4 : (e ⟨a, ha⟩) ^ 4 = 1 :=
    (by decide : ∀ y : SL23, y ^ 8 = 1 → y ^ 4 = 1) _ (orderOf_dvd_iff_pow_eq_one.mp h8)
  exact mem_twoCoreIn_of_mem_pCore
    (mem_pCore_of_map_mem_pCore e (mem_pCore_of_pow_four h4))

theorem sec10T_exists_comm3 [Finite G] (hP5 : Asc82FactPockets5) (hC5 : Asc82FactCentZ5)
    {t : G} {L S : Subgroup G} {z : G} {K1 K2 : Subgroup G} (hpsp : IsPSp43 L)
    (hctx : Sec10Ctx G t L S z K1 K2) :
    ∃ k ∈ K1, Odd (orderOf k) ∧ ∃ g0 ∈ twoCoreIn K1, k * g0 * k⁻¹ * g0⁻¹ ∉ zpowers z := by
  obtain ⟨e⟩ := (sec10KS_equiv hP5 hC5 hpsp hctx).1
  obtain ⟨c, i, hc3, hc1, hi4, hci1, hcineg1⟩ :=
    (by decide : ∃ c i : SL23, c ^ 3 = 1 ∧ c ≠ 1 ∧ i ^ 4 = 1 ∧
      c * i * c⁻¹ * i⁻¹ ≠ 1 ∧ c * i * c⁻¹ * i⁻¹ ≠ -1)
  haveI : Fact (Nat.Prime 3) := ⟨by norm_num⟩
  have horder_c : orderOf c = 3 := orderOf_eq_prime hc3 hc1
  let k : ↥K1 := e.symm c
  let g0 : ↥K1 := e.symm i
  have hk_order_sub : orderOf k = orderOf c := by
    rw [← MulEquiv.orderOf_eq e k]
    simp [k]
  have hk_order : orderOf (k : G) = 3 := by
    rw [Subgroup.orderOf_coe, hk_order_sub, horder_c]
  have hk_odd : Odd (orderOf (k : G)) := by rw [hk_order]; norm_num
  have hg0Q : (g0 : G) ∈ twoCoreIn K1 := symm_mem_twoCoreIn_of_pow4 e hi4
  refine ⟨(k : G), k.2, hk_odd, (g0 : G), hg0Q, ?_⟩
  intro hcomm
  let w : ↥K1 := k * g0 * k⁻¹ * g0⁻¹
  have hwcoeeq : (w : G) = (k : G) * (g0 : G) * (k : G)⁻¹ * (g0 : G)⁻¹ := by simp [w]
  have hcommw : (w : G) ∈ zpowers z := by rw [hwcoeeq]; exact hcomm
  obtain ⟨n, hn⟩ := Subgroup.mem_zpowers_iff.mp hcommw
  have hzK1 : z ∈ K1 := hctx.pocket1.1
  have hw_eq : w = (⟨z, hzK1⟩ : ↥K1) ^ n := by
    apply Subtype.ext
    simpa using hn.symm
  have hew : e w = (-1 : SL23) ^ n := by
    rw [hw_eq]
    simp only [map_zpow, map_w_eq_neg_one e hzK1 hctx.toSec10Z.pocket.1]
  have hew_sq : e w * e w = 1 := by
    rw [hew, ← zpow_add, show n + n = 2 * n by ring, zpow_mul, zpow_two]
    have hnn : (-1 : SL23) * (-1) = 1 := by decide
    rw [hnn]
    simp
  have hew_val : e w = c * i * c⁻¹ * i⁻¹ := by simp [w, k, g0]
  rcases sl23_unique_involution (e w) hew_sq with h | h
  · exact hci1 (by rw [← hew_val, h])
  · exact hcineg1 (by rw [← hew_val, h])

end CFSG.OddStandard.SmallF3.Omega
