module

public import Mathlib.Data.ZMod.QuotientGroup
public import Mathlib.Tactic.Group
public import Mathlib.RingTheory.Coprime.Basic

public section

namespace CFSG.ClassicalInvolution.Q3.PhilipHall.Frame.TwinPerpV3

namespace Pf52Aut

variable {Y : Type} [Group Y]

theorem conj_zpow_fix {m x : Y} (hfix : m * x * m⁻¹ = x) (i : ℤ) :
    m * x ^ i * m⁻¹ = x ^ i := by
  rw [← conj_zpow, hfix]

theorem conj_inv_zpow_fix {m x : Y} (hfix : m * x * m⁻¹ = x) (i : ℤ) :
    m⁻¹ * x ^ i * m = x ^ i := by
  have h := conj_zpow_fix hfix i
  calc m⁻¹ * x ^ i * m = m⁻¹ * (m * x ^ i * m⁻¹) * m := by rw [h]
    _ = x ^ i := by group

theorem iter_conj {m x y : Y} (hfix : m * x * m⁻¹ = x) {i : ℤ}
    (hy : m * y * m⁻¹ = x ^ i * y) (j : ℕ) :
    m ^ j * y * (m ^ j)⁻¹ = x ^ (i * (j : ℤ)) * y := by
  induction j with
  | zero => simp
  | succ j ih =>
    have e : m ^ (j + 1) * y * (m ^ (j + 1))⁻¹ = m * (m ^ j * y * (m ^ j)⁻¹) * m⁻¹ := by
      rw [pow_succ', mul_inv_rev]; group
    rw [e, ih]
    have e2 : m * (x ^ (i * (j : ℤ)) * y) * m⁻¹
        = (m * x ^ (i * (j : ℤ)) * m⁻¹) * (m * y * m⁻¹) := by group
    rw [e2, conj_zpow_fix hfix, hy, ← mul_assoc, ← zpow_add]
    congr 2
    push_cast
    ring

end Pf52Aut

open Pf52Aut in
theorem centralizes_of_odd_fix {Y : Type} [Group Y] [Finite Y] {K : Subgroup Y} {m x : Y}
    (hK8 : Nat.card ↥K = 8) (hx : x ∈ K) (hx4 : orderOf x = 4)
    (hm : m ∈ Subgroup.normalizer (K : Set Y)) {k : ℕ} (hk : Odd k) (hmk : m ^ k = 1)
    (hfix : m * x * m⁻¹ = x) : ∀ y ∈ K, m * y = y * m := by
  intro y hyK
  have hcomm : ∀ z, m * z * m⁻¹ = z → m * z = z * m := fun z hz => by
    rw [mul_inv_eq_iff_eq_mul] at hz; exact hz
  by_cases hyH : y ∈ Subgroup.zpowers x
  · obtain ⟨a, rfl⟩ := Subgroup.mem_zpowers_iff.mp hyH
    exact hcomm _ (conj_zpow_fix hfix a)
  · have hHK : Subgroup.zpowers x ≤ K := (Subgroup.zpowers_le).mpr hx
    have hcard : Nat.card (Subgroup.zpowers x) = 4 := by rw [Nat.card_zpowers, hx4]
    have hrel : (Subgroup.zpowers x).relIndex K = 2 := by
      have h := Subgroup.relIndex_mul_card (H := Subgroup.zpowers x) (K := K)
      rw [inf_of_le_left hHK, hcard, hK8] at h
      omega
    obtain ⟨a, haK, ha⟩ := (Subgroup.relIndex_eq_two_iff.mp hrel)
    have hnotH : ∀ z ∈ K, z ∉ Subgroup.zpowers x → z * a ∈ Subgroup.zpowers x := by
      intro z hz hzH
      rcases ha z hz with ⟨h1, _⟩ | ⟨h1, h2⟩
      · exact h1
      · exact absurd h1 hzH
    have hyK' : m * y * m⁻¹ ∈ K := ((Subgroup.mem_set_normalizer_iff.mp hm) y).mp hyK
    have hσ : m * y * m⁻¹ ∉ Subgroup.zpowers x := by
      intro h
      obtain ⟨a', ha'⟩ := Subgroup.mem_zpowers_iff.mp h
      apply hyH
      have : y = m⁻¹ * (m * y * m⁻¹) * m := by group
      rw [this, ← ha', conj_inv_zpow_fix hfix]
      exact Subgroup.zpow_mem_zpowers x a'
    have h1 := hnotH y hyK hyH
    have h2 := hnotH _ hyK' hσ
    have h3 : (m * y * m⁻¹) * y⁻¹ ∈ Subgroup.zpowers x := by
      have := mul_mem h2 (inv_mem h1)
      simpa [mul_assoc] using this
    obtain ⟨i, hi⟩ := Subgroup.mem_zpowers_iff.mp h3
    have hy : m * y * m⁻¹ = x ^ i * y := by rw [hi]; group
    have hit := iter_conj hfix hy k
    rw [hmk] at hit
    simp only [inv_one, mul_one, one_mul] at hit
    have hxi : x ^ (i * (k : ℤ)) = 1 := by
      have := congrArg (fun t => t * y⁻¹) hit
      simpa using this.symm
    have hdvd : (4 : ℤ) ∣ i * (k : ℤ) := by
      have := (orderOf_dvd_iff_zpow_eq_one (x := x) (i := i * (k : ℤ))).mpr hxi
      rwa [hx4] at this
    obtain ⟨c, hc⟩ := hk
    have hcop : IsCoprime (4 : ℤ) (k : ℤ) := ⟨(c : ℤ) ^ 2, 1 - 2 * c, by rw [hc]; push_cast; ring⟩
    have h4i : (4 : ℤ) ∣ i := hcop.dvd_of_dvd_mul_right hdvd
    have hxi1 : x ^ i = 1 := by
      have := (orderOf_dvd_iff_zpow_eq_one (x := x) (i := i)).mp (by rw [hx4]; exact h4i)
      exact this
    exact hcomm y (by rw [hy, hxi1, one_mul])

theorem centralizes_of_odd_fix' {Y : Type} [Group Y] [Finite Y] {K : Subgroup Y} {m x : Y}
    (hK8 : Nat.card ↥K = 8) (hx : x ∈ K) (hx4 : orderOf x = 4)
    (hm : m ∈ Subgroup.normalizer (K : Set Y)) (hmo : Odd (orderOf m))
    (hfix : m * x * m⁻¹ = x) : ∀ y ∈ K, m * y = y * m :=
  centralizes_of_odd_fix hK8 hx hx4 hm hmo (pow_orderOf_eq_one m) hfix

end CFSG.ClassicalInvolution.Q3.PhilipHall.Frame.TwinPerpV3
