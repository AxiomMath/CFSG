module

public import CFSG.GF2Type.Aschbacher1976Full.ShapeHallR

public section

namespace CFSG.GF2Type.Aschbacher1976Full.Shape

open CFSG CFSG.SectionRank.Ccomm Subgroup
open scoped commutatorElement

section Hall

variable {P : Type*} [Group P] {D E R : Subgroup P} {z : P} {a : P} {k : ℕ}

theorem eq_one_or_eq_of_mem_zpowers_two {x : P} (hz : orderOf z = 2) (hx : x ∈ zpowers z) :
    x = 1 ∨ x = z := by
  obtain ⟨n, rfl⟩ := mem_zpowers_iff.mp hx
  have hz2 : z ^ 2 = 1 := by rw [← hz]; exact pow_orderOf_eq_one z
  rcases Int.even_or_odd' n with ⟨m, rfl | rfl⟩
  · left
    rw [zpow_mul, zpow_two, ← sq, hz2, one_zpow]
  · right
    rw [zpow_add, zpow_mul, zpow_two, ← sq, hz2, one_zpow, one_mul, zpow_one]

theorem zpow_mem_zpowers_sq (a : P) (m : ℤ) : a ^ (2 * m) ∈ zpowers (a ^ 2) :=
  mem_zpowers_iff.mpr ⟨m, by rw [← zpow_natCast a 2, ← zpow_mul]; rfl⟩

theorem conj_zpowers_central (hzc : z ∈ center P) {u : P} (hu : u ∈ zpowers z) (g : P) :
    g * u * g⁻¹ = u := by
  obtain ⟨n, rfl⟩ := mem_zpowers_iff.mp hu
  have hz : g * z * g⁻¹ = z := by
    rw [mul_inv_eq_iff_eq_mul]
    exact mem_center_iff.mp hzc g
  rw [← conj_zpow, hz]

variable [Finite P]

theorem Gen.C2_normal (c : CritData D E R z) (hg : Gen c a k) (hk : 1 ≤ k) :
    (zpowers (a ^ 2)).Normal := by
  haveI := c.Z_normal
  refine ⟨fun n hn f => ?_⟩
  obtain ⟨j, rfl⟩ := mem_zpowers_iff.mp hn
  obtain ⟨s, -, hs⟩ := exists_act hg.mem hg.gen hg.ord hk f
  have h2 : f * a ^ 2 * f⁻¹ = a ^ (s * 2) := by simpa using hs 2
  have h3 : f * (a ^ 2) ^ j * f⁻¹ = (a ^ (s * 2)) ^ j := by rw [← h2, conj_zpow]
  rw [h3]
  refine mem_zpowers_iff.mpr ⟨s * j, ?_⟩
  rw [← zpow_mul, ← zpow_natCast a 2, ← zpow_mul]
  congr 1
  push_cast
  ring

theorem CritData.comm_E_mem (c : CritData D E R z) (f : P) {e : P} (he : e ∈ E) :
    f * e * f⁻¹ * e⁻¹ ∈ zpowers z := by
  haveI := c.R_normal
  have hf : f ∈ E ⊔ R := by rw [c.ER]; exact mem_top f
  obtain ⟨e', he', r, hr, rfl⟩ := mem_sup_of_normal_right.mp hf
  have hconj : r * e * r⁻¹ = e := by
    rw [mul_inv_eq_iff_eq_mul]
    exact (c.E_R_comm he hr).symm
  have h1 : e' * r * e * (e' * r)⁻¹ * e⁻¹ = e' * e * e'⁻¹ * e⁻¹ := by
    calc e' * r * e * (e' * r)⁻¹ * e⁻¹ = e' * (r * e * r⁻¹) * e'⁻¹ * e⁻¹ := by group
      _ = e' * e * e'⁻¹ * e⁻¹ := by rw [hconj]
  rw [h1]
  exact c.E_comm e' he' e he

theorem Gen.C2_le_Z (c : CritData D E R z) (hg : Gen c a k) : zpowers (a ^ 2) ≤ Zof D :=
  zpowers_le.mpr (pow_mem hg.mem 2)

theorem Gen.comm_D_mem (c : CritData D E R z) (hg : Gen c a k) (hk : 3 ≤ k) (f : P) {d : P}
    (hd : d ∈ D) : f * d * f⁻¹ * d⁻¹ ∈ zpowers (a ^ 2) := by
  obtain ⟨e, he, y, hy, rfl⟩ := c.exists_mul_of_mem_D hd
  have h1 : f * e * f⁻¹ * e⁻¹ ∈ zpowers (a ^ 2) :=
    zpowers_le.mpr (hg.z_mem_C2 c (by omega)) (c.comm_E_mem f he)
  have h2 := hg.comm_mem c (by omega) f hy
  have h3 : e * (f * y * f⁻¹ * y⁻¹) * e⁻¹ = f * y * f⁻¹ * y⁻¹ := by
    rw [mul_inv_eq_iff_eq_mul]
    exact CritData.Z_comm D (hg.C2_le_Z c h2) (c.E_le_D he)
  have h4 : f * (e * y) * f⁻¹ * (e * y)⁻¹ =
      (f * e * f⁻¹ * e⁻¹) * (e * (f * y * f⁻¹ * y⁻¹) * e⁻¹) := by group
  rw [h4, h3]
  exact mul_mem h1 h2

theorem Gen.sq_D_mem [Finite P] (c : CritData D E R z) (hg : Gen c a k) (hk : 2 ≤ k) {d : P}
    (hd : d ∈ D) : d ^ 2 ∈ zpowers (a ^ 2) := by
  obtain ⟨e, he, y, hy, rfl⟩ := c.exists_mul_of_mem_D hd
  have hcomm : Commute e y := CritData.Z_comm D hy (c.E_le_D he)
  rw [hcomm.mul_pow]
  exact mul_mem (zpowers_le.mpr (hg.z_mem_C2 c hk) (c.E_sq e he)) (hg.sq_mem c hy)

theorem Gen.sq_x_mem (c : CritData D E R z) (hg : Gen c a k) (hk : 1 ≤ k) {x : P} (hxR : x ∈ R)
    (hxτ : x * a * x⁻¹ = a ^ ((1 : ℤ) + 2 ^ (k - 1))) (hx2 : x ^ 2 ∈ D) :
    ∃ c' : ℤ, x ^ 2 = a ^ (2 * c') := by
  have hZ : x ^ 2 ∈ Zof D := by
    have h : x ^ 2 ∈ R ⊓ centralizer ((Zof D : Subgroup P) : Set P) :=
      ⟨pow_mem hxR 2, by rw [c.cent]; exact hx2⟩
    rwa [c.RZ] at h
  obtain ⟨n, hn⟩ := hg.gen _ hZ
  have h1 : x * a ^ n * x⁻¹ = a ^ n := by
    rw [hn]
    group
  rw [conj_zpow_eq hxτ n] at h1
  have h3 := (zpow_eq_zpow_iff_dvd hg.ord).mp h1
  obtain ⟨j, rfl⟩ : ∃ j, k = j + 1 := ⟨k - 1, by omega⟩
  have h4 : (2 : ℤ) ^ j * 2 ∣ 2 ^ j * n := by
    have : ((1 : ℤ) + 2 ^ (j + 1 - 1)) * n - n = 2 ^ j * n := by
      rw [show j + 1 - 1 = j by omega]
      ring
    rw [this, pow_succ] at h3
    exact h3
  obtain ⟨c', hc'⟩ := (mul_dvd_mul_iff_left (by positivity : (2 : ℤ) ^ j ≠ 0)).mp h4
  exact ⟨c', by rw [← hn, hc']⟩

theorem Gen.comm_R_x (c : CritData D E R z) (hg : Gen c a k) (hk : 3 ≤ k) {x : P} (hxR : x ∈ R)
    (hxτ : x * a * x⁻¹ = a ^ ((1 : ℤ) + 2 ^ (k - 1))) (hx2 : x ^ 2 ∈ D) {r : P} (hr : r ∈ R) :
    r * x * r⁻¹ * x⁻¹ ∈ zpowers (a ^ 2) := by
  haveI := c.Z_normal
  obtain ⟨c', hc'⟩ := hg.sq_x_mem c (by omega) hxR hxτ hx2
  obtain ⟨s, hso, hs⟩ := exists_act hg.mem hg.gen hg.ord (by omega) r
  obtain ⟨s', -, hs'⟩ := exists_act hg.mem hg.gen hg.ord (by omega) r⁻¹
  have hx' : ∀ j : ℤ, x * a ^ j * x⁻¹ = a ^ (((1 : ℤ) + 2 ^ (k - 1)) * j) := conj_zpow_eq hxτ
  have hxinv := hg.x_act_inv c (by omega) hxτ
  have hτ2 : a ^ (((1 : ℤ) + 2 ^ (k - 1)) * ((1 : ℤ) + 2 ^ (k - 1))) = a := by
    have := (zpow_eq_zpow_iff_dvd hg.ord (a := a) (m := ((1 : ℤ) + 2 ^ (k - 1)) *
      ((1 : ℤ) + 2 ^ (k - 1))) (n := 1)).mpr (tau_sq (by omega))
    rwa [zpow_one] at this
  have hss' : a ^ (s * s') = a := by
    have h1 : r⁻¹ * a * r = a ^ s' := by simpa using hs' 1
    calc a ^ (s * s') = r * a ^ s' * r⁻¹ := (hs s').symm
      _ = r * (r⁻¹ * a * r) * r⁻¹ := by rw [h1]
      _ = a := by group
  have hwD : r * x * r⁻¹ * x⁻¹ ∈ D := by
    rw [hg.mem_D_iff c]
    have h2 : r⁻¹ * a ^ ((1 : ℤ) + 2 ^ (k - 1)) * r = a ^ (s' * ((1 : ℤ) + 2 ^ (k - 1))) := by
      have := hs' ((1 : ℤ) + 2 ^ (k - 1))
      rwa [inv_inv] at this
    calc (r * x * r⁻¹ * x⁻¹) * a * (r * x * r⁻¹ * x⁻¹)⁻¹
        = r * (x * (r⁻¹ * (x⁻¹ * a * x) * r) * x⁻¹) * r⁻¹ := by group
      _ = r * (x * (r⁻¹ * a ^ ((1 : ℤ) + 2 ^ (k - 1)) * r) * x⁻¹) * r⁻¹ := by rw [hxinv]
      _ = r * (x * a ^ (s' * ((1 : ℤ) + 2 ^ (k - 1))) * x⁻¹) * r⁻¹ := by rw [h2]
      _ = r * a ^ (((1 : ℤ) + 2 ^ (k - 1)) * (s' * ((1 : ℤ) + 2 ^ (k - 1)))) * r⁻¹ := by
          rw [hx']
      _ = a ^ (s * (((1 : ℤ) + 2 ^ (k - 1)) * (s' * ((1 : ℤ) + 2 ^ (k - 1))))) := hs _
      _ = a := by
          rw [show s * (((1 : ℤ) + 2 ^ (k - 1)) * (s' * ((1 : ℤ) + 2 ^ (k - 1)))) =
            (s * s') * (((1 : ℤ) + 2 ^ (k - 1)) * ((1 : ℤ) + 2 ^ (k - 1))) by ring, zpow_mul,
            hss', hτ2]
  have hwR : r * x * r⁻¹ * x⁻¹ ∈ R :=
    mul_mem (mul_mem (mul_mem hr hxR) (inv_mem hr)) (inv_mem hxR)
  have hwZ : r * x * r⁻¹ * x⁻¹ ∈ Zof D := by
    have h : r * x * r⁻¹ * x⁻¹ ∈ R ⊓ centralizer ((Zof D : Subgroup P) : Set P) :=
      ⟨hwR, by rw [c.cent]; exact hwD⟩
    rwa [c.RZ] at h
  obtain ⟨m, hm⟩ := hg.gen _ hwZ
  have hrx : r * x * r⁻¹ = a ^ m * x := by
    rw [hm]
    group
  have h1 : a ^ (s * (2 * c')) = a ^ (m + ((1 : ℤ) + 2 ^ (k - 1)) * m + 2 * c') := by
    calc a ^ (s * (2 * c')) = r * a ^ (2 * c') * r⁻¹ := (hs _).symm
      _ = r * x ^ 2 * r⁻¹ := by rw [← hc']
      _ = (r * x * r⁻¹) * (r * x * r⁻¹) := by rw [pow_two]; group
      _ = (a ^ m * x) * (a ^ m * x) := by rw [hrx]
      _ = a ^ m * (x * a ^ m * x⁻¹) * x ^ 2 := by rw [pow_two]; group
      _ = a ^ m * a ^ (((1 : ℤ) + 2 ^ (k - 1)) * m) * a ^ (2 * c') := by rw [hx' m, hc']
      _ = a ^ (m + ((1 : ℤ) + 2 ^ (k - 1)) * m + 2 * c') := by rw [← zpow_add, ← zpow_add]
  have h2 := (zpow_eq_zpow_iff_dvd hg.ord).mp h1
  obtain ⟨t, ht⟩ := hso
  obtain ⟨j, rfl⟩ : ∃ j, k = j + 3 := ⟨k - 3, by omega⟩
  have hT' : (1 : ℤ) + 2 ^ (j + 3 - 1) = 1 + 4 * 2 ^ j := by
    rw [show j + 3 - 1 = j + 2 by omega, pow_add]
    ring
  have h8 : (2 : ℤ) ^ (j + 3) = 8 * 2 ^ j := by ring
  have h4 : (4 : ℤ) ∣ (s * (2 * c') - (m + ((1 : ℤ) + 2 ^ (j + 3 - 1)) * m + 2 * c')) :=
    dvd_trans ⟨2 * 2 ^ j, by rw [h8]; ring⟩ h2
  have h5 : s * (2 * c') - (m + ((1 : ℤ) + 2 ^ (j + 3 - 1)) * m + 2 * c') =
      4 * (t * c') - 2 * m - 4 * (m * 2 ^ j) := by
    rw [ht, hT']
    ring
  rw [h5] at h4
  have hm2 : (2 : ℤ) ∣ m := by
    generalize t * c' = U at h4
    generalize m * 2 ^ j = V at h4
    omega
  obtain ⟨m', hm'⟩ := hm2
  rw [← hm, hm']
  exact zpow_mem_zpowers_sq a m'

theorem Gen.comm_P_x (c : CritData D E R z) (hg : Gen c a k) (hk : 3 ≤ k) {x : P} (hxR : x ∈ R)
    (hxτ : x * a * x⁻¹ = a ^ ((1 : ℤ) + 2 ^ (k - 1))) (hx2 : x ^ 2 ∈ D) (f : P) :
    f * x * f⁻¹ * x⁻¹ ∈ zpowers (a ^ 2) := by
  haveI := c.R_normal
  have hf : f ∈ E ⊔ R := by rw [c.ER]; exact mem_top f
  obtain ⟨e', he', r, hr, rfl⟩ := mem_sup_of_normal_right.mp hf
  have h1 : r * x * r⁻¹ ∈ R := mul_mem (mul_mem hr hxR) (inv_mem hr)
  have h2 : e' * (r * x * r⁻¹) * e'⁻¹ = r * x * r⁻¹ := by
    rw [mul_inv_eq_iff_eq_mul]
    exact c.E_R_comm he' h1
  have h3 : (e' * r) * x * (e' * r)⁻¹ * x⁻¹ = (r * x * r⁻¹) * x⁻¹ := by
    calc (e' * r) * x * (e' * r)⁻¹ * x⁻¹ = e' * (r * x * r⁻¹) * e'⁻¹ * x⁻¹ := by group
      _ = (r * x * r⁻¹) * x⁻¹ := by rw [h2]
  rw [h3]
  exact hg.comm_R_x c hk hxR hxτ hx2 hr

end Hall

end CFSG.GF2Type.Aschbacher1976Full.Shape
