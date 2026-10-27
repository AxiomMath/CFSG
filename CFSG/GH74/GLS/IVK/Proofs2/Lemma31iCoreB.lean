module

public import CFSG.GH74.GLS.IVK.Proofs2.Lemma31iRels
public import CFSG.GroupTheory.ABGDGroups.LinearCentralizers
public import CFSG.GH74.GLS.IVK.Defs

public section

namespace CFSG.GH74.GLS.IVK.Proofs2

open Subgroup CFSG.GH74.GLS.IVK

namespace Lemma31iCoreB

open Lemma31iRels

variable {G : Type} [Group G] {n : ℕ} {z t d j d' j' : G}

theorem jd_eq (h : Rels n z t d j d' j') : j * d = d⁻¹ * j := by
  have := h.jdj
  rwa [mul_inv_eq_iff_eq_mul] at this

theorem j'd'_eq (h : Rels n z t d j d' j') : j' * d' = d'⁻¹ * j' := by
  have := h.jdj'
  rwa [mul_inv_eq_iff_eq_mul] at this

theorem tj_eq (h : Rels n z t d j d' j') : t * j = j' * t := by
  have := h.tj
  rwa [mul_inv_eq_iff_eq_mul] at this

theorem tj'_eq (h : Rels n z t d j d' j') : t * j' = j * t := by
  have := h.tj'
  rwa [mul_inv_eq_iff_eq_mul] at this

theorem td'_eq (h : Rels n z t d j d' j') : t * d' = d * t := by
  have := h.td'
  rwa [mul_inv_eq_iff_eq_mul] at this

theorem z_comm_dinv (h : Rels n z t d j d' j') : z * d⁻¹ = d⁻¹ * z := by
  have : Commute z d := h.z_comm_d
  exact this.inv_right.eq

theorem tinv (h : Rels n z t d j d' j') : t⁻¹ = t := inv_eq_of_mul_eq_one_right h.tt

theorem d_sq_ne_one (h : Rels n z t d j d' j') : d * d ≠ 1 := by
  intro hd
  have hn := h.three_le
  have h1 : orderOf d ∣ 2 := orderOf_dvd_of_pow_eq_one (by rw [sq]; exact hd)
  rw [h.d_ord] at h1
  have h2 := Nat.le_of_dvd (by norm_num) h1
  have h3 : 2 ^ 2 ≤ 2 ^ (n - 1) := Nat.pow_le_pow_right (by norm_num) (by omega)
  omega

theorem y_sq (h : Rels n z t d j d' j') : (j * d' * j') * (j * d' * j') = 1 := by
  have e1 : j * d' * j' * (j * d' * j') = (j * j) * d' * (j' * d' * j') := by
    calc j * d' * j' * (j * d' * j') = j * d' * (j' * j) * d' * j' := by group
      _ = j * d' * (j * j') * d' * j' := by rw [← h.jj'c]
      _ = j * (d' * j) * j' * d' * j' := by group
      _ = j * (j * d') * j' * d' * j' := by rw [← h.jd']
      _ = (j * j) * d' * (j' * d' * j') := by group
  have e2 : j' * d' * j' = d'⁻¹ * z := by
    calc j' * d' * j' = (j' * d' * j'⁻¹) * (j' * j') := by group
      _ = d'⁻¹ * z := by rw [h.jdj', h.jj']
  rw [e1, h.jj, e2]
  calc z * d' * (d'⁻¹ * z) = z * z := by group
    _ = 1 := h.z_sq

theorem y_d (h : Rels n z t d j d' j') : (j * d' * j') * d = d⁻¹ * (j * d' * j') := by
  calc j * d' * j' * d = j * d' * (j' * d) := by group
    _ = j * d' * (d * j') := by rw [h.dj']
    _ = j * (d' * d) * j' := by group
    _ = j * (d * d') * j' := by rw [h.dd']
    _ = (j * d) * d' * j' := by group
    _ = (d⁻¹ * j) * d' * j' := by rw [jd_eq h]
    _ = d⁻¹ * (j * d' * j') := by group

theorem y_d' (h : Rels n z t d j d' j') : (j * d' * j') * d' = d'⁻¹ * (j * d' * j') := by
  have hjd'inv : j * d'⁻¹ = d'⁻¹ * j := by
    have : Commute j d' := h.jd'
    exact (this.inv_right).eq
  calc j * d' * j' * d' = j * d' * (j' * d') := by group
    _ = j * d' * (d'⁻¹ * j') := by rw [j'd'_eq h]
    _ = j * j' := by group
    _ = j * (d'⁻¹ * d') * j' := by group
    _ = (j * d'⁻¹) * d' * j' := by group
    _ = (d'⁻¹ * j) * d' * j' := by rw [hjd'inv]
    _ = d'⁻¹ * (j * d' * j') := by group

theorem y_conj_d (h : Rels n z t d j d' j') : (j * d' * j') * d * (j * d' * j')⁻¹ = d⁻¹ := by
  rw [mul_inv_eq_iff_eq_mul]
  exact y_d h

theorem y_conj_d' (h : Rels n z t d j d' j') : (j * d' * j') * d' * (j * d' * j')⁻¹ = d'⁻¹ := by
  rw [mul_inv_eq_iff_eq_mul]
  exact y_d' h

theorem orderOf_y (h : Rels n z t d j d' j') : orderOf (j * d' * j') = 2 := by
  have hy2 : (j * d' * j') ^ 2 = 1 := by rw [sq]; exact y_sq h
  have hy1 : j * d' * j' ≠ 1 := by
    intro hy
    have := y_d h
    rw [hy, one_mul, mul_one] at this
    apply d_sq_ne_one h
    calc d * d = d * d⁻¹⁻¹ := by rw [inv_inv]
      _ = 1 := by rw [← this]; simp
  exact orderOf_eq_prime hy2 hy1

theorem yinv (h : Rels n z t d j d' j') : (j * d' * j')⁻¹ = j * d' * j' :=
  inv_eq_of_mul_eq_one_right (y_sq h)

theorem s_sq (h : Rels n z t d j d' j') : (j * j' * t) * (j * j' * t) = 1 := by
  have htv : t * (j * j') = (j * j') * t := by
    calc t * (j * j') = (t * j) * j' := by group
      _ = j' * t * j' := by rw [tj_eq h]
      _ = j' * (t * j') := by group
      _ = j' * (j * t) := by rw [tj'_eq h]
      _ = (j' * j) * t := by group
      _ = (j * j') * t := by rw [h.jj'c]
  have hv : (j * j') * (j * j') = 1 := by
    calc (j * j') * (j * j') = j * (j' * j) * j' := by group
      _ = j * (j * j') * j' := by rw [← h.jj'c]
      _ = (j * j) * (j' * j') := by group
      _ = z * z := by rw [h.jj, h.jj']
      _ = 1 := h.z_sq
  calc (j * j' * t) * (j * j' * t) = (j * j') * (t * (j * j')) * t := by group
    _ = (j * j') * ((j * j') * t) * t := by rw [htv]
    _ = ((j * j') * (j * j')) * (t * t) := by group
    _ = 1 := by rw [hv, h.tt]; group

theorem t_y (h : Rels n z t d j d' j') : t * (j * d' * j') = j' * d * j * t := by
  calc t * (j * d' * j') = (t * j) * d' * j' := by group
    _ = j' * t * d' * j' := by rw [tj_eq h]
    _ = j' * (t * d') * j' := by group
    _ = j' * (d * t) * j' := by rw [td'_eq h]
    _ = j' * d * (t * j') := by group
    _ = j' * d * (j * t) := by rw [tj'_eq h]
    _ = j' * d * j * t := by group

theorem s_y (h : Rels n z t d j d' j') :
    (j * j' * t) * (j * d' * j') = d⁻¹ * t := by
  calc (j * j' * t) * (j * d' * j') = (j * j') * (t * (j * d' * j')) := by group
    _ = (j * j') * (j' * d * j * t) := by rw [t_y h]
    _ = j * (j' * j') * d * j * t := by group
    _ = j * z * d * j * t := by rw [h.jj']
    _ = z * (j * d * j) * t := by
        have : j * z = z * j := h.z_comm_j.symm
        calc j * z * d * j * t = (j * z) * d * j * t := by group
          _ = (z * j) * d * j * t := by rw [this]
          _ = z * (j * d * j) * t := by group
    _ = z * (d⁻¹ * z) * t := by
        have : j * d * j = d⁻¹ * z := by
          calc j * d * j = (j * d * j⁻¹) * (j * j) := by group
            _ = d⁻¹ * z := by rw [h.jdj, h.jj]
        rw [this]
    _ = d⁻¹ * (z * z) * t := by
        have := z_comm_dinv h
        calc z * (d⁻¹ * z) * t = (z * d⁻¹) * z * t := by group
          _ = (d⁻¹ * z) * z * t := by rw [this]
          _ = d⁻¹ * (z * z) * t := by group
    _ = d⁻¹ * t := by rw [h.z_sq]; group

theorem r2_sq (h : Rels n z t d j d' j') :
    (t * (j * d' * j')) * (t * (j * d' * j')) = d * d'⁻¹ := by
  have hj'd : j' * d * j'⁻¹ = d := by
    rw [mul_inv_eq_iff_eq_mul]
    exact h.dj'.symm
  have hzd : z * d = d * z := h.z_comm_d
  have hzd' : z * d' = d' * z := h.z_comm_d'
  have hzj' : z * j' = j' * z := h.z_comm_j'
  have e1 : j' * d * (j * j) * d' * j' = z * (j' * d * d' * j') := by
    rw [h.jj]
    calc j' * d * z * d' * j' = j' * (d * z) * d' * j' := by group
      _ = j' * (z * d) * d' * j' := by rw [hzd]
      _ = (j' * z) * d * d' * j' := by group
      _ = (z * j') * d * d' * j' := by rw [hzj']
      _ = z * (j' * d * d' * j') := by group
  have e2 : j' * d * d' * j' = d * d'⁻¹ * z := by
    calc j' * d * d' * j' = (j' * d * j'⁻¹) * (j' * d' * j'⁻¹) * (j' * j') := by group
      _ = d * d'⁻¹ * z := by rw [hj'd, h.jdj', h.jj']
  calc (t * (j * d' * j')) * (t * (j * d' * j'))
      = (t * (j * d' * j')) * t * (j * d' * j') := by group
    _ = (j' * d * j * t) * t * (j * d' * j') := by rw [t_y h]
    _ = j' * d * j * (t * t) * (j * d' * j') := by group
    _ = j' * d * (j * j) * d' * j' := by rw [h.tt]; group
    _ = z * (j' * d * d' * j') := e1
    _ = z * (d * d'⁻¹ * z) := by rw [e2]
    _ = d * d'⁻¹ := by
        have hc : z * (d * d'⁻¹) = (d * d'⁻¹) * z := by
          have c1 : Commute z d := hzd
          have c2 : Commute z d' := hzd'
          exact (c1.mul_right c2.inv_right).eq
        calc z * (d * d'⁻¹ * z) = (z * (d * d'⁻¹)) * z := by group
          _ = ((d * d'⁻¹) * z) * z := by rw [hc]
          _ = (d * d'⁻¹) * (z * z) := by group
          _ = d * d'⁻¹ := by rw [h.z_sq]; group

theorem dm_ne (h : Rels n z t d j d' j') : d ^ 2 ^ (n - 3) ≠ 1 ∧ d ^ 2 ^ (n - 3) ≠ z := by
  have hn := h.three_le
  obtain ⟨m, rfl⟩ : ∃ m, n = m + 3 := ⟨n - 3, by omega⟩
  have e3 : m + 3 - 3 = m := by omega
  have e2 : m + 3 - 2 = m + 1 := by omega
  have e1 : m + 3 - 1 = m + 2 := by omega
  rw [e3]
  have hz : z = d ^ 2 ^ (m + 1) := by have := h.z_eq; rwa [e2] at this
  constructor
  · intro h1
    have : orderOf d ∣ 2 ^ m := orderOf_dvd_of_pow_eq_one h1
    rw [h.d_ord, e1] at this
    have := Nat.le_of_dvd (by positivity) this
    have : 2 ^ m < 2 ^ (m + 2) := Nat.pow_lt_pow_right (by norm_num) (by omega)
    omega
  · intro h1
    rw [hz] at h1
    have h3 : d ^ (2 ^ (m + 1) - 2 ^ m) = 1 := by
      have hle : 2 ^ m ≤ 2 ^ (m + 1) := Nat.pow_le_pow_right (by norm_num) (by omega)
      have : d ^ 2 ^ m * d ^ (2 ^ (m + 1) - 2 ^ m) = d ^ 2 ^ m * 1 := by
        rw [← pow_add, Nat.add_sub_cancel' hle, mul_one]
        exact h1.symm
      exact mul_left_cancel this
    have h4 : orderOf d ∣ 2 ^ (m + 1) - 2 ^ m := orderOf_dvd_of_pow_eq_one h3
    rw [h.d_ord, e1] at h4
    have hpos : 0 < 2 ^ (m + 1) - 2 ^ m := by
      have : 2 ^ m < 2 ^ (m + 1) := Nat.pow_lt_pow_right (by norm_num) (by omega)
      omega
    have := Nat.le_of_dvd hpos h4
    have : 2 ^ (m + 1) = 2 * 2 ^ m := by ring
    have : 2 ^ (m + 2) = 4 * 2 ^ m := by ring
    omega

theorem a_pow (h : Rels n z t d j d' j') (k : ℕ) : (d * d') ^ k = d ^ k * d' ^ k :=
  Commute.mul_pow (show Commute d d' from h.dd') k

theorem u0_ne_one (h : Rels n z t d j d' j') : d ^ 2 ^ (n - 3) * d' ^ 2 ^ (n - 3) ≠ 1 := by
  have hn := h.three_le
  have hdm := dm_ne h
  obtain ⟨m, rfl⟩ : ∃ m, n = m + 3 := ⟨n - 3, by omega⟩
  have e3 : m + 3 - 3 = m := by omega
  have e1 : m + 3 - 1 = m + 2 := by omega
  rw [e3] at hdm ⊢
  intro hu
  have hN : d' ^ 2 ^ (m + 2) = 1 := by have := h.d'_pow; rwa [e1] at this
  have hm : 2 ^ m ≤ 2 ^ (m + 2) := Nat.pow_le_pow_right (by norm_num) (by omega)
  have hdd : d ^ 2 ^ m = d' ^ (2 ^ (m + 2) - 2 ^ m) := by
    have h1 : d' ^ 2 ^ m * d' ^ (2 ^ (m + 2) - 2 ^ m) = 1 := by
      rw [← pow_add, Nat.add_sub_cancel' hm]; exact hN
    have h2 : d ^ 2 ^ m = (d' ^ 2 ^ m)⁻¹ := eq_inv_of_mul_eq_one_left hu
    rw [h2]
    exact inv_eq_of_mul_eq_one_right h1
  rcases h.indep _ _ hdd with h1 | h1
  · exact hdm.1 h1
  · exact hdm.2 h1

theorem v0_ne_one (h : Rels n z t d j d' j') :
    d ^ 2 ^ (n - 3) * (d' ^ 2 ^ (n - 3))⁻¹ ≠ 1 := by
  intro hv
  have h1 : d ^ 2 ^ (n - 3) = d' ^ 2 ^ (n - 3) := mul_inv_eq_one.mp hv
  rcases h.indep _ _ h1 with h2 | h2
  · exact (dm_ne h).1 h2
  · exact (dm_ne h).2 h2

theorem orderOf_r1 (h : Rels n z t d j d' j') : orderOf (d⁻¹ * t) = 2 ^ (n - 1) := by
  have hn := h.three_le
  have hu := u0_ne_one h
  have hc : Commute d d' := h.dd'
  have htd : t * d⁻¹ * t⁻¹ = d'⁻¹ := by
    calc t * d⁻¹ * t⁻¹ = (t * d * t⁻¹)⁻¹ := by group
      _ = d'⁻¹ := by rw [h.td]
  have hr1sq : (d⁻¹ * t) * (d⁻¹ * t) = (d * d')⁻¹ := by
    calc (d⁻¹ * t) * (d⁻¹ * t) = d⁻¹ * (t * d⁻¹ * t⁻¹) * (t * t) := by group
      _ = d⁻¹ * d'⁻¹ * 1 := by rw [htd, h.tt]
      _ = (d * d')⁻¹ := by rw [mul_one, hc.inv_inv.eq, mul_inv_rev]
  obtain ⟨m, rfl⟩ : ∃ m, n = m + 3 := ⟨n - 3, by omega⟩
  have e3 : m + 3 - 3 = m := by omega
  have e2 : m + 3 - 2 = m + 1 := by omega
  have e1 : m + 3 - 1 = m + 2 := by omega
  rw [e1]
  rw [e3] at hu
  have hz : z = d ^ 2 ^ (m + 1) := by have := h.z_eq; rwa [e2] at this
  have hz' : z = d' ^ 2 ^ (m + 1) := by have := h.z_eq'; rwa [e2] at this
  have hsq : ∀ k : ℕ, (d⁻¹ * t) ^ (2 * k) = ((d * d') ^ k)⁻¹ := by
    intro k
    rw [pow_mul, sq, hr1sq, inv_pow]
  apply orderOf_eq_prime_pow (n := m + 1)
  · intro h1
    have : (d⁻¹ * t) ^ 2 ^ (m + 1) = ((d * d') ^ 2 ^ m)⁻¹ := by
      rw [pow_succ', hsq]
    rw [this, inv_eq_one, a_pow h] at h1
    exact hu h1
  · have : (d⁻¹ * t) ^ 2 ^ (m + 1 + 1) = ((d * d') ^ 2 ^ (m + 1))⁻¹ := by
      rw [pow_succ' 2 (m + 1), hsq]
    rw [this, a_pow h, ← hz, ← hz', h.z_sq]
    simp

theorem orderOf_r2 (h : Rels n z t d j d' j') : orderOf (t * (j * d' * j')) = 2 ^ (n - 1) := by
  have hn := h.three_le
  have hv := v0_ne_one h
  have hc : Commute d d' := h.dd'
  obtain ⟨m, rfl⟩ : ∃ m, n = m + 3 := ⟨n - 3, by omega⟩
  have e3 : m + 3 - 3 = m := by omega
  have e2 : m + 3 - 2 = m + 1 := by omega
  have e1 : m + 3 - 1 = m + 2 := by omega
  rw [e1]
  rw [e3] at hv
  have hz : z = d ^ 2 ^ (m + 1) := by have := h.z_eq; rwa [e2] at this
  have hz' : z = d' ^ 2 ^ (m + 1) := by have := h.z_eq'; rwa [e2] at this
  have hbpow : ∀ k : ℕ, (d * d'⁻¹) ^ k = d ^ k * (d' ^ k)⁻¹ := by
    intro k
    rw [Commute.mul_pow (hc.inv_right) k, inv_pow]
  have hsq : ∀ k : ℕ, (t * (j * d' * j')) ^ (2 * k) = (d * d'⁻¹) ^ k := by
    intro k
    rw [pow_mul, sq, r2_sq h]
  apply orderOf_eq_prime_pow (n := m + 1)
  · intro h1
    have : (t * (j * d' * j')) ^ 2 ^ (m + 1) = (d * d'⁻¹) ^ 2 ^ m := by
      rw [pow_succ', hsq]
    rw [this, hbpow] at h1
    exact hv h1
  · have : (t * (j * d' * j')) ^ 2 ^ (m + 1 + 1) = (d * d'⁻¹) ^ 2 ^ (m + 1) := by
      rw [pow_succ' 2 (m + 1), hsq]
    rw [this, hbpow, ← hz, ← hz']
    have : z⁻¹ = z := inv_eq_of_mul_eq_one_right h.z_sq
    rw [this, h.z_sq]

theorem dihedral_of_inv [Finite G] (r y : G) {N : ℕ} (hN : 2 ≤ N) (hr : orderOf r = N)
    (hy : y * y = 1) (hinv : y * r * y⁻¹ = r⁻¹) (hr2 : r * r ≠ 1) :
    IsDihedralOrder ↥(zpowers r ⊔ zpowers y) (2 * N) := by
  have hysT : y ∉ zpowers r := by
    intro hmem
    obtain ⟨k, hk⟩ := Subgroup.mem_zpowers_iff.mp hmem
    have hcomm : y * r = r * y := by
      rw [← hk]
      exact ((Commute.refl r).zpow_right k).eq.symm
    have : r⁻¹ = r := by
      calc r⁻¹ = y * r * y⁻¹ := hinv.symm
        _ = r * y * y⁻¹ := by rw [hcomm]
        _ = r := by group
    apply hr2
    calc r * r = r * r⁻¹ := by rw [this]
      _ = 1 := by group
  have hinv' : ∀ x ∈ zpowers r, y * x * y⁻¹ = x⁻¹ := by
    intro x hx
    obtain ⟨k, rfl⟩ := Subgroup.mem_zpowers_iff.mp hx
    calc y * r ^ k * y⁻¹ = (y * r * y⁻¹) ^ k := (conj_zpow).symm
      _ = (r ^ k)⁻¹ := by rw [hinv, inv_zpow]
  obtain ⟨e⟩ := CFSG.ABGDGroups.nonempty_mulEquiv_dihedral_of_reflected (T := zpowers r) hysT hy hinv'
  refine ⟨N, rfl, hN, ⟨?_⟩⟩
  have hc : Nat.card (zpowers r) = N := by rw [Nat.card_zpowers, hr]
  rw [hc] at e
  exact e

theorem r_sq_ne_one {r : G} {N : ℕ} (hN : 3 ≤ N) (hr : orderOf r = N) : r * r ≠ 1 := by
  intro h1
  have : orderOf r ∣ 2 := orderOf_dvd_of_pow_eq_one (by rw [sq]; exact h1)
  rw [hr] at this
  have := Nat.le_of_dvd (by norm_num) this
  omega

theorem two_pow_ge (h : Rels n z t d j d' j') : 4 ≤ 2 ^ (n - 1) := by
  have hn := h.three_le
  calc 4 = 2 ^ 2 := by norm_num
    _ ≤ 2 ^ (n - 1) := Nat.pow_le_pow_right (by norm_num) (by omega)

theorem two_pow_succ (h : Rels n z t d j d' j') : 2 * 2 ^ (n - 1) = 2 ^ n := by
  have hn := h.three_le
  rw [← pow_succ']
  congr 1
  omega

theorem y_inv_r1 (h : Rels n z t d j d' j') :
    (j * d' * j') * (d⁻¹ * t) * (j * d' * j')⁻¹ = (d⁻¹ * t)⁻¹ := by
  rw [← s_y h, yinv h, mul_inv_rev, yinv h, inv_eq_of_mul_eq_one_right (s_sq h)]
  calc (j * d' * j') * ((j * j' * t) * (j * d' * j')) * (j * d' * j')
      = (j * d' * j') * (j * j' * t) * ((j * d' * j') * (j * d' * j')) := by group
    _ = (j * d' * j') * (j * j' * t) := by rw [y_sq h]; group

theorem y_inv_r2 (h : Rels n z t d j d' j') :
    (j * d' * j') * (t * (j * d' * j')) * (j * d' * j')⁻¹ = (t * (j * d' * j'))⁻¹ := by
  rw [yinv h, mul_inv_rev, yinv h, tinv h]
  calc (j * d' * j') * (t * (j * d' * j')) * (j * d' * j')
      = (j * d' * j') * t * ((j * d' * j') * (j * d' * j')) := by group
    _ = (j * d' * j') * t := by rw [y_sq h]; group

theorem r1_sq (h : Rels n z t d j d' j') : (d⁻¹ * t) * (d⁻¹ * t) = (d * d')⁻¹ := by
  have hc : Commute d d' := h.dd'
  have htd : t * d⁻¹ * t⁻¹ = d'⁻¹ := by
    calc t * d⁻¹ * t⁻¹ = (t * d * t⁻¹)⁻¹ := by group
      _ = d'⁻¹ := by rw [h.td]
  calc (d⁻¹ * t) * (d⁻¹ * t) = d⁻¹ * (t * d⁻¹ * t⁻¹) * (t * t) := by group
    _ = d⁻¹ * d'⁻¹ * 1 := by rw [htd, h.tt]
    _ = (d * d')⁻¹ := by rw [mul_one, hc.inv_inv.eq, mul_inv_rev]

theorem B₁_sup_eq (h : Rels n z t d j d' j') :
    B₁ d d' j j' t ⊔ zpowers (j * d' * j') = zpowers (d⁻¹ * t) ⊔ zpowers (j * d' * j') := by
  have hy : j * d' * j' ∈ zpowers (d⁻¹ * t) ⊔ zpowers (j * d' * j') :=
    Subgroup.mem_sup_right (Subgroup.mem_zpowers _)
  have hr : d⁻¹ * t ∈ zpowers (d⁻¹ * t) ⊔ zpowers (j * d' * j') :=
    Subgroup.mem_sup_left (Subgroup.mem_zpowers _)
  apply le_antisymm
  · refine sup_le (sup_le ?_ ?_) (Subgroup.zpowers_le.mpr hy)
    · rw [Subgroup.zpowers_le]
      have h1 : d * d' = ((d⁻¹ * t) * (d⁻¹ * t))⁻¹ := by
        rw [r1_sq h, inv_inv]
      rw [h1]
      exact Subgroup.inv_mem _ (Subgroup.mul_mem _ hr hr)
    · rw [Subgroup.zpowers_le]
      have h1 : j * j' * t = (d⁻¹ * t) * (j * d' * j') := by
        calc j * j' * t = ((j * j' * t) * (j * d' * j')) * (j * d' * j')⁻¹ := by group
          _ = (d⁻¹ * t) * (j * d' * j') := by rw [s_y h, yinv h]
      rw [h1]
      exact Subgroup.mul_mem _ hr hy
  · refine sup_le (Subgroup.zpowers_le.mpr ?_) (Subgroup.zpowers_le.mpr ?_)
    · have h1 : d⁻¹ * t = (j * j' * t) * (j * d' * j') := (s_y h).symm
      rw [h1]
      refine Subgroup.mul_mem _ ?_ ?_
      · exact Subgroup.mem_sup_left (Subgroup.mem_sup_right (Subgroup.mem_zpowers _))
      · exact Subgroup.mem_sup_right (Subgroup.mem_zpowers _)
    · exact Subgroup.mem_sup_right (Subgroup.mem_zpowers _)

theorem B₂_sup_eq (h : Rels n z t d j d' j') :
    B₂ d d' t ⊔ zpowers (j * d' * j') = zpowers (t * (j * d' * j')) ⊔ zpowers (j * d' * j') := by
  have hy : j * d' * j' ∈ zpowers (t * (j * d' * j')) ⊔ zpowers (j * d' * j') :=
    Subgroup.mem_sup_right (Subgroup.mem_zpowers _)
  have hr : t * (j * d' * j') ∈ zpowers (t * (j * d' * j')) ⊔ zpowers (j * d' * j') :=
    Subgroup.mem_sup_left (Subgroup.mem_zpowers _)
  apply le_antisymm
  · refine sup_le (sup_le ?_ ?_) (Subgroup.zpowers_le.mpr hy)
    · rw [Subgroup.zpowers_le]
      rw [← r2_sq h]
      exact Subgroup.mul_mem _ hr hr
    · rw [Subgroup.zpowers_le]
      have h1 : (t * (j * d' * j')) * (j * d' * j') = t := by
        calc (t * (j * d' * j')) * (j * d' * j') = t * ((j * d' * j') * (j * d' * j')) := by group
          _ = t := by rw [y_sq h]; group
      have h2 := Subgroup.mul_mem _ hr hy
      rwa [h1] at h2
  · refine sup_le (Subgroup.zpowers_le.mpr ?_) (Subgroup.zpowers_le.mpr ?_)
    · refine Subgroup.mul_mem _ ?_ ?_
      · exact Subgroup.mem_sup_left (Subgroup.mem_sup_right (Subgroup.mem_zpowers _))
      · exact Subgroup.mem_sup_right (Subgroup.mem_zpowers _)
    · exact Subgroup.mem_sup_right (Subgroup.mem_zpowers _)

theorem y_dihedral₁ [Finite G] (h : Rels n z t d j d' j') :
    IsDihedralOrder ↥(B₁ d d' j j' t ⊔ zpowers (j * d' * j')) (2 ^ n) := by
  have hr1 := orderOf_r1 h
  have hge := two_pow_ge h
  have hrsq : (d⁻¹ * t) * (d⁻¹ * t) ≠ 1 := r_sq_ne_one (N := 2 ^ (n - 1)) (by omega) hr1
  have hdih := dihedral_of_inv (d⁻¹ * t) (j * d' * j') (N := 2 ^ (n - 1))
    (by omega) hr1 (y_sq h) (y_inv_r1 h) hrsq
  rw [B₁_sup_eq h, ← two_pow_succ h]
  exact hdih

theorem y_dihedral₂ [Finite G] (h : Rels n z t d j d' j') :
    IsDihedralOrder ↥(B₂ d d' t ⊔ zpowers (j * d' * j')) (2 ^ n) := by
  have hr2 := orderOf_r2 h
  have hge := two_pow_ge h
  have hrsq : (t * (j * d' * j')) * (t * (j * d' * j')) ≠ 1 :=
    r_sq_ne_one (N := 2 ^ (n - 1)) (by omega) hr2
  have hdih := dihedral_of_inv (t * (j * d' * j')) (j * d' * j') (N := 2 ^ (n - 1))
    (by omega) hr2 (y_sq h) (y_inv_r2 h) hrsq
  rw [B₂_sup_eq h, ← two_pow_succ h]
  exact hdih

theorem u0_sq (h : Rels n z t d j d' j') :
    uvec n d d' * uvec n d d' = 1 := by
  have hn := h.three_le
  have hc : Commute d d' := h.dd'
  obtain ⟨m, rfl⟩ : ∃ m, n = m + 3 := ⟨n - 3, by omega⟩
  have e3 : m + 3 - 3 = m := by omega
  have e2 : m + 3 - 2 = m + 1 := by omega
  have hz : z = d ^ 2 ^ (m + 1) := by have := h.z_eq; rwa [e2] at this
  have hz' : z = d' ^ 2 ^ (m + 1) := by have := h.z_eq'; rwa [e2] at this
  unfold uvec
  rw [e3]
  have hcm : d' ^ 2 ^ m * d ^ 2 ^ m = d ^ 2 ^ m * d' ^ 2 ^ m :=
    ((hc.symm.pow_pow (2 ^ m) (2 ^ m)).eq)
  calc d ^ 2 ^ m * d' ^ 2 ^ m * (d ^ 2 ^ m * d' ^ 2 ^ m)
      = d ^ 2 ^ m * (d' ^ 2 ^ m * d ^ 2 ^ m) * d' ^ 2 ^ m := by group
    _ = d ^ 2 ^ m * (d ^ 2 ^ m * d' ^ 2 ^ m) * d' ^ 2 ^ m := by rw [hcm]
    _ = d ^ 2 ^ m * d ^ 2 ^ m * (d' ^ 2 ^ m * d' ^ 2 ^ m) := by group
    _ = d ^ 2 ^ (m + 1) * d' ^ 2 ^ (m + 1) := by
        rw [← pow_add, ← pow_add, ← two_mul, pow_succ' 2 m]
    _ = z * z := by rw [← hz, ← hz']
    _ = 1 := h.z_sq

theorem inv_comm_u (h : Rels n z t d j d' j') {x : G} (hxd : x * d * x⁻¹ = d⁻¹)
    (hxd' : x * d' * x⁻¹ = d'⁻¹) : x * uvec n d d' = uvec n d d' * x := by
  have hc : Commute d d' := h.dd'
  have hu2 := u0_sq h
  have hui : (uvec n d d')⁻¹ = uvec n d d' := inv_eq_of_mul_eq_one_right hu2
  have hcm : d' ^ 2 ^ (n - 3) * d ^ 2 ^ (n - 3) = d ^ 2 ^ (n - 3) * d' ^ 2 ^ (n - 3) :=
    (hc.symm.pow_pow (2 ^ (n - 3)) (2 ^ (n - 3))).eq
  have hconj : x * uvec n d d' * x⁻¹ = uvec n d d' := by
    have e1 : x * uvec n d d' * x⁻¹ =
        (x * d * x⁻¹) ^ 2 ^ (n - 3) * (x * d' * x⁻¹) ^ 2 ^ (n - 3) := by
      unfold uvec
      rw [conj_pow, conj_pow]
      group
    rw [e1, hxd, hxd', inv_pow, inv_pow]
    calc (d ^ 2 ^ (n - 3))⁻¹ * (d' ^ 2 ^ (n - 3))⁻¹
        = (d' ^ 2 ^ (n - 3) * d ^ 2 ^ (n - 3))⁻¹ := (mul_inv_rev _ _).symm
      _ = (d ^ 2 ^ (n - 3) * d' ^ 2 ^ (n - 3))⁻¹ := by rw [hcm]
      _ = (uvec n d d')⁻¹ := rfl
      _ = uvec n d d' := hui
  rw [mul_inv_eq_iff_eq_mul] at hconj
  exact hconj

theorem t_comm_u (h : Rels n z t d j d' j') : t * uvec n d d' = uvec n d d' * t := by
  have hc : Commute d d' := h.dd'
  have hconj : t * uvec n d d' * t⁻¹ = uvec n d d' := by
    have e1 : t * uvec n d d' * t⁻¹ = (t * d * t⁻¹) ^ 2 ^ (n - 3) * (t * d' * t⁻¹) ^ 2 ^ (n - 3) := by
      unfold uvec
      rw [conj_pow, conj_pow]
      group
    rw [e1, h.td, h.td']
    unfold uvec
    exact ((hc.symm.pow_pow (2 ^ (n - 3)) (2 ^ (n - 3))).eq)
  rw [mul_inv_eq_iff_eq_mul] at hconj
  exact hconj

theorem v_inv_d (h : Rels n z t d j d' j') : (j * j') * d * (j * j')⁻¹ = d⁻¹ := by
  have hj'd : j' * d * j'⁻¹ = d := by
    rw [mul_inv_eq_iff_eq_mul]
    exact h.dj'.symm
  calc (j * j') * d * (j * j')⁻¹ = j * (j' * d * j'⁻¹) * j⁻¹ := by group
    _ = j * d * j⁻¹ := by rw [hj'd]
    _ = d⁻¹ := h.jdj

theorem v_inv_d' (h : Rels n z t d j d' j') : (j * j') * d' * (j * j')⁻¹ = d'⁻¹ := by
  have hjd'inv : j * d' * j⁻¹ = d' := by
    rw [mul_inv_eq_iff_eq_mul]
    exact h.jd'
  calc (j * j') * d' * (j * j')⁻¹ = j * (j' * d' * j'⁻¹) * j⁻¹ := by group
    _ = j * d'⁻¹ * j⁻¹ := by rw [h.jdj']
    _ = (j * d' * j⁻¹)⁻¹ := by group
    _ = d'⁻¹ := by rw [hjd'inv]

theorem comm_u (h : Rels n z t d j d' j') :
    ∀ g ∈ B₁ d d' j j' t ⊔ B₂ d d' t ⊔ zpowers (j * d' * j'),
      g * uvec n d d' = uvec n d d' * g := by
  have hc : Commute d d' := h.dd'
  have hcu : ∀ {x : G}, x * uvec n d d' = uvec n d d' * x →
      x ∈ centralizer ({uvec n d d'} : Set G) := by
    intro x hx
    rw [Subgroup.mem_centralizer_singleton_iff]
    exact hx
  have hcomm_ab : ∀ {x : G}, Commute x d → Commute x d' → x * uvec n d d' = uvec n d d' * x := by
    intro x h1 h2
    unfold uvec
    exact ((h1.pow_right _).mul_right (h2.pow_right _)).eq
  have ha : (d * d') * uvec n d d' = uvec n d d' * (d * d') := by
    apply hcomm_ab
    · exact (Commute.refl d).mul_left hc.symm
    · exact hc.mul_left (Commute.refl d')
  have hb : (d * d'⁻¹) * uvec n d d' = uvec n d d' * (d * d'⁻¹) := by
    apply hcomm_ab
    · exact (Commute.refl d).mul_left (hc.symm.inv_left)
    · exact hc.mul_left ((Commute.refl d').inv_left)
  have hv : (j * j') * uvec n d d' = uvec n d d' * (j * j') :=
    inv_comm_u h (v_inv_d h) (v_inv_d' h)
  have hy : (j * d' * j') * uvec n d d' = uvec n d d' * (j * d' * j') :=
    inv_comm_u h (y_conj_d h) (y_conj_d' h)
  have ht := t_comm_u h
  have hs : (j * j' * t) * uvec n d d' = uvec n d d' * (j * j' * t) := by
    have hvc : Commute (j * j') (uvec n d d') := hv
    have htc : Commute t (uvec n d d') := ht
    exact (hvc.mul_left htc).eq
  have hle : B₁ d d' j j' t ⊔ B₂ d d' t ⊔ zpowers (j * d' * j') ≤
      centralizer ({uvec n d d'} : Set G) := by
    refine sup_le (sup_le (sup_le ?_ ?_) (sup_le ?_ ?_)) ?_
    · rw [Subgroup.zpowers_le]; exact hcu ha
    · rw [Subgroup.zpowers_le]; exact hcu hs
    · rw [Subgroup.zpowers_le]; exact hcu hb
    · rw [Subgroup.zpowers_le]; exact hcu ht
    · rw [Subgroup.zpowers_le]; exact hcu hy
  intro g hg
  exact Subgroup.mem_centralizer_singleton_iff.mp (hle hg)

end Lemma31iCoreB

end CFSG.GH74.GLS.IVK.Proofs2
