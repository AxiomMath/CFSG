module

public import CFSG.LocalAnalysis.ComponentClassification.HallQ8Q

public section

namespace CFSG.ComponentClassification.Foote5.HallGen

open CFSG Subgroup CFSG.ABGLocalTools

variable {G : Type} [Group G] [Finite G] {D : Subgroup G} {c : G}

omit [Finite G] in
theorem zpowers_cjS {v a w : G} (hw : a⁻¹ * v * a = w) : cjS (zpowers v) a = zpowers w := by
  rw [cjS, MonoidHom.map_zpowers]
  simp [← hw]

namespace Q8Cfg

theorem sq_comm_cy (h : Q8Cfg D c) {s : G} (hs : s ∈ normalizer (D : Set G)) :
    (s * s) * cy c = cy c * (s * s) := by
  have hmem : s * cy c * s⁻¹ ∈ zpowers c := conj_K h hs (cy_mem h)
  have hsq : (s * cy c * s⁻¹) * (s * cy c * s⁻¹) = cz c := by
    rw [show s * cy c * s⁻¹ * (s * cy c * s⁻¹) = s * (cy c * cy c) * s⁻¹ by group, cy_mul_cy h]
    exact h.conj_cz_eq s
  rcases eq_cy_or_inv h hmem hsq with e | e
  · have : s * s * cy c * (s * s)⁻¹ = cy c := by
      calc s * s * cy c * (s * s)⁻¹ = s * (s * cy c * s⁻¹) * s⁻¹ := by group
        _ = cy c := by rw [e, e]
    exact mul_inv_eq_iff_eq_mul.mp this
  · have : s * s * cy c * (s * s)⁻¹ = cy c := by
      calc s * s * cy c * (s * s)⁻¹ = s * (s * cy c * s⁻¹) * s⁻¹ := by group
        _ = s * (cy c)⁻¹ * s⁻¹ := by rw [e]
        _ = (s * cy c * s⁻¹)⁻¹ := by group
        _ = cy c := by rw [e, inv_inv]
    exact mul_inv_eq_iff_eq_mul.mp this

theorem pow_two_pow_cy (h : Q8Cfg D c) {e : ℕ} (he : 3 ≤ e) {v : G} (hv : v ∈ zpowers c)
    (hord : orderOf v = 2 ^ e) :
    v ^ (2 ^ (e - 2)) = cy c ∨ v ^ (2 ^ (e - 2)) = (cy c)⁻¹ := by
  have h1 : v ^ (2 ^ (e - 2)) * v ^ (2 ^ (e - 2)) = v ^ (2 ^ (e - 1)) := by
    rw [← pow_add, ← two_mul, ← pow_succ']
    congr 2
    omega
  have h2 : v ^ (2 ^ (e - 1)) * v ^ (2 ^ (e - 1)) = 1 := by
    rw [← pow_add, ← two_mul, ← pow_succ', show e - 1 + 1 = e by omega, ← hord]
    exact pow_orderOf_eq_one v
  have h3 : v ^ (2 ^ (e - 1)) ≠ 1 := by
    intro h'
    have h4 := orderOf_dvd_of_pow_eq_one h'
    rw [hord] at h4
    have h5 := Nat.le_of_dvd (by positivity) h4
    have h6 : 2 ^ (e - 1) < 2 ^ e := Nat.pow_lt_pow_right (by norm_num) (by omega)
    omega
  have hsq : v ^ (2 ^ (e - 2)) * v ^ (2 ^ (e - 2)) = cz c := by
    rcases eq_one_or_eq_cz h.h4 (pow_mem hv _) h2 with e1 | e1
    · exact absurd e1 h3
    · rw [h1, e1]
  exact eq_cy_or_inv h (pow_mem hv _) hsq

omit [Finite G] in
theorem conj_pow' (v a : G) (n : ℕ) : (a⁻¹ * v * a) ^ n = a⁻¹ * v ^ n * a := by
  have := conj_pow (a := a⁻¹) (b := v) (i := n)
  simpa using this

omit [Finite G] in
theorem orderOf_conj' (v a : G) : orderOf (a⁻¹ * v * a) = orderOf v := by
  have h := MulEquiv.orderOf_eq (MulAut.conj a⁻¹) v
  rw [MulAut.conj_apply, inv_inv] at h
  exact h

theorem claim3_pow (h : Q8Cfg D c) {S : Subgroup G} (hS : IsSylowOf 2 S ⊤) (hDS : D ≤ S)
    {e : ℕ} (he : 3 ≤ e) {v a : G} (hv : v ∈ zpowers c) (hord : orderOf v = 2 ^ e)
    (hwS : a⁻¹ * v * a ∈ S) :
    (a⁻¹ * v * a) ^ (2 ^ (e - 2)) = cy c ∨ (a⁻¹ * v * a) ^ (2 ^ (e - 2)) = (cy c)⁻¹ := by
  have hSN := h.le_normalizer hS.isPGroup hDS
  obtain ⟨u, huD, huK⟩ := exists_refl' h
  set w := a⁻¹ * v * a with hw
  set yw := w ^ (2 ^ (e - 2)) with hyw
  have hTh : Th c yw := by
    rw [hyw, hw, conj_pow']
    rcases pow_two_pow_cy h he hv hord with e1 | e1
    · rw [e1]
      exact Th_conj Th_cy a
    · rw [e1]
      have := Th_inv h huD huK (Th_conj (Th_cy (c := c)) a)
      rwa [show (a⁻¹ * cy c * a)⁻¹ = a⁻¹ * (cy c)⁻¹ * a by group] at this
  have hSyw : yw ∈ S := pow_mem hwS _
  have hcomm : yw * cy c = cy c * yw := by
    have hs : w ^ (2 ^ (e - 3)) ∈ normalizer (D : Set G) := hSN (pow_mem hwS _)
    have := sq_comm_cy h hs
    rwa [← pow_add, ← two_mul, ← pow_succ', show e - 3 + 1 = e - 2 by omega] at this
  have hyD : yw ∈ D := c2 h hS hDS hSyw hTh hcomm
  have hywK : yw ∈ zpowers c := sq_cz_mem_K h hyD (Th_sq h hTh)
  exact eq_cy_or_inv h hywK (Th_sq h hTh)

theorem claim3_close (h : Q8Cfg D c) {S : Subgroup G} (hS : IsSylowOf 2 S ⊤) (hDS : D ≤ S)
    {e : ℕ} (he : 3 ≤ e) {v a : G} (hv : v ∈ zpowers c) (hord : orderOf v = 2 ^ e)
    (hwS : a⁻¹ * v * a ∈ S) (hw2K : (a⁻¹ * v * a) * (a⁻¹ * v * a) ∈ zpowers c) :
    a⁻¹ * v * a ∈ D := by
  have hSN := h.le_normalizer hS.isPGroup hDS
  set w := a⁻¹ * v * a with hw
  have hwy : w * cy c = cy c * w := by
    have hc : Commute w (w ^ (2 ^ (e - 2))) := Commute.self_pow w _
    rcases claim3_pow h hS hDS he hv hord hwS with e1 | e1
    · rw [e1] at hc
      exact hc
    · rw [e1] at hc
      have h3 := hc.inv_right
      rw [inv_inv] at h3
      exact h3
  have hword : orderOf w = 2 ^ e := by rw [hw, orderOf_conj', hord]
  have hw2 : w * w ≠ 1 := by
    intro h1
    have h2 : orderOf w ∣ 2 := orderOf_dvd_of_pow_eq_one (by rw [sq]; exact h1)
    rw [hword] at h2
    have h3 := Nat.le_of_dvd (by norm_num) h2
    have h4 : 2 ^ 3 ≤ 2 ^ e := Nat.pow_le_pow_right (by norm_num) he
    omega
  have hnorm := normalizes_zpowers h (hSN hwS) hwy hw2K hw2
  have hVD : zpowers v ≤ D := zpowers_le.mpr ((zpowers_le.mpr h.mem) hv)
  have hSV := le_normalizer_zpowers_K h hSN hv
  have hcj := zpowers_cjS (v := v) (a := a) (w := w) rfl
  have hDN : D ≤ normalizer ((cjS (zpowers v) a : Subgroup G) : Set G) := by
    rw [hcj]
    exact le_normalizer_of_norm hnorm
  have := lemmaW h hS hDS hVD hSV hDN
  rw [hcj] at this
  exact this (mem_zpowers w)

theorem claim3 (h : Q8Cfg D c) {S : Subgroup G} (hS : IsSylowOf 2 S ⊤) (hDS : D ≤ S) :
    ∀ e : ℕ, 3 ≤ e → ∀ {v a : G}, v ∈ zpowers c → orderOf v = 2 ^ e →
      a⁻¹ * v * a ∈ S → a⁻¹ * v * a ∈ D := by
  intro e he
  induction e, he using Nat.le_induction with
  | base =>
    intro v a hv hord hwS
    refine claim3_close h hS hDS le_rfl hv hord hwS ?_
    have := claim3_pow h hS hDS le_rfl hv hord hwS
    rw [show (3 : ℕ) - 2 = 1 by rfl, pow_one] at this
    rw [← sq]
    rcases this with e1 | e1 <;> rw [e1]
    · exact cy_mem h
    · exact inv_mem (cy_mem h)
  | succ e he ih =>
    intro v a hv hord hwS
    refine claim3_close h hS hDS (by omega) hv hord hwS ?_
    set w := a⁻¹ * v * a with hw
    have hv2 : v * v ∈ zpowers c := mul_mem hv hv
    have hord2 : orderOf (v * v) = 2 ^ e := by
      rw [← sq, orderOf_pow_of_dvd (by norm_num)
        (by rw [hord, pow_succ]; exact Dvd.intro_left _ rfl), hord, pow_succ,
        Nat.mul_div_cancel _ two_pos]
    have hwwS : a⁻¹ * (v * v) * a ∈ S := by
      rw [show a⁻¹ * (v * v) * a = w * w by rw [hw]; group]
      exact mul_mem hwS hwS
    have hD2 := ih hv2 hord2 hwwS
    rw [show a⁻¹ * (v * v) * a = w * w by rw [hw]; group] at hD2
    rcases h.dih _ hD2 with h1 | ⟨h1, -⟩
    · exact h1
    · exfalso
      have hword : orderOf w = 2 ^ (e + 1) := by rw [hw, orderOf_conj', hord]
      have h2 : orderOf w ∣ 4 := orderOf_dvd_of_pow_eq_one (by
        rw [show (4 : ℕ) = 2 + 2 by rfl, pow_add, sq]
        rw [show w * w * (w * w) = 1 from h1])
      rw [hword] at h2
      have h3 := Nat.le_of_dvd (by norm_num) h2
      have h4 : 2 ^ 4 ≤ 2 ^ (e + 1) := Nat.pow_le_pow_right (by norm_num) (by omega)
      omega

end Q8Cfg

end CFSG.ComponentClassification.Foote5.HallGen
