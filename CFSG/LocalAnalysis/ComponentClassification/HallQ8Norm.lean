module

public import CFSG.LocalAnalysis.ComponentClassification.HallQ8Fix

public section

namespace CFSG.ComponentClassification.Foote5.HallGen

open CFSG Subgroup CFSG.ABGLocalTools

variable {G : Type} [Group G] [Finite G] {D : Subgroup G} {c : G}

namespace Q8Cfg

theorem cz_mem_zpowers_of_ne_one (h : Q8Cfg D c) {x : G} (hx : x ∈ zpowers c) (hx1 : x ≠ 1) :
    cz c ∈ zpowers x := by
  obtain ⟨m, hm⟩ := h.pow_m
  obtain ⟨i, rfl⟩ := mem_zpowers_iff.mp hx
  have hxm : (c ^ i) ^ (2 ^ m) = 1 := by
    rw [← zpow_natCast, ← zpow_mul, mul_comm, zpow_mul, zpow_natCast, hm, one_zpow]
  obtain ⟨e, -, he⟩ := (Nat.dvd_prime_pow Nat.prime_two).mp (orderOf_dvd_of_pow_eq_one hxm)
  have he1 : e ≠ 0 := by
    rintro rfl
    exact hx1 (orderOf_eq_one_iff.mp (by simpa using he))
  obtain ⟨e', rfl⟩ : ∃ e', e = e' + 1 := ⟨e - 1, by omega⟩
  set x := c ^ i with hxdef
  have h1 : (x ^ (2 ^ e')) * (x ^ (2 ^ e')) = 1 := by
    rw [← pow_add, ← two_mul, ← pow_succ']
    rw [← he]
    exact pow_orderOf_eq_one x
  have h2 : x ^ (2 ^ e') ≠ 1 := by
    intro h3
    have := orderOf_dvd_of_pow_eq_one h3
    rw [he] at this
    have h4 := Nat.le_of_dvd (by positivity) this
    have : 2 ^ e' < 2 ^ (e' + 1) := Nat.pow_lt_pow_right (by norm_num) (by omega)
    omega
  have hK : x ^ (2 ^ e') ∈ zpowers c := pow_mem hx _
  rcases eq_one_or_eq_cz h.h4 hK h1 with h3 | h3
  · exact absurd h3 h2
  · rw [← h3]
    exact pow_mem (mem_zpowers x) _

theorem four_dvd_sub_one (h : Q8Cfg D c) {w : G} {j : ℤ} (hj : w * c * w⁻¹ = c ^ j)
    (hwy : w * cy c * w⁻¹ = cy c) : (4 : ℤ) ∣ j - 1 := by
  obtain ⟨q, hq⟩ := h.h4
  have hq0 : 0 < q := by
    have := h.k_pos
    omega
  have hq4 : orderOf c / 4 = q := by omega
  have h1 : w * cy c * w⁻¹ = c ^ (j * (q : ℤ)) := by
    rw [cy, hq4, ← conj_pow, hj, ← zpow_natCast, ← zpow_mul]
  have h2 : c ^ ((j - 1) * (q : ℤ)) = 1 := by
    rw [sub_mul, zpow_sub, ← h1, hwy, one_mul, cy, hq4, zpow_natCast, mul_inv_cancel]
  have h3 := orderOf_dvd_iff_zpow_eq_one.mpr h2
  rw [hq] at h3
  push_cast at h3
  exact Int.dvd_of_mul_dvd_mul_right (by exact_mod_cast hq0.ne') h3

omit [Finite G] in
theorem commK (_h : Q8Cfg D c) {x x' : G} (hx : x ∈ zpowers c) (hx' : x' ∈ zpowers c) :
    Commute x x' := by
  obtain ⟨i, rfl⟩ := mem_zpowers_iff.mp hx
  obtain ⟨i', rfl⟩ := mem_zpowers_iff.mp hx'
  exact Commute.zpow_zpow_self c i i'

theorem rot_mem_zpowers (h : Q8Cfg D c) {w : G} {j a : ℤ} (hj : w * c * w⁻¹ = c ^ j)
    (ha : j = 4 * a + 1) (hw2K : w * w ∈ zpowers c) (hw2 : w * w ≠ 1) :
    c ^ (j - 1) ∈ zpowers (w * w) := by
  set κ := w * w with hκ
  have hcomm : Commute κ c := (commK h hw2K (mem_zpowers c))
  have h1 : κ * c * κ⁻¹ = c := by rw [hcomm.eq]; group
  have h2 : κ * c * κ⁻¹ = c ^ (j * j) := by
    calc κ * c * κ⁻¹ = w * (w * c * w⁻¹) * w⁻¹ := by rw [hκ]; group
      _ = w * c ^ j * w⁻¹ := by rw [hj]
      _ = (w * c * w⁻¹) ^ j := by rw [conj_zpow]
      _ = c ^ (j * j) := by rw [hj, ← zpow_mul]
  have h3 : c ^ (j * j - 1) = 1 := by rw [zpow_sub, ← h2, h1, zpow_one, mul_inv_cancel]
  have h4 : ((c ^ (j - 1)) ^ (2 : ℤ)) ^ (2 * a + 1) = 1 := by
    rw [← zpow_mul, ← zpow_mul, ← h3]
    congr 1
    rw [ha]
    ring
  have h5 : (c ^ (j - 1)) ^ (2 : ℤ) = 1 :=
    eq_one_of_zpow_odd_K h (zpow_mem (zpow_mem (mem_zpowers c) _) _) ⟨a, rfl⟩ h4
  have h6 : c ^ (j - 1) * c ^ (j - 1) = 1 := by rw [← sq, ← zpow_natCast]; simpa using h5
  rcases eq_one_or_eq_cz h.h4 (zpow_mem (mem_zpowers c) _) h6 with e | e
  · rw [e]
    exact one_mem _
  · rw [e]
    exact h.cz_mem_zpowers_of_ne_one hw2K hw2

theorem refl_mem_zpowers (h : Q8Cfg D c) {w u : G} (hu : u ∈ D) (huK : u ∉ zpowers c)
    {j l a : ℤ} (hj : w * c * w⁻¹ = c ^ j) (hl : w * u * w⁻¹ = c ^ l * u)
    (ha : j = 4 * a + 1) (hw2K : w * w ∈ zpowers c) (hw2 : w * w ≠ 1) :
    c ^ l ∈ zpowers (w * w) := by
  set κ := w * w with hκ
  obtain ⟨s, hs⟩ := mem_zpowers_iff.mp hw2K
  have hu_κ : u * κ * u⁻¹ = κ⁻¹ := by rw [← hs, refl_conj_zpow h hu huK, zpow_neg]
  have hu_κ' : u * κ⁻¹ * u⁻¹ = κ := by
    have : u * κ⁻¹ * u⁻¹ = (u * κ * u⁻¹)⁻¹ := by group
    rw [this, hu_κ, inv_inv]
  have hκu : κ * u * κ⁻¹ = κ * κ * u := by
    calc κ * u * κ⁻¹ = κ * (u * κ⁻¹ * u⁻¹) * u := by group
      _ = κ * κ * u := by rw [hu_κ']
  have hw2u : κ * u * κ⁻¹ = c ^ (j * l) * (c ^ l * u) := by
    calc κ * u * κ⁻¹ = w * (w * u * w⁻¹) * w⁻¹ := by rw [hκ]; group
      _ = w * (c ^ l * u) * w⁻¹ := by rw [hl]
      _ = (w * c ^ l * w⁻¹) * (w * u * w⁻¹) := by group
      _ = c ^ (j * l) * (c ^ l * u) := by rw [← conj_zpow, hj, ← zpow_mul, hl]
  have hκκ : κ * κ = c ^ (j * l + l) := by
    have h1 : κ * κ * u = c ^ (j * l + l) * u := by
      rw [← hκu, hw2u, zpow_add, mul_assoc]
    exact mul_right_cancel h1
  set p := (c ^ l) ^ (2 * a + 1) with hp
  have hpK : p ∈ zpowers c := zpow_mem (zpow_mem (mem_zpowers c) _) _
  have hpp : p * p = κ * κ := by
    rw [hp, ← zpow_add, ← zpow_mul, hκκ]
    congr 1
    rw [ha]
    ring
  have hκK : κ⁻¹ ∈ zpowers c := inv_mem hw2K
  have hsq : (p * κ⁻¹) * (p * κ⁻¹) = 1 := by
    have hc : Commute p κ⁻¹ := commK h hpK hκK
    calc (p * κ⁻¹) * (p * κ⁻¹) = (p * p) * (κ⁻¹ * κ⁻¹) := by
          rw [← sq, hc.mul_pow, sq, sq]
      _ = 1 := by rw [hpp]; group
  have hzκ := h.cz_mem_zpowers_of_ne_one hw2K hw2
  have hpκ : p ∈ zpowers κ := by
    rcases eq_one_or_eq_cz h.h4 (mul_mem hpK hκK) hsq with e | e
    · have : p = κ := mul_inv_eq_one.mp e
      rw [this]
      exact mem_zpowers κ
    · have : p = cz c * κ := by rw [← e]; group
      rw [this]
      exact mul_mem hzκ (mem_zpowers κ)
  have hcl : c ^ l ∈ zpowers p := h.mem_zpowers_zpow_odd_K (zpow_mem (mem_zpowers c) _) ⟨a, rfl⟩
  exact (zpowers_le.mpr hpκ) hcl

theorem normalizes_zpowers (h : Q8Cfg D c) {w : G} (hw : w ∈ normalizer (D : Set G))
    (hwy : w * cy c = cy c * w) (hw2K : w * w ∈ zpowers c) (hw2 : w * w ≠ 1) :
    ∀ d ∈ D, d * w * d⁻¹ ∈ zpowers w := by
  obtain ⟨u, huD, huK⟩ := exists_refl' h
  obtain ⟨j, hj⟩ := conj_c h hw
  obtain ⟨l, hl⟩ := conj_refl h hw huD huK
  have hwy' : w * cy c * w⁻¹ = cy c := by rw [hwy]; group
  obtain ⟨a, ha⟩ : ∃ a : ℤ, j = 4 * a + 1 := by
    obtain ⟨a, ha⟩ := four_dvd_sub_one h hj hwy'
    exact ⟨a, by omega⟩
  have hκw : zpowers (w * w) ≤ zpowers w :=
    zpowers_le.mpr ⟨2, by show w ^ (2 : ℤ) = w * w; exact zpow_two w⟩
  have hA : c ^ (j - 1) ∈ zpowers w := hκw (rot_mem_zpowers h hj ha hw2K hw2)
  have hB : c ^ l ∈ zpowers w := hκw (refl_mem_zpowers h huD huK hj hl ha hw2K hw2)
  have hcw : ∀ i : ℤ, c ^ i * w * (c ^ i)⁻¹ = c ^ ((j - 1) * (-i)) * w := by
    intro i
    have h1 : w * c ^ (-i) * w⁻¹ = c ^ (j * (-i)) := by rw [← conj_zpow, hj, ← zpow_mul]
    calc c ^ i * w * (c ^ i)⁻¹ = c ^ i * (w * c ^ (-i) * w⁻¹) * w := by rw [zpow_neg]; group
      _ = c ^ i * c ^ (j * (-i)) * w := by rw [h1]
      _ = c ^ ((j - 1) * (-i)) * w := by
          rw [← zpow_add]
          congr 2
          ring
  have huw : u * w * u⁻¹ = (c ^ l)⁻¹ * w := by
    have : c ^ l * (u * w * u⁻¹) = w := by
      calc c ^ l * (u * w * u⁻¹) = (c ^ l * u) * w * u⁻¹ := by group
        _ = (w * u * w⁻¹) * w * u⁻¹ := by rw [hl]
        _ = w := by group
    calc u * w * u⁻¹ = (c ^ l)⁻¹ * (c ^ l * (u * w * u⁻¹)) := by group
      _ = (c ^ l)⁻¹ * w := by rw [this]
  have hrot : ∀ i : ℤ, c ^ ((j - 1) * (-i)) ∈ zpowers w := fun i => by
    rw [zpow_mul]
    exact zpow_mem hA _
  intro d hd
  rcases refl_cases h huD huK hd with hdK | ⟨i, rfl⟩
  · obtain ⟨i, rfl⟩ := mem_zpowers_iff.mp hdK
    rw [hcw]
    exact mul_mem (hrot i) (mem_zpowers w)
  · have key : (c ^ i * u) * w * (c ^ i * u)⁻¹ =
        (c ^ l)⁻¹ * (c ^ ((j - 1) * (-i)) * w) := by
      have hcm : Commute (c ^ i) (c ^ l)⁻¹ := (Commute.zpow_zpow_self c i l).inv_right
      calc (c ^ i * u) * w * (c ^ i * u)⁻¹ = c ^ i * (u * w * u⁻¹) * (c ^ i)⁻¹ := by group
        _ = c ^ i * ((c ^ l)⁻¹ * w) * (c ^ i)⁻¹ := by rw [huw]
        _ = (c ^ i * (c ^ l)⁻¹) * w * (c ^ i)⁻¹ := by group
        _ = ((c ^ l)⁻¹ * c ^ i) * w * (c ^ i)⁻¹ := by rw [hcm.eq]
        _ = (c ^ l)⁻¹ * (c ^ i * w * (c ^ i)⁻¹) := by group
        _ = (c ^ l)⁻¹ * (c ^ ((j - 1) * (-i)) * w) := by rw [hcw]
    rw [key]
    exact mul_mem (inv_mem hB) (mul_mem (hrot i) (mem_zpowers w))

theorem sq_cz_mem_K (h : Q8Cfg D c) {x : G} (hx : x ∈ D) (hx2 : x * x = cz c) :
    x ∈ zpowers c := by
  by_contra hK
  exact cz_ne_one' h (hx2.symm.trans (refl_data h hx hK).1)

omit [Finite G] in
theorem le_normalizer_of_norm {w : G} (hD : ∀ d ∈ D, d * w * d⁻¹ ∈ zpowers w) :
    D ≤ normalizer (zpowers w : Set G) := by
  refine le_normalizer_of_forall fun p hp v hv => ?_
  obtain ⟨i, rfl⟩ := mem_zpowers_iff.mp hv
  rw [← conj_zpow]
  exact zpow_mem (hD p hp) i

omit [Finite G] in
theorem zpowers_cjS_cy {g w : G} (hg : g⁻¹ * cy c * g = w) :
    cjS (zpowers (cy c)) g = zpowers w := by
  rw [cjS, MonoidHom.map_zpowers]
  simp [← hg]

theorem c2 (h : Q8Cfg D c) {S : Subgroup G} (hS : IsSylowOf 2 S ⊤) (hDS : D ≤ S) {w : G}
    (hwS : w ∈ S) (hwTh : Th c w) (hwy : w * cy c = cy c * w) : w ∈ D := by
  have hSN := h.le_normalizer hS.isPGroup hDS
  have hw2 : w * w = cz c := Th_sq h hwTh
  have hnorm := normalizes_zpowers h (hSN hwS) hwy (by rw [hw2]; exact cz_mem' h)
    (by rw [hw2]; exact cz_ne_one' h)
  obtain ⟨g, hg⟩ := hwTh
  have hVD : zpowers (cy c) ≤ D := zpowers_le.mpr ((zpowers_le.mpr h.mem) (cy_mem h))
  have hSV := le_normalizer_zpowers_K h hSN (cy_mem h)
  have hcj := zpowers_cjS_cy hg
  have hDN : D ≤ normalizer ((cjS (zpowers (cy c)) g : Subgroup G) : Set G) := by
    rw [hcj]
    exact le_normalizer_of_norm hnorm
  have := lemmaW h hS hDS hVD hSV hDN
  rw [hcj] at this
  exact this (mem_zpowers w)

theorem cc (h : Q8Cfg D c) {S : Subgroup G} (hS : IsSylowOf 2 S ⊤) (hDS : D ≤ S) {q w : G}
    (hq : Th c q) (hw : Th c w) (hqw : q * w = w * q) : q = w ∨ q = w⁻¹ := by
  have hSN := h.le_normalizer hS.isPGroup hDS
  obtain ⟨k, hk⟩ := hw
  have hq2 := Th_sq h hq
  have hw2 := Th_sq h ⟨k, hk⟩
  have hq4 : q ^ (2 ^ 2) = 1 := by
    rw [show (2 : ℕ) ^ 2 = 2 + 2 by rfl, pow_add, sq, hq2]
    exact cz_mul_cz h.h4
  have hw4 : w ^ (2 ^ 2) = 1 := by
    rw [show (2 : ℕ) ^ 2 = 2 + 2 by rfl, pow_add, sq, hw2]
    exact cz_mul_cz h.h4
  have hqc : Commute q w := hqw
  have hR2 := isPGroup_sup_zpowers hqc hq4 hw4
  have hVD : zpowers (cy c) ≤ D := zpowers_le.mpr ((zpowers_le.mpr h.mem) (cy_mem h))
  have hSV := le_normalizer_zpowers_K h hSN (cy_mem h)
  have hcj := zpowers_cjS_cy hk
  have hRN : (zpowers q ⊔ zpowers w : Subgroup G) ≤
      normalizer ((cjS (zpowers (cy c)) k : Subgroup G) : Set G) := by
    rw [hcj]
    refine sup_le ?_ Subgroup.le_normalizer
    refine le_normalizer_of_forall fun p hp v hv => ?_
    obtain ⟨i, rfl⟩ := mem_zpowers_iff.mp hp
    obtain ⟨j, rfl⟩ := mem_zpowers_iff.mp hv
    have : Commute (q ^ i) (w ^ j) := (hqc.zpow_left i).zpow_right j
    rw [this.eq, mul_inv_cancel_right]
    exact zpow_mem (mem_zpowers w) j
  obtain ⟨t, htV, hRt⟩ := exists_conj_sylow hS hSV k hR2 hRN
  have hqS : t * q * t⁻¹ ∈ S := mem_cjS.mp (hRt (mem_sup_left (mem_zpowers q)))
  have hwV : t * w * t⁻¹ ∈ zpowers (cy c) := by
    have : w ∈ cjS (zpowers (cy c)) k := by
      rw [hcj]
      exact mem_zpowers w
    rw [← htV] at this
    exact mem_cjS.mp this
  have hq₀Th : Th c (t * q * t⁻¹) := by
    have := Th_conj hq t⁻¹
    rwa [inv_inv] at this
  have hw₀Th : Th c (t * w * t⁻¹) := by
    have := Th_conj ⟨k, hk⟩ t⁻¹
    rwa [inv_inv] at this
  have hw₀K : t * w * t⁻¹ ∈ zpowers c := (zpowers_le.mpr (cy_mem h)) hwV
  have hw₀2 := Th_sq h hw₀Th
  have hq₀2 := Th_sq h hq₀Th
  have hcomm₀ : (t * q * t⁻¹) * (t * w * t⁻¹) = (t * w * t⁻¹) * (t * q * t⁻¹) := by
    calc (t * q * t⁻¹) * (t * w * t⁻¹) = t * (q * w) * t⁻¹ := by group
      _ = t * (w * q) * t⁻¹ := by rw [hqw]
      _ = (t * w * t⁻¹) * (t * q * t⁻¹) := by group
  have hq₀y : (t * q * t⁻¹) * cy c = cy c * (t * q * t⁻¹) := by
    rcases eq_cy_or_inv h hw₀K hw₀2 with e | e
    · rwa [e] at hcomm₀
    · rw [e] at hcomm₀
      have h3 : Commute (t * q * t⁻¹) (cy c)⁻¹ := hcomm₀
      have h4 := h3.inv_right
      rw [inv_inv] at h4
      exact h4.eq
  have hq₀D : t * q * t⁻¹ ∈ D := c2 h hS hDS hqS hq₀Th hq₀y
  have hq₀K : t * q * t⁻¹ ∈ zpowers c := sq_cz_mem_K h hq₀D hq₀2
  have hcases : t * q * t⁻¹ = t * w * t⁻¹ ∨ t * q * t⁻¹ = (t * w * t⁻¹)⁻¹ := by
    rcases eq_cy_or_inv h hq₀K hq₀2 with e1 | e1 <;> rcases eq_cy_or_inv h hw₀K hw₀2 with e2 | e2
    · left
      rw [e1, e2]
    · right
      rw [e1, e2, inv_inv]
    · right
      rw [e1, e2]
    · left
      rw [e1, e2]
  rcases hcases with e | e
  · left
    exact mul_left_cancel (mul_right_cancel e)
  · right
    have : t * q * t⁻¹ = t * w⁻¹ * t⁻¹ := by rw [e]; group
    exact mul_left_cancel (mul_right_cancel this)

end Q8Cfg

end CFSG.ComponentClassification.Foote5.HallGen
