module

public import CFSG.LocalAnalysis.ComponentClassification.Foote5HallGen

public section

namespace CFSG.ComponentClassification.Foote5.HallGen

open CFSG Subgroup CFSG.ABGLocalTools

variable {G : Type} [Group G] {D : Subgroup G} {c : G}

structure Q8Cfg (D : Subgroup G) (c : G) : Prop where
  two_pow : ∃ m : ℕ, 3 ≤ m ∧ orderOf c = 2 ^ m
  mem : c ∈ D
  card : Nat.card D = 2 * orderOf c
  dih : ∀ x ∈ D, x ∈ zpowers c ∨ (x * x = 1 ∧ x * c * x⁻¹ = c⁻¹)
  sic : ∀ x ∈ normalizer (D : Set G), x ∉ D → orderOf x = 2 →
    ∀ d ∈ D, orderOf d = 2 → ∀ g : G, g⁻¹ * x * g ≠ d
  central : ∀ g : G, g * cz c = cz c * g

@[expose] noncomputable def cy (c : G) : G := c ^ (orderOf c / 4)

omit [Group G] in
theorem mem_zpowers_zpow_odd [Group G] (x : G) (m : ℕ) (hx : x ^ (2 ^ m) = 1) (o : ℤ)
    (ho : Odd o) : x ∈ zpowers (x ^ o) := by
  have hc : IsCoprime o ((2 : ℤ) ^ m) := by
    apply IsCoprime.pow_right
    rcases ho with ⟨t, rfl⟩
    exact ⟨1, -t, by ring⟩
  obtain ⟨a, b, hab⟩ := hc
  refine mem_zpowers_iff.mpr ⟨a, ?_⟩
  have h2 : x ^ ((2 : ℤ) ^ m) = 1 := by
    have := zpow_natCast x (2 ^ m)
    push_cast at this
    rw [this]
    exact hx
  calc (x ^ o) ^ a = x ^ (o * a) := by rw [← zpow_mul]
    _ = x ^ (a * o + b * 2 ^ m) * (x ^ ((2 : ℤ) ^ m)) ^ (-b) := by
        rw [← zpow_mul, ← zpow_add]
        congr 1
        ring
    _ = x := by rw [hab, h2]; simp

omit [Group G] in
theorem eq_one_of_zpow_odd [Group G] (x : G) (m : ℕ) (hx : x ^ (2 ^ m) = 1) (o : ℤ)
    (ho : Odd o) (h : x ^ o = 1) : x = 1 := by
  have := mem_zpowers_zpow_odd x m hx o ho
  rw [h] at this
  simpa using this

namespace Q8Cfg

variable [Finite G]

omit [Finite G] in
theorem pow_m (h : Q8Cfg D c) : ∃ m : ℕ, c ^ (2 ^ m) = 1 := by
  obtain ⟨m, -, hk⟩ := h.two_pow
  exact ⟨m, by rw [← hk]; exact pow_orderOf_eq_one c⟩

omit [Finite G] in
theorem h8 (h : Q8Cfg D c) : 8 ∣ orderOf c := by
  obtain ⟨m, hm, hk⟩ := h.two_pow
  rw [hk, show m = (m - 3) + 3 by omega, pow_add]
  exact Dvd.intro_left _ rfl

omit [Finite G] in
theorem h4 (h : Q8Cfg D c) : 4 ∣ orderOf c := (by norm_num : (4 : ℕ) ∣ 8).trans h.h8

theorem k_pos (_h : Q8Cfg D c) : 0 < orderOf c := orderOf_pos c

omit [Finite G] in
theorem eq_one_of_zpow_odd_K (h : Q8Cfg D c) {x : G} (hx : x ∈ zpowers c) {o : ℤ}
    (ho : Odd o) (hxo : x ^ o = 1) : x = 1 := by
  obtain ⟨m, hm⟩ := h.pow_m
  obtain ⟨i, rfl⟩ := mem_zpowers_iff.mp hx
  refine eq_one_of_zpow_odd _ m ?_ o ho hxo
  rw [← zpow_natCast, ← zpow_mul, mul_comm, zpow_mul, zpow_natCast, hm, one_zpow]

omit [Finite G] in
theorem mem_zpowers_zpow_odd_K (h : Q8Cfg D c) {x : G} (hx : x ∈ zpowers c) {o : ℤ}
    (ho : Odd o) : x ∈ zpowers (x ^ o) := by
  obtain ⟨m, hm⟩ := h.pow_m
  obtain ⟨i, rfl⟩ := mem_zpowers_iff.mp hx
  refine mem_zpowers_zpow_odd _ m ?_ o ho
  rw [← zpow_natCast, ← zpow_mul, mul_comm, zpow_mul, zpow_natCast, hm, one_zpow]

omit [Finite G] in
theorem cz_mem' (_h : Q8Cfg D c) : cz c ∈ zpowers c := pow_mem (mem_zpowers c) _

omit [Finite G] in
theorem cy_mem (_h : Q8Cfg D c) : cy c ∈ zpowers c := pow_mem (mem_zpowers c) _

omit [Finite G] in
theorem cy_mul_cy (h : Q8Cfg D c) : cy c * cy c = cz c := by
  obtain ⟨q, hq⟩ := h.h4
  rw [cy, cz, ← pow_add, hq, show 4 * q / 4 = q by omega, show 4 * q / 2 = q + q by omega]

theorem cz_ne_one' (h : Q8Cfg D c) : cz c ≠ 1 := cz_ne_one h.h4

theorem cy_mul_cy_ne_one (h : Q8Cfg D c) : cy c * cy c ≠ 1 := by
  rw [cy_mul_cy h]
  exact cz_ne_one' h

omit [Finite G] in
theorem cy_inv (h : Q8Cfg D c) : (cy c)⁻¹ = cy c * cz c := by
  refine inv_eq_of_mul_eq_one_right ?_
  rw [← mul_assoc, cy_mul_cy h]
  exact cz_mul_cz h.h4

omit [Finite G] in
theorem cz_inv' (h : Q8Cfg D c) : (cz c)⁻¹ = cz c := cz_inv h.h4

omit [Finite G] in
theorem comm_cy (_h : Q8Cfg D c) {x : G} (hx : x ∈ zpowers c) : Commute x (cy c) := by
  obtain ⟨i, rfl⟩ := mem_zpowers_iff.mp hx
  exact Commute.zpow_left (Commute.pow_right (Commute.refl c) _) i

theorem eq_cy_or_inv (h : Q8Cfg D c) {x : G} (hx : x ∈ zpowers c) (hx2 : x * x = cz c) :
    x = cy c ∨ x = (cy c)⁻¹ := by
  have hcomm := comm_cy h hx
  have hxy : (x * (cy c)⁻¹) * (x * (cy c)⁻¹) = 1 := by
    rw [← sq, hcomm.inv_right.mul_pow, sq, sq, hx2, ← mul_inv_rev, cy_mul_cy h, cz_inv' h]
    exact cz_mul_cz h.h4
  have hmem : x * (cy c)⁻¹ ∈ zpowers c := mul_mem hx (inv_mem (cy_mem h))
  rcases eq_one_or_eq_cz h.h4 hmem hxy with h1 | h1
  · left
    exact mul_inv_eq_one.mp h1
  · right
    have : x = cz c * cy c := by rw [← h1]; group
    rw [this, cy_inv h]
    exact (comm_cy h (cz_mem' h)).symm.eq.symm

omit [Finite G] in
theorem refl_data (h : Q8Cfg D c) {u : G} (hu : u ∈ D) (huK : u ∉ zpowers c) :
    u * u = 1 ∧ u * c * u⁻¹ = c⁻¹ := by
  rcases h.dih u hu with h1 | h1
  · exact absurd h1 huK
  · exact h1

theorem exists_refl' (h : Q8Cfg D c) : ∃ u ∈ D, u ∉ zpowers c := exists_refl h.card

omit [Finite G] in
theorem refl_inv (h : Q8Cfg D c) {u : G} (hu : u ∈ D) (huK : u ∉ zpowers c) : u⁻¹ = u :=
  inv_eq_of_mul_eq_one_right (refl_data h hu huK).1

theorem c_mul_c_ne_one (h : Q8Cfg D c) : c * c ≠ 1 := by
  intro h1
  have h2 : orderOf c ∣ 2 := orderOf_dvd_of_pow_eq_one (by rw [sq]; exact h1)
  have h3 := Nat.le_of_dvd (by norm_num) h2
  have h4 := h.k_pos
  have h5 := h.h8
  omega

theorem refl_cases (h : Q8Cfg D c) {u : G} (hu : u ∈ D) (huK : u ∉ zpowers c) {x : G}
    (hx : x ∈ D) : x ∈ zpowers c ∨ ∃ i : ℤ, x = c ^ i * u := by
  by_cases hxK : x ∈ zpowers c
  · exact Or.inl hxK
  · right
    obtain ⟨hx2, hxc⟩ := refl_data h hx hxK
    obtain ⟨hu2, huc⟩ := refl_data h hu huK
    have hxu : x * u⁻¹ ∈ zpowers c := by
      by_contra hn
      obtain ⟨-, h3⟩ := refl_data h (mul_mem hx (inv_mem hu)) hn
      have e1 : u⁻¹ * c * u = c⁻¹ := by
        have hui := refl_inv h hu huK
        rw [hui]
        rwa [hui] at huc
      have h4 : (x * u⁻¹) * c * (x * u⁻¹)⁻¹ = c := by
        calc (x * u⁻¹) * c * (x * u⁻¹)⁻¹ = x * (u⁻¹ * c * u) * x⁻¹ := by group
          _ = x * c⁻¹ * x⁻¹ := by rw [e1]
          _ = (x * c * x⁻¹)⁻¹ := by group
          _ = c := by rw [hxc, inv_inv]
      have hcc : c = c⁻¹ := h4.symm.trans h3
      exact c_mul_c_ne_one h (mul_eq_one_iff_eq_inv.mpr hcc)
    obtain ⟨i, hi⟩ := mem_zpowers_iff.mp hxu
    refine ⟨i, ?_⟩
    rw [hi]
    group

theorem conj_c (h : Q8Cfg D c) {w : G} (hw : w ∈ normalizer (D : Set G)) :
    ∃ j : ℤ, w * c * w⁻¹ = c ^ j := by
  obtain ⟨j, hj⟩ := mem_zpowers_iff.mp (conj_c_mem h.dih h.h4 hw h.mem)
  exact ⟨j, hj.symm⟩

theorem conj_K (h : Q8Cfg D c) {w : G} (hw : w ∈ normalizer (D : Set G)) {x : G}
    (hx : x ∈ zpowers c) : w * x * w⁻¹ ∈ zpowers c := by
  obtain ⟨i, rfl⟩ := mem_zpowers_iff.mp hx
  obtain ⟨j, hj⟩ := conj_c h hw
  rw [← conj_zpow, hj, ← zpow_mul]
  exact zpow_mem (mem_zpowers c) _

theorem conj_K' (h : Q8Cfg D c) {w : G} (hw : w ∈ normalizer (D : Set G)) {x : G}
    (hx : x ∈ zpowers c) : w⁻¹ * x * w ∈ zpowers c := by
  have := conj_K h (inv_mem hw) hx
  rwa [inv_inv] at this

theorem conj_refl (h : Q8Cfg D c) {w : G} (hw : w ∈ normalizer (D : Set G)) {u : G}
    (hu : u ∈ D) (huK : u ∉ zpowers c) : ∃ l : ℤ, w * u * w⁻¹ = c ^ l * u := by
  have hmem : w * u * w⁻¹ ∈ D := (mem_normalizer_iff.mp hw u).mp hu
  rcases refl_cases h hu huK hmem with h1 | ⟨l, hl⟩
  · exfalso
    apply huK
    have := conj_K' h hw h1
    rwa [show w⁻¹ * (w * u * w⁻¹) * w = u by group] at this
  · exact ⟨l, hl⟩

omit [Finite G] in
theorem refl_conj_zpow (h : Q8Cfg D c) {u : G} (hu : u ∈ D) (huK : u ∉ zpowers c) (i : ℤ) :
    u * c ^ i * u⁻¹ = c ^ (-i) := by
  rw [← conj_zpow, (refl_data h hu huK).2, inv_zpow']

end Q8Cfg

end CFSG.ComponentClassification.Foote5.HallGen
