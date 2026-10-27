module

public import CFSG.GH74.GLS.C3.Layer1.St1P89Basic

public section

namespace CFSG.GH74.GLS.C3.Layer1.P89

open Subgroup CFSG.ABGLocalTools CFSG.GH74.GLS

structure IsD8 {G : Type} [Group G] (P : Subgroup G) (r s z : G) : Prop where
  r_mem : r ∈ P
  s_mem : s ∈ P
  r4 : r ^ 4 = 1
  s2 : s ^ 2 = 1
  srs : s * r * s⁻¹ = r⁻¹
  r2_ne : r ^ 2 ≠ 1
  z_eq : z = r ^ 2
  P_gen : ∀ p ∈ P, ∃ i j : ℕ, p = r ^ i * s ^ j

variable {G : Type} [Group G] {P : Subgroup G} {r s z : G}

theorem Cfg89T.isD8 {T Q : Subgroup G} {u x f : G} [Finite G] (c : Cfg89T G T P Q u z x f r s) : IsD8 P r s z :=
  ⟨c.r_mem, c.s_mem, c.r4, c.s2, c.srs, c.r2_ne, c.z_eq, c.P_gen⟩

theorem IsD8.conj (d : IsD8 P r s z) (a : G) :
    IsD8 (conjSub a P) (a * r * a⁻¹) (a * s * a⁻¹) (a * z * a⁻¹) where
  r_mem := conj_mem_conjSub d.r_mem
  s_mem := conj_mem_conjSub d.s_mem
  r4 := by rw [conj_pow, d.r4]; group
  s2 := by rw [conj_pow, d.s2]; group
  srs := by
    have h1 : a * s * a⁻¹ * (a * r * a⁻¹) * (a * s * a⁻¹)⁻¹ = a * (s * r * s⁻¹) * a⁻¹ := by group
    rw [h1, d.srs]; group
  r2_ne := by
    intro h
    apply d.r2_ne
    have : a * r ^ 2 * a⁻¹ = 1 := by rw [← conj_pow]; exact h
    calc r ^ 2 = a⁻¹ * (a * r ^ 2 * a⁻¹) * a := by group
      _ = 1 := by rw [this]; group
  z_eq := by rw [d.z_eq, conj_pow]
  P_gen := by
    intro p hp
    obtain ⟨q, hq, rfl⟩ := mem_conjSub.mp hp
    obtain ⟨i, j, rfl⟩ := d.P_gen q hq
    exact ⟨i, j, by rw [show a * (r ^ i * s ^ j) * a⁻¹ = (a * r * a⁻¹) ^ i * (a * s * a⁻¹) ^ j by
      rw [conj_pow, conj_pow]; group]⟩

theorem IsD8.z_sq (d : IsD8 P r s z) : z ^ 2 = 1 := by
  rw [d.z_eq, ← pow_mul]; exact d.r4

theorem IsD8.z_ne_one (d : IsD8 P r s z) : z ≠ 1 := by
  rw [d.z_eq]; exact d.r2_ne

theorem IsD8.z_mem (d : IsD8 P r s z) : z ∈ P := by
  rw [d.z_eq]; exact P.pow_mem d.r_mem 2

theorem IsD8.r_inv (d : IsD8 P r s z) : r⁻¹ = r ^ 3 := by
  have : r * r ^ 3 = 1 := by rw [← pow_succ']; exact d.r4
  exact inv_eq_of_mul_eq_one_right this

theorem IsD8.s_r (d : IsD8 P r s z) : s * r = r ^ 3 * s := by
  have h := d.srs
  rw [d.r_inv] at h
  calc s * r = (s * r * s⁻¹) * s := by group
    _ = r ^ 3 * s := by rw [h]

theorem IsD8.z_comm_s (d : IsD8 P r s z) : z * s = s * z := by
  have h1 : s * r ^ 2 * s⁻¹ = r ^ 2 := by
    have : s * r ^ 2 * s⁻¹ = (s * r * s⁻¹) ^ 2 := (conj_pow).symm
    rw [this, d.srs, d.r_inv]
    calc (r ^ 3) ^ 2 = r ^ 4 * r ^ 2 := by group
      _ = r ^ 2 := by rw [d.r4, one_mul]
  rw [mul_inv_eq_iff_eq_mul] at h1
  rw [d.z_eq]; exact h1.symm

theorem IsD8.s_r2 (d : IsD8 P r s z) : s * r ^ 2 = r ^ 2 * s := by
  have h := d.z_comm_s
  rw [d.z_eq] at h
  exact h.symm

theorem IsD8.s_r3 (d : IsD8 P r s z) : s * r ^ 3 = r * s := by
  calc s * r ^ 3 = s * r ^ 2 * r := by group
    _ = r ^ 2 * s * r := by rw [d.s_r2]
    _ = r ^ 2 * (s * r) := by group
    _ = r ^ 2 * (r ^ 3 * s) := by rw [d.s_r]
    _ = r ^ 5 * s := by group
    _ = r * s := by
      have : r ^ 5 = r ^ 4 * r := by group
      rw [this, d.r4, one_mul]

theorem IsD8.P_inv (d : IsD8 P r s z) {p : G} (hp : p ∈ P) (hp2 : p ^ 2 = 1) :
    p = 1 ∨ p = z ∨ p = s ∨ p = z * s ∨ p = r * s ∨ p = z * (r * s) := by
  obtain ⟨i, j, rfl⟩ := d.P_gen p hp
  have hz : z = r ^ 2 := d.z_eq
  rw [pow_eq_pow_mod i d.r4, pow_eq_pow_mod j d.s2] at hp2 ⊢
  have hi : i % 4 < 4 := Nat.mod_lt _ (by norm_num)
  have hj : j % 2 < 2 := Nat.mod_lt _ (by norm_num)
  generalize i % 4 = a at hi hp2 ⊢
  generalize j % 2 = b at hj hp2 ⊢
  interval_cases a <;> interval_cases b <;> simp at hp2 ⊢
  · exact absurd hp2 d.r2_ne
  · exact Or.inr (Or.inl hz.symm)
  · exact Or.inr (Or.inr (Or.inr (Or.inl hz.symm)))
  · exfalso
    apply d.r2_ne
    have : (r ^ 3) ^ 2 = r ^ 2 := by
      calc (r ^ 3) ^ 2 = r ^ 4 * r ^ 2 := by group
        _ = r ^ 2 := by rw [d.r4, one_mul]
    rw [← this]; exact hp2
  · right; right; right; right; right
    rw [hz]; group

theorem IsD8.r_ne_inv (d : IsD8 P r s z) : r ≠ r⁻¹ := by
  intro h
  apply d.r2_ne
  calc r ^ 2 = r * r := sq r
    _ = r * r⁻¹ := by rw [← h]
    _ = 1 := mul_inv_cancel r

theorem IsD8.s_ne_one (d : IsD8 P r s z) : s ≠ 1 := by
  intro h
  apply d.r_ne_inv
  have := d.srs
  rwa [h, inv_one, one_mul, mul_one] at this

theorem IsD8.s_ne_z (d : IsD8 P r s z) : s ≠ z := by
  intro h
  apply d.r_ne_inv
  have hzr : z * r = r * z := by rw [d.z_eq]; group
  have := d.srs
  rw [h] at this
  calc r = z * r * z⁻¹ := by rw [hzr]; group
    _ = r⁻¹ := this

theorem IsD8.rs_sq (d : IsD8 P r s z) : (r * s) ^ 2 = 1 := by
  have h : s * r * s⁻¹ = r⁻¹ := d.srs
  calc (r * s) ^ 2 = r * s * (r * s) := sq _
    _ = r * (s * r * s⁻¹) * (s * s) := by group
    _ = r * r⁻¹ * (s * s) := by rw [h]
    _ = 1 := by rw [mul_inv_cancel, one_mul, ← sq, d.s2]

theorem IsD8.key_r2 (d : IsD8 P r s z) {k : ℕ} (h : r ^ k * s = r ^ (k + 2) * s) : False := by
  have h1 : r ^ k = r ^ (k + 2) := mul_right_cancel h
  apply d.r2_ne
  have : r ^ k * 1 = r ^ k * r ^ 2 := by rw [mul_one, ← pow_add]; exact h1
  exact (mul_left_cancel this).symm

theorem IsD8.s_comm_r_false (d : IsD8 P r s z) (h : s * r = r * s) : False := by
  apply d.key_r2 (k := 1)
  calc r ^ 1 * s = s * r := by rw [pow_one, h]
    _ = r ^ 3 * s := d.s_r
    _ = r ^ (1 + 2) * s := rfl

theorem IsD8.P_center (d : IsD8 P r s z) {p : G} (hp : p ∈ P)
    (hc : ∀ p' ∈ P, p * p' = p' * p) : p = 1 ∨ p = z := by
  obtain ⟨i, j, rfl⟩ := d.P_gen p hp
  have h1 := hc r d.r_mem
  have h2 := hc s d.s_mem
  rw [pow_eq_pow_mod i d.r4, pow_eq_pow_mod j d.s2] at h1 h2 ⊢
  have hi : i % 4 < 4 := Nat.mod_lt _ (by norm_num)
  have hj : j % 2 < 2 := Nat.mod_lt _ (by norm_num)
  generalize i % 4 = a at hi h1 h2 ⊢
  generalize j % 2 = b at hj h1 h2 ⊢
  have hz : z = r ^ 2 := d.z_eq
  have hsr := d.s_r
  have hsr3 := d.s_r3
  have hr4 := d.r4
  interval_cases a <;> interval_cases b <;> simp at h1 h2 ⊢
  · exact (d.s_comm_r_false h1).elim
  · exact (d.s_comm_r_false h2.symm).elim
  · apply (d.s_comm_r_false _).elim
    have h3 : r * (s * r) = r * (r * s) := by rw [← mul_assoc]; exact h1
    exact mul_left_cancel h3
  · exact Or.inr hz.symm
  · exfalso
    apply d.key_r2 (k := 1)
    calc r ^ 1 * s = r ^ 5 * s := by
          have : r ^ 5 = r ^ 4 * r := by group
          rw [this, hr4, one_mul, pow_one]
      _ = r ^ 2 * (r ^ 3 * s) := by group
      _ = r ^ 2 * (s * r) := by rw [hsr]
      _ = r ^ 2 * s * r := by group
      _ = r * (r ^ 2 * s) := h1
      _ = r ^ 3 * s := by group
      _ = r ^ (1 + 2) * s := rfl
  · exfalso
    apply d.key_r2 (k := 1)
    calc r ^ 1 * s = s * r ^ 3 := by rw [pow_one, hsr3]
      _ = r ^ 3 * s := h2.symm
      _ = r ^ (1 + 2) * s := rfl
  · exfalso
    apply d.key_r2 (k := 0)
    calc r ^ 0 * s = r * (r ^ 3 * s) := by
          have : r * r ^ 3 = r ^ 4 := by group
          rw [← mul_assoc, this, hr4]; simp
      _ = r ^ 3 * s * r := h1.symm
      _ = r ^ 3 * (s * r) := by group
      _ = r ^ 3 * (r ^ 3 * s) := by rw [hsr]
      _ = r ^ 6 * s := by group
      _ = r ^ (0 + 2) * s := by
          have : r ^ 6 = r ^ 4 * r ^ 2 := by group
          rw [this, hr4, one_mul]

theorem IsD8.sq_table (d : IsD8 P r s z) (a b : ℕ) (ha : a < 4) (hb : b < 2) :
    ((r ^ a * s ^ b) ^ 2 = 1 ∧ (a = 0 ∨ a = 2 ∨ b = 1)) ∨ ((r ^ a * s ^ b) ^ 2 = z ∧ b = 0 ∧ (a = 1 ∨ a = 3)) := by
  have hz : z = r ^ 2 := d.z_eq
  have hr4 := d.r4
  have hs2 := d.s2
  have hsr := d.s_r
  have hsr2 := d.s_r2
  have hsr3 := d.s_r3
  interval_cases a <;> interval_cases b
  · left; simp
  · left; refine ⟨?_, by simp⟩; simpa using hs2
  · right; refine ⟨?_, rfl, by simp⟩; simp [sq, hz]
  · left; refine ⟨?_, by simp⟩; simpa using d.rs_sq
  · left; refine ⟨?_, by simp⟩; simp only [pow_zero, mul_one]; rw [← pow_mul]; simpa using hr4
  · left; refine ⟨?_, by simp⟩
    rw [pow_one]
    have : (r ^ 2 * s) ^ 2 = r ^ 2 * (s * r ^ 2) * s := by rw [sq]; group
    rw [this, hsr2]
    calc r ^ 2 * (r ^ 2 * s) * s = r ^ 4 * (s * s) := by group
      _ = 1 := by rw [← sq, hr4, hs2, one_mul]
  · right; refine ⟨?_, rfl, by simp⟩
    simp only [pow_zero, mul_one]
    rw [hz, ← pow_mul]
    have : r ^ (3 * 2) = r ^ 4 * r ^ 2 := by group
    rw [this, hr4, one_mul]
  · left; refine ⟨?_, by simp⟩
    rw [pow_one]
    have : (r ^ 3 * s) ^ 2 = r ^ 3 * (s * r ^ 3) * s := by rw [sq]; group
    rw [this, hsr3]
    calc r ^ 3 * (r * s) * s = r ^ 4 * (s * s) := by group
      _ = 1 := by rw [← sq, hr4, hs2, one_mul]

theorem IsD8.sq_mem (d : IsD8 P r s z) {p : G} (hp : p ∈ P) : p ^ 2 = 1 ∨ p ^ 2 = z := by
  obtain ⟨i, j, rfl⟩ := d.P_gen p hp
  rw [pow_eq_pow_mod i d.r4, pow_eq_pow_mod j d.s2]
  have hi : i % 4 < 4 := Nat.mod_lt _ (by norm_num)
  have hj : j % 2 < 2 := Nat.mod_lt _ (by norm_num)
  rcases d.sq_table (i % 4) (j % 2) hi hj with h | h
  · exact Or.inl h.1
  · exact Or.inr h.1

theorem IsD8.sq_eq_z (d : IsD8 P r s z) {p : G} (hp : p ∈ P) (h : p ^ 2 = z) : p = r ∨ p = r ^ 3 := by
  obtain ⟨i, j, rfl⟩ := d.P_gen p hp
  rw [pow_eq_pow_mod i d.r4, pow_eq_pow_mod j d.s2] at h ⊢
  have hi : i % 4 < 4 := Nat.mod_lt _ (by norm_num)
  have hj : j % 2 < 2 := Nat.mod_lt _ (by norm_num)
  rcases d.sq_table (i % 4) (j % 2) hi hj with ⟨h1, h2⟩ | ⟨-, hb, ha⟩
  · exact absurd (h.symm.trans h1) d.z_ne_one
  · rw [hb]
    rcases ha with ha | ha <;> rw [ha] <;> simp

theorem IsD8.sq_ne_one (d : IsD8 P r s z) {p : G} (hp : p ∈ P) (h : p ^ 2 ≠ 1) : p = r ∨ p = r ^ 3 := by
  rcases d.sq_mem hp with h1 | h1
  · exact absurd h1 h
  · exact d.sq_eq_z hp h1

theorem IsD8.s_conj_r (d : IsD8 P r s z) : s * r * s⁻¹ = r ^ 3 := by
  rw [d.srs, d.r_inv]

theorem IsD8.r_conj_s (d : IsD8 P r s z) : r * s * r⁻¹ = z * s := by
  rw [d.r_inv, d.z_eq]
  calc r * s * r ^ 3 = r * (s * r ^ 3) := by group
    _ = r * (r * s) := by rw [d.s_r3]
    _ = r ^ 2 * s := by rw [sq, mul_assoc]

theorem IsD8.exists_inner (d : IsD8 P r s z) {q : G}
    (hr : q * r * q⁻¹ = r ∨ q * r * q⁻¹ = r ^ 3) (hs : q * s * q⁻¹ = s ∨ q * s * q⁻¹ = z * s) :
    ∃ d' ∈ P, ∀ p ∈ P, q * p * q⁻¹ = d' * p * d'⁻¹ := by
  have key : ∀ (w : G) (i j : ℕ), w * (r ^ i * s ^ j) * w⁻¹ = (w * r * w⁻¹) ^ i * (w * s * w⁻¹) ^ j := by
    intro w i j; rw [conj_pow, conj_pow]; group
  have hrs : r * s ∈ P := P.mul_mem d.r_mem d.s_mem
  have hrsr : (r * s) * r * (r * s)⁻¹ = r ^ 3 := by
    calc (r * s) * r * (r * s)⁻¹ = r * (s * r * s⁻¹) * r⁻¹ := by group
      _ = r * r ^ 3 * r⁻¹ := by rw [d.s_conj_r]
      _ = r ^ 3 := by group
  have hrss : (r * s) * s * (r * s)⁻¹ = z * s := by
    calc (r * s) * s * (r * s)⁻¹ = r * s * r⁻¹ := by group
      _ = z * s := d.r_conj_s
  have hsss : s * s * s⁻¹ = s := by group
  have hrrr : r * r * r⁻¹ = r := by group
  have h1 : (1 : G) * r * (1 : G)⁻¹ = r := by group
  have h1s : (1 : G) * s * (1 : G)⁻¹ = s := by group
  rcases hr with hr | hr <;> rcases hs with hs | hs
  · refine ⟨1, P.one_mem, fun p hp => ?_⟩
    obtain ⟨i, j, rfl⟩ := d.P_gen p hp
    rw [key, key, hr, hs, h1, h1s]
  · refine ⟨r, d.r_mem, fun p hp => ?_⟩
    obtain ⟨i, j, rfl⟩ := d.P_gen p hp
    rw [key, key, hr, hs, hrrr, d.r_conj_s]
  · refine ⟨s, d.s_mem, fun p hp => ?_⟩
    obtain ⟨i, j, rfl⟩ := d.P_gen p hp
    rw [key, key, hr, hs, d.s_conj_r, hsss]
  · refine ⟨r * s, hrs, fun p hp => ?_⟩
    obtain ⟨i, j, rfl⟩ := d.P_gen p hp
    rw [key, key, hr, hs, hrsr, hrss]

theorem IsD8.r3_ne_one (d : IsD8 P r s z) : r ^ 3 ≠ 1 := by
  intro h
  apply d.r2_ne
  have : r = 1 := by
    calc r = r ^ 4 * (r ^ 3)⁻¹ := by group
      _ = 1 := by rw [d.r4, h]; group
  rw [this]; group

theorem IsD8.r_ne_one (d : IsD8 P r s z) : r ≠ 1 := by
  intro h
  apply d.r2_ne
  rw [h]; group

theorem IsD8.P_cases (d : IsD8 P r s z) {p : G} (hp : p ∈ P) :
    p = 1 ∨ p = r ∨ p = z ∨ p = r ^ 3 ∨ p = s ∨ p = r * s ∨ p = z * s ∨ p = r ^ 3 * s := by
  obtain ⟨i, j, rfl⟩ := d.P_gen p hp
  rw [pow_eq_pow_mod i d.r4, pow_eq_pow_mod j d.s2]
  have hi : i % 4 < 4 := Nat.mod_lt _ (by norm_num)
  have hj : j % 2 < 2 := Nat.mod_lt _ (by norm_num)
  generalize i % 4 = a at hi ⊢
  generalize j % 2 = b at hj ⊢
  interval_cases a <;> interval_cases b <;> simp [d.z_eq]

theorem IsD8.outer_shape (d : IsD8 P r s z) {y : G} (hy2 : y ^ 2 = 1) (hyP : ∀ p ∈ P, y * p * y⁻¹ ∈ P)
    (hout : ¬ ∃ d' ∈ P, ∀ p ∈ P, y * p * y⁻¹ = d' * p * d'⁻¹) :
    y * r * y⁻¹ = r⁻¹ ∧ (y * s * y⁻¹ = r * s ∨ y * s * y⁻¹ = r ^ 3 * s) := by
  have hz1 : y * z * y⁻¹ = z := by
    have h1 : (y * r * y⁻¹) ^ 2 = y * z * y⁻¹ := by rw [conj_pow, d.z_eq]
    have hr1P := hyP r d.r_mem
    rcases d.sq_mem hr1P with h | h
    · exfalso
      apply d.z_ne_one
      calc z = y⁻¹ * (y * z * y⁻¹) * y := by group
        _ = 1 := by rw [← h1, h]; group
    · rw [← h1, h]
  have hyz' : y⁻¹ * z * y = z := by
    calc y⁻¹ * z * y = y⁻¹ * (y * z * y⁻¹) * y := by rw [hz1]
      _ = z := by group
  have hr1 : y * r * y⁻¹ = r ∨ y * r * y⁻¹ = r ^ 3 := by
    apply d.sq_eq_z (hyP r d.r_mem)
    rw [conj_pow, ← d.z_eq, hz1]
  have hs1P := hyP s d.s_mem
  have hs12 : (y * s * y⁻¹) ^ 2 = 1 := by rw [conj_pow, d.s2]; group
  have hs11 : y * s * y⁻¹ ≠ 1 := by
    intro h
    apply d.s_ne_one
    calc s = y⁻¹ * (y * s * y⁻¹) * y := by group
      _ = 1 := by rw [h]; group
  have hs1z : y * s * y⁻¹ ≠ z := by
    intro h
    apply d.s_ne_z
    calc s = y⁻¹ * (y * s * y⁻¹) * y := by group
      _ = z := by rw [h, hyz']
  have hyy : ∀ w : G, y * (y * w * y⁻¹) * y⁻¹ = w := by
    intro w
    calc y * (y * w * y⁻¹) * y⁻¹ = y ^ 2 * w * (y ^ 2)⁻¹ := by rw [sq]; group
      _ = w := by rw [hy2]; group
  have hrs : r * s ∈ P := P.mul_mem d.r_mem d.s_mem
  rcases d.P_inv hs1P hs12 with h | h | h | h | h | h
  · exact absurd h hs11
  · exact absurd h hs1z
  ·
    exfalso
    apply hout
    exact d.exists_inner hr1 (Or.inl h)
  · exfalso
    apply hout
    exact d.exists_inner hr1 (Or.inr h)
  ·
    rcases hr1 with hr | hr
    · exfalso
      have := hyy s
      rw [h] at this
      have e : y * (r * s) * y⁻¹ = (y * r * y⁻¹) * (y * s * y⁻¹) := by group
      rw [e, hr, h] at this
      apply d.r2_ne
      have h2 : r ^ 2 * s = 1 * s := by
        calc r ^ 2 * s = r * (r * s) := by rw [sq, mul_assoc]
          _ = s := this
          _ = 1 * s := (one_mul s).symm
      exact mul_right_cancel h2
    · exact ⟨by rw [hr, d.r_inv], Or.inl h⟩
  ·
    rcases hr1 with hr | hr
    · exfalso
      have := hyy s
      rw [h] at this
      have e : y * (z * (r * s)) * y⁻¹ = (y * z * y⁻¹) * (y * r * y⁻¹) * (y * s * y⁻¹) := by group
      rw [e, hz1, hr, h] at this
      apply d.r2_ne
      have hzz : z * z = 1 := by rw [← sq]; exact d.z_sq
      have : r ^ 2 * s = 1 * s := by
        rw [one_mul]
        calc r ^ 2 * s = (z * z) * (r ^ 2 * s) := by rw [hzz, one_mul]
          _ = z * r * (z * (r * s)) := by rw [d.z_eq]; group
          _ = s := by rw [this]
      exact mul_right_cancel this
    · refine ⟨by rw [hr, d.r_inv], Or.inr ?_⟩
      rw [h, d.z_eq]; group

theorem IsD8.refl_inv (d : IsD8 P r s z) (k : ℕ) : (r ^ k * s)⁻¹ = r ^ k * s := by
  apply inv_eq_of_mul_eq_one_right
  have h : s * r ^ k * s⁻¹ = (r⁻¹) ^ k := by rw [← d.srs]; exact (conj_pow).symm
  calc r ^ k * s * (r ^ k * s) = r ^ k * (s * r ^ k * s⁻¹) * (s * s) := by group
    _ = r ^ k * (r⁻¹) ^ k * 1 := by rw [h, ← sq, d.s2]
    _ = 1 := by rw [inv_pow]; group

theorem IsD8.refl_not_fixed (d : IsD8 P r s z) {y : G} (hyr : y * r * y⁻¹ = r⁻¹)
    (hys : y * s * y⁻¹ = r * s ∨ y * s * y⁻¹ = r ^ 3 * s) (k : ℕ) :
    y * (r ^ k * s) * y⁻¹ ≠ r ^ k * s := by
  intro hk
  obtain ⟨ε, hε, hε13⟩ : ∃ ε : ℕ, y * s * y⁻¹ = r ^ ε * s ∧ (ε = 1 ∨ ε = 3) := by
    rcases hys with h | h
    · exact ⟨1, by rw [h, pow_one], Or.inl rfl⟩
    · exact ⟨3, h, Or.inr rfl⟩
  have hyrk : y * r ^ k * y⁻¹ = (r⁻¹) ^ k := by rw [← hyr]; exact (conj_pow).symm
  have key : y * (r ^ k * s) * y⁻¹ = (r⁻¹) ^ k * (r ^ ε * s) := by
    rw [← hε, ← hyrk]; group
  rw [key] at hk
  have e : r ^ ε * s = r ^ (2 * k) * s := by
    calc r ^ ε * s = r ^ k * ((r⁻¹) ^ k * (r ^ ε * s)) := by group
      _ = r ^ k * (r ^ k * s) := by rw [hk]
      _ = r ^ (2 * k) * s := by rw [two_mul, pow_add]; group
  have h1 : r ^ ε = r ^ (2 * k) := mul_right_cancel e
  have hzk : r ^ (2 * k) = 1 ∨ r ^ (2 * k) = r ^ 2 := by
    rw [pow_mul, ← d.z_eq, pow_eq_pow_mod k d.z_sq]
    have hk2 : k % 2 < 2 := Nat.mod_lt _ (by norm_num)
    generalize k % 2 = b at hk2
    interval_cases b
    · left; simp
    · right; simp [d.z_eq]
  have hr1 : r ≠ 1 := d.r_ne_one
  have hr12 : r ≠ r ^ 2 := by
    intro h
    apply hr1
    have h' := h
    rw [sq] at h'
    exact mul_eq_left.mp h'.symm
  have hr3 : r ^ 3 ≠ 1 := d.r3_ne_one
  have hr32 : r ^ 3 ≠ r ^ 2 := by
    intro h
    apply hr1
    have h' : r ^ 2 * r = r ^ 2 := by rw [← pow_succ]; exact h
    exact mul_eq_left.mp h'
  rcases hε13 with rfl | rfl <;> rcases hzk with h2 | h2 <;> rw [h2] at h1
  · exact hr1 (by simpa using h1)
  · exact hr12 (by simpa using h1)
  · exact hr3 h1
  · exact hr32 h1

theorem IsD8.inverted_decomp (d : IsD8 P r s z) {y : G} (hyr : y * r * y⁻¹ = r⁻¹)
    (hys : y * s * y⁻¹ = r * s ∨ y * s * y⁻¹ = r ^ 3 * s) {p : G} (hp : p ∈ P)
    (hinv : y * p * y⁻¹ = p⁻¹) : ∃ g ∈ P, p = g * (y * g * y⁻¹)⁻¹ := by
  have hrs : r * s ∈ P := P.mul_mem d.r_mem d.s_mem
  have hconj : ∀ w : G, y * (r * w) * y⁻¹ = r⁻¹ * (y * w * y⁻¹) := fun w => by
    rw [← hyr]; group
  have hr4 := d.r4
  have hr3inv : r⁻¹ = r ^ 3 := d.r_inv
  have hz : z = r ^ 2 := d.z_eq
  have hs2 := d.s2
  have hsr := d.s_r
  have hsr2 := d.s_r2
  have hsr3 := d.s_r3
  have hss : s * s = 1 := by rw [← sq]; exact hs2
  have hrefl : ∀ k : ℕ, p = r ^ k * s → False := by
    intro k hk
    apply d.refl_not_fixed hyr hys k
    rw [← hk, hinv, hk, d.refl_inv]
  have hrefl1 : (r ^ 1 * s)⁻¹ = r * s := by rw [d.refl_inv, pow_one]
  have hrefl2 : (r ^ 2 * s)⁻¹ = r ^ 2 * s := d.refl_inv 2
  have hrefl3 : (r ^ 3 * s)⁻¹ = r ^ 3 * s := d.refl_inv 3
  rcases d.P_cases hp with h | h | h | h | h | h | h | h
  · exact ⟨1, P.one_mem, by rw [h]; group⟩
  ·
    rcases hys with hys | hys
    · refine ⟨r * s, hrs, ?_⟩
      have e : y * (r * s) * y⁻¹ = s := by rw [hconj, hys]; group
      rw [e, h]; group
    · refine ⟨s, d.s_mem, ?_⟩
      rw [hys, h]
      have : (r ^ 3 * s)⁻¹ = r ^ 3 * s := hrefl3
      rw [this]
      calc r = (r * s) * s := by rw [mul_assoc, hss, mul_one]
        _ = (s * r ^ 3) * s := by rw [hsr3]
        _ = s * (r ^ 3 * s) := by rw [mul_assoc]
  ·
    refine ⟨r, d.r_mem, ?_⟩
    rw [hyr, h, hz, inv_inv, sq]
  ·
    rcases hys with hys | hys
    · refine ⟨s, d.s_mem, ?_⟩
      rw [hys, h]
      have : (r * s)⁻¹ = r * s := by simpa using hrefl1
      rw [this]
      calc r ^ 3 = (r ^ 3 * s) * s := by rw [mul_assoc, hss, mul_one]
        _ = (s * r) * s := by rw [hsr]
        _ = s * (r * s) := by rw [mul_assoc]
    · refine ⟨r * s, hrs, ?_⟩
      have e : y * (r * s) * y⁻¹ = r ^ 2 * s := by
        rw [hconj, hys, hr3inv]
        calc r ^ 3 * (r ^ 3 * s) = r ^ 4 * r ^ 2 * s := by group
          _ = r ^ 2 * s := by rw [hr4, one_mul]
      rw [e, hrefl2, h]
      symm
      calc r * s * (r ^ 2 * s) = r * (s * r ^ 2) * s := by group
        _ = r * (r ^ 2 * s) * s := by rw [hsr2]
        _ = r * r ^ 2 * (s * s) := by group
        _ = r ^ 3 := by rw [hss, mul_one]; group
  · exact (hrefl 0 (by rw [h]; group)).elim
  · exact (hrefl 1 (by rw [h]; group)).elim
  · exact (hrefl 2 (by rw [h, hz])).elim
  · exact (hrefl 3 h).elim

theorem IsD8.r_ne_sq (d : IsD8 P r s z) : r ≠ r ^ 2 := by
  intro h
  apply d.r_ne_one
  have h' := h
  rw [sq] at h'
  exact mul_eq_left.mp h'.symm

theorem IsD8.r3_ne_sq (d : IsD8 P r s z) : r ^ 3 ≠ r ^ 2 := by
  intro h
  apply d.r_ne_one
  have h' : r ^ 2 * r = r ^ 2 := by rw [← pow_succ]; exact h
  exact mul_eq_left.mp h'

theorem IsD8.cent_of_outer (d : IsD8 P r s z) {y : G} (hyr : y * r * y⁻¹ = r⁻¹)
    (hys : y * s * y⁻¹ = r * s ∨ y * s * y⁻¹ = r ^ 3 * s) {p : G} (hp : p ∈ P)
    (hc : y * p * y⁻¹ = p) : p = 1 ∨ p = z := by
  have hr4 := d.r4
  have h3 : (r⁻¹) ^ 3 = r := by
    calc (r⁻¹) ^ 3 = r ^ 4 * (r⁻¹) ^ 3 := by rw [hr4, one_mul]
      _ = r := by group
  rcases d.P_cases hp with h | h | h | h | h | h | h | h
  · exact Or.inl h
  · exfalso
    rw [h, hyr] at hc
    exact d.r_ne_inv hc.symm
  · exact Or.inr h
  · exfalso
    rw [h] at hc
    have : y * r ^ 3 * y⁻¹ = (r⁻¹) ^ 3 := by rw [← hyr]; exact (conj_pow).symm
    rw [this, h3] at hc
    apply d.r2_ne
    have : r ^ 2 = 1 := by
      calc r ^ 2 = r ^ 3 * r⁻¹ := by group
        _ = r * r⁻¹ := by rw [← hc]
        _ = 1 := by group
    exact this
  · exact (d.refl_not_fixed hyr hys 0 (by rw [h] at hc; simpa using hc)).elim
  · exact (d.refl_not_fixed hyr hys 1 (by rw [h] at hc; simpa using hc)).elim
  · exact (d.refl_not_fixed hyr hys 2 (by rw [h, d.z_eq] at hc; exact hc)).elim
  · exact (d.refl_not_fixed hyr hys 3 (by rw [h] at hc; exact hc)).elim

theorem IsD8.conj_s (d : IsD8 P r s z) {p : G} (hp : p ∈ P) :
    p * s * p⁻¹ = s ∨ p * s * p⁻¹ = z * s := by
  have hzs : z * s * z⁻¹ = s := by
    calc z * s * z⁻¹ = s * z * z⁻¹ := by rw [d.z_comm_s]
      _ = s := by group
  have hr3 : r ^ 3 * s * (r ^ 3)⁻¹ = z * s := by
    have : (r ^ 3)⁻¹ = r := by rw [← d.r_inv, inv_inv]
    calc r ^ 3 * s * (r ^ 3)⁻¹ = r ^ 3 * (s * r) := by rw [this]; group
      _ = r ^ 3 * (r ^ 3 * s) := by rw [d.s_r]
      _ = r ^ 4 * r ^ 2 * s := by group
      _ = z * s := by rw [d.r4, one_mul, d.z_eq]
  rcases d.P_cases hp with h | h | h | h | h | h | h | h
  · left; rw [h]; group
  · right; rw [h]; exact d.r_conj_s
  · left; rw [h]; exact hzs
  · right; rw [h]; exact hr3
  · left; rw [h]; group
  · right; rw [h]
    calc r * s * s * (r * s)⁻¹ = r * s * r⁻¹ := by group
      _ = z * s := d.r_conj_s
  · left; rw [h]
    calc z * s * s * (z * s)⁻¹ = z * s * z⁻¹ := by group
      _ = s := hzs
  · right; rw [h]
    calc r ^ 3 * s * s * (r ^ 3 * s)⁻¹ = r ^ 3 * s * (r ^ 3)⁻¹ := by group
      _ = z * s := hr3

theorem IsD8.not_inner_of_shape (d : IsD8 P r s z) {y : G} (_hyr : y * r * y⁻¹ = r⁻¹)
    (hys : y * s * y⁻¹ = r * s ∨ y * s * y⁻¹ = r ^ 3 * s) :
    ¬ ∃ d' ∈ P, ∀ p ∈ P, y * p * y⁻¹ = d' * p * d'⁻¹ := by
  rintro ⟨d', hd', h⟩
  have h1 := h s d.s_mem
  rcases d.conj_s hd' with h2 | h2 <;> rw [h2] at h1 <;> rcases hys with h3 | h3 <;> rw [h3] at h1
  · exact d.r_ne_one (mul_eq_right.mp h1)
  · exact d.r3_ne_one (mul_eq_right.mp h1)
  · exact d.r_ne_sq ((mul_right_cancel h1).trans d.z_eq)
  · exact d.r3_ne_sq ((mul_right_cancel h1).trans d.z_eq)

end CFSG.GH74.GLS.C3.Layer1.P89
