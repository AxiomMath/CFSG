module

public import Mathlib.GroupTheory.SpecificGroups.Dihedral

public section

namespace CFSG.CGT.Foote81L6

open DihedralGroup

def zc (a : ℕ) : DihedralGroup (2 ^ a) := r ((2 ^ (a - 1) : ℕ) : ZMod (2 ^ a))

theorem two_pow_add_self (b : ℕ) :
    ((2 ^ b : ℕ) : ZMod (2 ^ (b + 1))) + ((2 ^ b : ℕ) : ZMod (2 ^ (b + 1))) = 0 := by
  rw [← Nat.cast_add, show 2 ^ b + 2 ^ b = 2 ^ (b + 1) by ring, ZMod.natCast_self]

theorem two_pow_neg (b : ℕ) :
    -((2 ^ b : ℕ) : ZMod (2 ^ (b + 1))) = ((2 ^ b : ℕ) : ZMod (2 ^ (b + 1))) :=
  neg_eq_of_add_eq_zero_left (two_pow_add_self b)

theorem two_ne_zero_zmod {a : ℕ} (ha : 2 ≤ a) : (2 : ZMod (2 ^ a)) ≠ 0 := by
  intro h
  have h2 : ((2 : ℕ) : ZMod (2 ^ a)) = 0 := by exact_mod_cast h
  rw [ZMod.natCast_eq_zero_iff] at h2
  have hle := Nat.le_of_dvd (by norm_num) h2
  have h4 : 2 ^ 2 ≤ 2 ^ a := Nat.pow_le_pow_right (by norm_num) ha
  norm_num at h4
  omega

theorem eq_zero_or_half {b : ℕ} {k : ZMod (2 ^ (b + 1))} (h : k + k = 0) :
    k = 0 ∨ k = ((2 ^ b : ℕ) : ZMod (2 ^ (b + 1))) := by
  haveI : NeZero (2 ^ (b + 1)) := ⟨by positivity⟩
  have hcast : ((2 * k.val : ℕ) : ZMod (2 ^ (b + 1))) = 2 * k := by
    rw [Nat.cast_mul, ZMod.natCast_zmod_val]
    norm_num
  have hdvd : 2 ^ (b + 1) ∣ 2 * k.val := by
    rw [← ZMod.natCast_eq_zero_iff, hcast, two_mul]
    exact h
  have h2 : 2 * 2 ^ b ∣ 2 * k.val := by
    rw [← pow_succ']
    exact hdvd
  have h3 : 2 ^ b ∣ k.val := Nat.dvd_of_mul_dvd_mul_left (by norm_num) h2
  obtain ⟨m, hm⟩ := h3
  have hlt : k.val < 2 ^ b * 2 := lt_of_lt_of_eq (ZMod.val_lt k) (pow_succ 2 b)
  have hm2 : m < 2 := by
    by_contra hcon
    have hcon' : 2 ≤ m := not_lt.mp hcon
    have hle : 2 ^ b * 2 ≤ 2 ^ b * m := Nat.mul_le_mul_left (2 ^ b) hcon'
    rw [← hm] at hle
    exact absurd hlt (not_lt.mpr hle)
  interval_cases m
  · left
    have h0 : k.val = 0 := by simpa using hm
    rw [← ZMod.natCast_zmod_val k, h0, Nat.cast_zero]
  · right
    have h1 : k.val = 2 ^ b := by simpa using hm
    rw [← ZMod.natCast_zmod_val k, h1]

theorem zc_mem_of_rot {a : ℕ} (ha : 1 ≤ a) (K : Subgroup (DihedralGroup (2 ^ a)))
    {k : ZMod (2 ^ a)} (hk : r k ∈ K) (hk0 : k ≠ 0) : zc a ∈ K := by
  obtain ⟨c, rfl⟩ : ∃ c, a = c + 1 := ⟨a - 1, by omega⟩
  haveI : NeZero (2 ^ (c + 1)) := ⟨by positivity⟩
  have hv0 : k.val ≠ 0 := by
    rwa [Ne, ZMod.val_eq_zero]
  obtain ⟨t, u, hu, hvtu⟩ := Nat.exists_eq_two_pow_mul_odd hv0
  have hupos : 0 < u := hu.pos
  have hvlt : k.val < 2 ^ (c + 1) := ZMod.val_lt k
  have ht : t ≤ c := by
    by_contra hcon
    have hcon' : c + 1 ≤ t := by omega
    have h1 : 2 ^ (c + 1) ≤ 2 ^ t := Nat.pow_le_pow_right (by norm_num) hcon'
    have h2 : 2 ^ t ≤ k.val := by
      rw [hvtu]
      exact Nat.le_mul_of_pos_right _ hupos
    exact absurd hvlt (not_lt.mpr (h1.trans h2))
  obtain ⟨s, rfl⟩ := hu
  have hk' : k = ((2 ^ t * (2 * s + 1) : ℕ) : ZMod (2 ^ (c + 1))) := by
    rw [← hvtu]
    exact (ZMod.natCast_zmod_val k).symm
  have h1 : 2 ^ t * 2 ^ (c - t) = 2 ^ c := by
    rw [← pow_add, Nat.add_sub_of_le ht]
  have h2 : 2 ^ t * (2 * s + 1) * 2 ^ (c - t) = 2 ^ c + 2 ^ (c + 1) * s := by
    calc 2 ^ t * (2 * s + 1) * 2 ^ (c - t) = (2 ^ t * 2 ^ (c - t)) * (2 * s + 1) := by ring
      _ = 2 ^ c * (2 * s + 1) := by rw [h1]
      _ = 2 ^ c + 2 ^ (c + 1) * s := by ring
  have key : k * ((2 ^ (c - t) : ℕ) : ZMod (2 ^ (c + 1))) = ((2 ^ c : ℕ) : ZMod (2 ^ (c + 1))) := by
    rw [hk', ← Nat.cast_mul, h2, Nat.cast_add, Nat.cast_mul, ZMod.natCast_self, zero_mul, add_zero]
  have hm : r (k * ((2 ^ (c - t) : ℕ) : ZMod (2 ^ (c + 1)))) ∈ K := by
    rw [← DihedralGroup.r_pow]
    exact K.pow_mem hk _
  rw [key] at hm
  have hz : zc (c + 1) = r ((2 ^ c : ℕ) : ZMod (2 ^ (c + 1))) := rfl
  rw [hz]
  exact hm

theorem zc_mul_self {a : ℕ} (ha : 1 ≤ a) : zc a * zc a = 1 := by
  obtain ⟨b, rfl⟩ : ∃ b, a = b + 1 := ⟨a - 1, by omega⟩
  simp only [zc, Nat.add_sub_cancel, r_mul_r]
  rw [one_def]
  congr 1
  exact two_pow_add_self b

theorem zc_ne_one {a : ℕ} (ha : 1 ≤ a) : zc a ≠ 1 := by
  obtain ⟨b, rfl⟩ : ∃ b, a = b + 1 := ⟨a - 1, by omega⟩
  intro h
  simp only [zc, Nat.add_sub_cancel, one_def] at h
  rw [DihedralGroup.r.injEq, ZMod.natCast_eq_zero_iff] at h
  have hle := Nat.le_of_dvd (by positivity) h
  have hlt : 2 ^ b < 2 ^ (b + 1) := Nat.pow_lt_pow_right (by norm_num) (by omega)
  omega

theorem zc_comm {a : ℕ} (ha : 1 ≤ a) (g : DihedralGroup (2 ^ a)) : g * zc a = zc a * g := by
  obtain ⟨b, rfl⟩ : ∃ b, a = b + 1 := ⟨a - 1, by omega⟩
  have hx := two_pow_neg b
  have hz : zc (b + 1) = r ((2 ^ b : ℕ) : ZMod (2 ^ (b + 1))) := rfl
  rw [hz]
  cases g with
  | r i =>
    rw [r_mul_r, r_mul_r]
    exact congrArg r (add_comm _ _)
  | sr i =>
    rw [sr_mul_r, r_mul_sr]
    congr 1
    rw [sub_eq_add_neg, hx]

theorem eq_one_or_zc_of_comm {a : ℕ} (ha : 2 ≤ a) {c : DihedralGroup (2 ^ a)}
    (hc : ∀ g, g * c = c * g) : c = 1 ∨ c = zc a := by
  obtain ⟨b, rfl⟩ : ∃ b, a = b + 1 := ⟨a - 1, by omega⟩
  cases c with
  | sr k =>
    exfalso
    have h1 := hc (r 1)
    rw [r_mul_sr, sr_mul_r] at h1
    simp only [DihedralGroup.sr.injEq] at h1
    apply two_ne_zero_zmod ha
    have e2 : (2 : ZMod (2 ^ (b + 1))) = (k + 1) - (k - 1) := by ring
    rw [e2, ← h1, sub_self]
  | r k =>
    have h1 := hc (sr 0)
    rw [sr_mul_r, r_mul_sr] at h1
    simp only [DihedralGroup.sr.injEq] at h1
    have h2 : k + k = 0 := by
      have e : k + k = (0 + k) - (0 - k) := by ring
      rw [e, h1, sub_self]
    rcases eq_zero_or_half h2 with h0 | hh
    · left
      subst h0
      exact one_def.symm
    · right
      subst hh
      rfl

theorem mul_comm_of_le_one {a : ℕ} (ha : a ≤ 1) (g h : DihedralGroup (2 ^ a)) :
    g * h = h * g := by
  interval_cases a
  · have hs : ∀ x y : ZMod (2 ^ 0), x = y := by
      intro x y
      haveI : NeZero (2 ^ 0) := ⟨by norm_num⟩
      have h0 : ∀ z : ZMod (2 ^ 0), z = 0 := by
        intro z
        have hz := ZMod.val_lt z
        exact (ZMod.val_eq_zero z).mp (Nat.lt_one_iff.mp (lt_of_lt_of_eq hz (pow_zero 2)))
      exact (h0 x).trans (h0 y).symm
    cases g <;> cases h <;> simp only [r_mul_r, r_mul_sr, sr_mul_r, sr_mul_sr] <;> congr 1 <;>
      exact hs _ _
  · exact (by decide : ∀ g h : DihedralGroup 2, g * h = h * g) g h

theorem pow_two_pow_eq_one {a b : ℕ} (ha : 1 ≤ a) (hab : a ≤ b) (g : DihedralGroup (2 ^ a)) :
    g ^ (2 ^ b) = 1 := by
  have hexp : Monoid.exponent (DihedralGroup (2 ^ a)) ∣ 2 ^ a := by
    rw [DihedralGroup.exponent]
    exact Nat.lcm_dvd dvd_rfl (dvd_pow_self 2 (by omega))
  have h1 : g ^ (2 ^ a) = 1 := by
    obtain ⟨d, hd⟩ := hexp
    have he : g ^ (2 ^ a) = g ^ (Monoid.exponent (DihedralGroup (2 ^ a)) * d) :=
      congrArg (fun n => g ^ n) hd
    rw [he, pow_mul, Monoid.pow_exponent_eq_one, one_pow]
  obtain ⟨c, rfl⟩ : ∃ c, b = a + c := ⟨b - a, by omega⟩
  rw [pow_add (2 : ℕ) a c, pow_mul, h1, one_pow]

theorem rho_pow {a : ℕ} (ha : 1 ≤ a) : (r 1 : DihedralGroup (2 ^ a)) ^ (2 ^ (a - 1)) = zc a := by
  show (r 1 : DihedralGroup (2 ^ a)) ^ (2 ^ (a - 1)) = r ((2 ^ (a - 1) : ℕ) : ZMod (2 ^ a))
  exact r_one_pow _

theorem comm_sr_r_eq {a : ℕ} :
    (sr 0 : DihedralGroup (2 ^ a))⁻¹ * (r 1)⁻¹ * sr 0 * r 1 = r 2 := by
  simp only [inv_sr, inv_r, sr_mul_r, sr_mul_sr, r_mul_r]
  congr 1
  ring

theorem comm_sr_r_ne_one {a : ℕ} (ha : 2 ≤ a) :
    (sr 0 : DihedralGroup (2 ^ a))⁻¹ * (r 1)⁻¹ * sr 0 * r 1 ≠ 1 := by
  rw [comm_sr_r_eq, one_def]
  intro h
  rw [DihedralGroup.r.injEq] at h
  exact two_ne_zero_zmod ha h

theorem comm_sr_r_pow {a : ℕ} (ha : 2 ≤ a) :
    ((sr 0 : DihedralGroup (2 ^ a))⁻¹ * (r 1)⁻¹ * sr 0 * r 1) ^ (2 ^ (a - 2)) = zc a := by
  rw [comm_sr_r_eq, r_pow]
  obtain ⟨c, rfl⟩ : ∃ c, a = c + 2 := ⟨a - 2, by omega⟩
  have hz : zc (c + 2) = r ((2 ^ (c + 1) : ℕ) : ZMod (2 ^ (c + 2))) := rfl
  rw [hz, show c + 2 - 2 = c by omega]
  congr 1
  push_cast
  ring

theorem zc_mem_of_normal {a : ℕ} (ha : 2 ≤ a) (K : Subgroup (DihedralGroup (2 ^ a))) [K.Normal]
    {n : DihedralGroup (2 ^ a)} (hn : n ∈ K) (h1 : n ≠ 1) : zc a ∈ K := by
  cases n with
  | r k =>
    have hk0 : k ≠ 0 := by
      rintro rfl
      exact h1 one_def.symm
    exact zc_mem_of_rot (by omega) K hn hk0
  | sr k =>
    have hconj : r 1 * sr k * (r 1)⁻¹ ∈ K := Subgroup.Normal.conj_mem ‹K.Normal› _ hn (r 1)
    have hprod : (sr k)⁻¹ * (r 1 * sr k * (r 1)⁻¹) ∈ K := K.mul_mem (K.inv_mem hn) hconj
    have hcomm : (sr k)⁻¹ * (r 1 * sr k * (r 1)⁻¹) = r (-2) := by
      simp only [inv_sr, inv_r, r_mul_sr, sr_mul_r, sr_mul_sr]
      congr 1
      ring
    rw [hcomm] at hprod
    exact zc_mem_of_rot (by omega) K hprod (neg_ne_zero.mpr (two_ne_zero_zmod ha))

theorem not_comm_of_two_le {a : ℕ} (ha : 2 ≤ a) :
    ∃ g h : DihedralGroup (2 ^ a), g * h ≠ h * g := by
  refine ⟨sr 0, r 1, ?_⟩
  intro h
  rw [sr_mul_r, r_mul_sr] at h
  simp only [DihedralGroup.sr.injEq] at h
  apply two_ne_zero_zmod ha
  have e : (2 : ZMod (2 ^ a)) = (0 + 1) - (0 - 1) := by ring
  rw [e, h, sub_self]

end CFSG.CGT.Foote81L6
