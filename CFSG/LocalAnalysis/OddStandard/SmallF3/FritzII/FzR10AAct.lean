module

public import Mathlib.Tactic.Group
public import Mathlib.Data.ZMod.Basic
public import CFSG.LocalAnalysis.OddStandard.SmallF3.FritzII.FzR10ADef

public section

namespace CFSG.OddStandard.SmallF3.FritzII

open Certificates.FzR10A

variable {G : Type} [Group G] {P : Subgroup G} {a b : G}

private lemma fzrAux_ap_lt (m : Mat) (n : ℕ) : m.ap n < 64 := by
  have h1 : (m.a * (n % 8) + m.b * (n / 8 % 8)) % 8 < 8 := Nat.mod_lt _ (by norm_num)
  have h2 : (m.c * (n % 8) + m.d * (n / 8 % 8)) % 8 < 8 := Nat.mod_lt _ (by norm_num)
  simp only [Mat.ap]
  omega

private lemma fzrAux_ap_lo (m : Mat) (n : ℕ) :
    m.ap n % 8 = (m.a * (n % 8) + m.b * (n / 8 % 8)) % 8 := by
  simp only [Mat.ap]
  rw [Nat.add_mul_mod_self_left, Nat.mod_mod]

private lemma fzrAux_ap_hi (m : Mat) (n : ℕ) :
    m.ap n / 8 % 8 = (m.c * (n % 8) + m.d * (n / 8 % 8)) % 8 := by
  simp only [Mat.ap]
  rw [Nat.add_mul_div_left _ _ (by norm_num : 0 < 8)]
  have hA : (m.a * (n % 8) + m.b * (n / 8 % 8)) % 8 / 8 = 0 :=
    Nat.div_eq_of_lt (Nat.mod_lt _ (by norm_num))
  rw [hA, Nat.zero_add, Nat.mod_mod]

private lemma fzrAux_ap_lo_zmod (m : Mat) (q : ℕ) :
    ((m.ap q % 8 : ℕ) : ZMod 8) =
      (m.a : ZMod 8) * ((q % 8 : ℕ) : ZMod 8) +
        (m.b : ZMod 8) * ((q / 8 % 8 : ℕ) : ZMod 8) := by
  calc ((m.ap q % 8 : ℕ) : ZMod 8)
      = (((m.a * (q % 8) + m.b * (q / 8 % 8)) % 8 : ℕ) : ZMod 8) := by
        rw [fzrAux_ap_lo m q]
    _ = ((m.a * (q % 8) + m.b * (q / 8 % 8) : ℕ) : ZMod 8) := by
        rw [ZMod.natCast_mod]
    _ = (m.a : ZMod 8) * ((q % 8 : ℕ) : ZMod 8) +
        (m.b : ZMod 8) * ((q / 8 % 8 : ℕ) : ZMod 8) := by
        push_cast
        ring

private lemma fzrAux_ap_hi_zmod (m : Mat) (q : ℕ) :
    ((m.ap q / 8 % 8 : ℕ) : ZMod 8) =
      (m.c : ZMod 8) * ((q % 8 : ℕ) : ZMod 8) +
        (m.d : ZMod 8) * ((q / 8 % 8 : ℕ) : ZMod 8) := by
  calc ((m.ap q / 8 % 8 : ℕ) : ZMod 8)
      = (((m.c * (q % 8) + m.d * (q / 8 % 8)) % 8 : ℕ) : ZMod 8) := by
        rw [fzrAux_ap_hi m q]
    _ = ((m.c * (q % 8) + m.d * (q / 8 % 8) : ℕ) : ZMod 8) := by
        rw [ZMod.natCast_mod]
    _ = (m.c : ZMod 8) * ((q % 8 : ℕ) : ZMod 8) +
        (m.d : ZMod 8) * ((q / 8 % 8 : ℕ) : ZMod 8) := by
        push_cast
        ring

private lemma fzrAux_zmod_eq_of_lt {p q : ℕ} (hp : p < 8) (hq : q < 8)
    (h : (p : ZMod 8) = (q : ZMod 8)) : p = q := by
  have hmod := (ZMod.natCast_eq_natCast_iff' p q 8).mp h
  rwa [Nat.mod_eq_of_lt hp, Nat.mod_eq_of_lt hq] at hmod

private lemma fzrAux_ap_mul_lo (m n : Mat) (p : ℕ) :
    (m.mul n).ap p % 8 = m.ap (n.ap p) % 8 := by
  apply fzrAux_zmod_eq_of_lt (Nat.mod_lt _ (by norm_num)) (Nat.mod_lt _ (by norm_num))
  rw [fzrAux_ap_lo_zmod, fzrAux_ap_lo_zmod]
  rw [fzrAux_ap_lo_zmod n p, fzrAux_ap_hi_zmod n p]
  simp only [Mat.mul]
  simp only [ZMod.natCast_mod]
  push_cast
  ring

private lemma fzrAux_ap_mul_hi (m n : Mat) (p : ℕ) :
    (m.mul n).ap p / 8 % 8 = m.ap (n.ap p) / 8 % 8 := by
  apply fzrAux_zmod_eq_of_lt (Nat.mod_lt _ (by norm_num)) (Nat.mod_lt _ (by norm_num))
  rw [fzrAux_ap_hi_zmod, fzrAux_ap_hi_zmod]
  rw [fzrAux_ap_lo_zmod n p, fzrAux_ap_hi_zmod n p]
  simp only [Mat.mul]
  simp only [ZMod.natCast_mod]
  push_cast
  ring

private lemma fzrAux_eq_of_coords {x y : ℕ} (hx : x < 64) (hy : y < 64)
    (h0 : x % 8 = y % 8) (h1 : x / 8 % 8 = y / 8 % 8) : x = y := by
  have hxdiv : x / 8 % 8 = x / 8 := Nat.mod_eq_of_lt (by omega)
  have hydiv : y / 8 % 8 = y / 8 := Nat.mod_eq_of_lt (by omega)
  rw [hxdiv] at h1
  rw [hydiv] at h1
  calc x = x % 8 + 8 * (x / 8) := (Nat.mod_add_div x 8).symm
    _ = y % 8 + 8 * (y / 8) := by rw [h0, h1]
    _ = y := Nat.mod_add_div y 8

private lemma fzrAux_ap_mul (m n : Mat) (p : ℕ) : (m.mul n).ap p = m.ap (n.ap p) := by
  apply fzrAux_eq_of_coords (fzrAux_ap_lt (m.mul n) p) (fzrAux_ap_lt m (n.ap p))
  · exact fzrAux_ap_mul_lo m n p
  · exact fzrAux_ap_mul_hi m n p

private lemma fzrAux_mul_lt (m n : Mat) : FzR10AMatLt (m.mul n) := by
  refine ⟨?_, ?_, ?_, ?_⟩ <;> simp only [Mat.mul] <;> exact Nat.mod_lt _ (by norm_num)

private lemma fzrAux_one_lt : FzR10AMatLt Mat.one := by
  norm_num [FzR10AMatLt, Mat.one]

private lemma fzrAux_num_eq {n : ℕ} (hn : n < 64) : n % 8 + 8 * (n / 8 % 8) = n := by
  have h : n / 8 < 8 := by omega
  rw [Nat.mod_eq_of_lt h]
  exact Nat.mod_add_div n 8

private lemma fzrAux_ap_one {n : ℕ} (hn : n < 64) : Mat.one.ap n = n := by
  simp only [Mat.one, Mat.ap, Nat.one_mul, Nat.zero_mul, Nat.zero_add, Nat.add_zero]
  rw [Nat.mod_mod, Nat.mod_mod]
  exact fzrAux_num_eq hn

private lemma fzrAux_ext {m n : Mat} (hm : FzR10AMatLt m) (hn : FzR10AMatLt n)
    (h1 : m.ap 1 = n.ap 1) (h8 : m.ap 8 = n.ap 8) : m = n := by
  have h1lo := congrArg (fun x : ℕ => x % 8) h1
  have h1hi := congrArg (fun x : ℕ => x / 8 % 8) h1
  have h8lo := congrArg (fun x : ℕ => x % 8) h8
  have h8hi := congrArg (fun x : ℕ => x / 8 % 8) h8
  simp only [fzrAux_ap_lo, fzrAux_ap_hi] at h1lo h1hi h8lo h8hi
  norm_num at h1lo h1hi h8lo h8hi
  rw [Nat.mod_eq_of_lt hm.1, Nat.mod_eq_of_lt hn.1] at h1lo
  rw [Nat.mod_eq_of_lt hm.2.2.1, Nat.mod_eq_of_lt hn.2.2.1] at h1hi
  rw [Nat.mod_eq_of_lt hm.2.1, Nat.mod_eq_of_lt hn.2.1] at h8lo
  rw [Nat.mod_eq_of_lt hm.2.2.2, Nat.mod_eq_of_lt hn.2.2.2] at h8hi
  cases m; cases n; simp_all

private lemma fzrAux_elt_eq_iff (hB : FzR10ABasis P a b) {n m : ℕ} (hn : n < 64)
    (hm : m < 64) : fzrAElt a b n = fzrAElt a b m ↔ n = m :=
  ⟨fun h => hB.inj n m hn hm h, fun h => by rw [h]⟩

private lemma fzrAux_conj_pow (c x : G) (n : ℕ) :
    c * x ^ n * c⁻¹ = (c * x * c⁻¹) ^ n := by
  induction n with
  | zero => simp
  | succ n ih =>
      calc c * x ^ (n + 1) * c⁻¹
          = c * (x ^ n * x) * c⁻¹ := by rw [pow_succ]
        _ = (c * x ^ n * c⁻¹) * (c * x * c⁻¹) := by group
        _ = (c * x * c⁻¹) ^ n * (c * x * c⁻¹) := by rw [ih]
        _ = (c * x * c⁻¹) ^ (n + 1) := by rw [pow_succ]

private lemma fzrAux_conj_mul (c x y : G) :
    c * (x * y) * c⁻¹ = (c * x * c⁻¹) * (c * y * c⁻¹) := by group

private lemma fzrAux_combine {x y : G} (h : Commute x y) (p q r s : ℕ) :
    x ^ p * y ^ q * (x ^ r * y ^ s) = x ^ (p + r) * y ^ (q + s) := by
  have hyx : y ^ q * x ^ r = x ^ r * y ^ q := (h.symm.pow_pow q r).eq
  calc
    x ^ p * y ^ q * (x ^ r * y ^ s)
        = x ^ p * (y ^ q * x ^ r) * y ^ s := by group
    _ = x ^ p * (x ^ r * y ^ q) * y ^ s := by rw [hyx]
    _ = x ^ p * x ^ r * (y ^ q * y ^ s) := by group
    _ = x ^ (p + r) * y ^ (q + s) := by rw [← pow_add, ← pow_add]

theorem fzr_a_act_exists (hB : FzR10ABasis P a b) {c : G} (hc : ∀ p ∈ P, c * p * c⁻¹ ∈ P) :
    ∃ M : Mat, FzR10AMatLt M ∧ FzR10AAct a b c M := by
  obtain ⟨n1, hn1, h1⟩ := hB.span (c * a * c⁻¹) (hc a hB.a_mem)
  obtain ⟨n2, hn2, h2⟩ := hB.span (c * b * c⁻¹) (hc b hB.b_mem)
  let M : Mat := ⟨n1 % 8, n2 % 8, n1 / 8 % 8, n2 / 8 % 8⟩
  refine ⟨M, ?_, ?_⟩
  · refine ⟨?_, ?_, ?_, ?_⟩ <;> simp only [M] <;> exact Nat.mod_lt _ (by norm_num)
  · intro n hn
    have hcomm : Commute a b := hB.comm
    have hpow1 : (fzrAElt a b n1) ^ (n % 8) =
        a ^ ((n1 % 8) * (n % 8)) * b ^ ((n1 / 8 % 8) * (n % 8)) := by
      rw [fzrAElt, (hcomm.pow_pow (n1 % 8) (n1 / 8 % 8)).mul_pow]
      rw [← pow_mul, ← pow_mul]
    have hpow2 : (fzrAElt a b n2) ^ (n / 8 % 8) =
        a ^ ((n2 % 8) * (n / 8 % 8)) * b ^ ((n2 / 8 % 8) * (n / 8 % 8)) := by
      rw [fzrAElt, (hcomm.pow_pow (n2 % 8) (n2 / 8 % 8)).mul_pow]
      rw [← pow_mul, ← pow_mul]
    calc
      c * fzrAElt a b n * c⁻¹
          = c * (a ^ (n % 8) * b ^ (n / 8 % 8)) * c⁻¹ := by rfl
        _ = (c * a ^ (n % 8) * c⁻¹) * (c * b ^ (n / 8 % 8) * c⁻¹) :=
              (fzrAux_conj_mul c (a ^ (n % 8)) (b ^ (n / 8 % 8)))
        _ = (c * a * c⁻¹) ^ (n % 8) * (c * b * c⁻¹) ^ (n / 8 % 8) := by
              rw [fzrAux_conj_pow, fzrAux_conj_pow]
        _ = (fzrAElt a b n1) ^ (n % 8) * (fzrAElt a b n2) ^ (n / 8 % 8) := by
              rw [← h1, ← h2]
        _ = a ^ ((n1 % 8) * (n % 8)) * b ^ ((n1 / 8 % 8) * (n % 8)) *
              (a ^ ((n2 % 8) * (n / 8 % 8)) *
                b ^ ((n2 / 8 % 8) * (n / 8 % 8))) := by
              rw [hpow1, hpow2]
        _ = a ^ ((n1 % 8) * (n % 8) + (n2 % 8) * (n / 8 % 8)) *
              b ^ ((n1 / 8 % 8) * (n % 8) + (n2 / 8 % 8) * (n / 8 % 8)) :=
              fzrAux_combine hcomm _ _ _ _
        _ = fzrAElt a b (M.ap n) := by
              rw [fzrAElt, fzrAux_ap_lo M n, fzrAux_ap_hi M n]
              simp only [M]
              rw [← pow_eq_pow_mod _ hB.a8, ← pow_eq_pow_mod _ hB.b8]

theorem fzr_a_act_one : FzR10AAct a b (1 : G) Mat.one := by
  intro n hn
  rw [one_mul, inv_one, mul_one, fzrAux_ap_one hn]

theorem fzr_a_act_unique (hB : FzR10ABasis P a b) {c : G} {M N : Mat} (hM : FzR10AMatLt M)
    (hN : FzR10AMatLt N) (h1 : FzR10AAct a b c M) (h2 : FzR10AAct a b c N) : M = N := by
  have h1a := h1 1 (by norm_num)
  have h2a := h2 1 (by norm_num)
  have h1b := h1 8 (by norm_num)
  have h2b := h2 8 (by norm_num)
  have h1eq : M.ap 1 = N.ap 1 :=
    (fzrAux_elt_eq_iff hB (fzrAux_ap_lt M 1) (fzrAux_ap_lt N 1)).mp (h1a.symm.trans h2a)
  have h8eq : M.ap 8 = N.ap 8 :=
    (fzrAux_elt_eq_iff hB (fzrAux_ap_lt M 8) (fzrAux_ap_lt N 8)).mp (h1b.symm.trans h2b)
  exact fzrAux_ext hM hN h1eq h8eq

theorem fzr_a_act_mul {c d : G} {M N : Mat} (hc : FzR10AAct a b c M) (hd : FzR10AAct a b d N) :
    FzR10AAct a b (c * d) (M.mul N) := by
  intro n hn
  calc
    (c * d) * fzrAElt a b n * (c * d)⁻¹
        = c * (d * fzrAElt a b n * d⁻¹) * c⁻¹ := by group
      _ = c * fzrAElt a b (N.ap n) * c⁻¹ := by rw [hd n hn]
      _ = fzrAElt a b (M.ap (N.ap n)) := hc (N.ap n) (fzrAux_ap_lt N n)
      _ = fzrAElt a b ((M.mul N).ap n) := by rw [← fzrAux_ap_mul]

theorem fzr_a_act_mul_eq (hB : FzR10ABasis P a b) {c d e f : G} {M N K L : Mat}
    (hM : FzR10AMatLt M) (hN : FzR10AMatLt N) (hK : FzR10AMatLt K) (hL : FzR10AMatLt L)
    (hc : FzR10AAct a b c M) (hd : FzR10AAct a b d N) (he : FzR10AAct a b e K)
    (hf : FzR10AAct a b f L) (h : c * d = e * f) : M.mul N = K.mul L := by
  have hcd := fzr_a_act_mul hc hd
  have hef := fzr_a_act_mul he hf
  rw [h] at hcd
  exact fzr_a_act_unique hB (fzrAux_mul_lt M N) (fzrAux_mul_lt K L) hcd hef

theorem fzr_a_act_sq_one (hB : FzR10ABasis P a b) {c : G} {M : Mat} (hM : FzR10AMatLt M)
    (hc : FzR10AAct a b c M) (h : c * c = 1) : M.mul M = Mat.one := by
  have hm := fzr_a_act_mul hc hc
  rw [h] at hm
  exact fzr_a_act_unique hB (fzrAux_mul_lt M M) fzrAux_one_lt hm fzr_a_act_one

theorem fzr_a_act_comm (hB : FzR10ABasis P a b) {c d : G} {M N : Mat} (hM : FzR10AMatLt M)
    (hN : FzR10AMatLt N) (hc : FzR10AAct a b c M) (hd : FzR10AAct a b d N)
    (h : c * d = d * c) : M.mul N = N.mul M := by
  exact fzr_a_act_mul_eq hB hM hN hN hM hc hd hd hc h

end CFSG.OddStandard.SmallF3.FritzII
