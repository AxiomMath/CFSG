module

public import Certificates.Data.Kernel.AxisPlane.Plane
public import CFSG.Certificates.Kernel.BenesSound

public section

set_option maxHeartbeats 400000

namespace CFSG.KC.AxisPlane

open CFSG.KC.Benes CFSG.KC.MonsterConv.Perm

@[expose] def dat (X q : Nat) : Bool := X.testBit (64 + q)

theorem land_shr_one (P k : Nat) : Nat.land (Nat.shiftRight P k) 1 = (P.testBit k).toNat := by
  rw [nland, nshr, Nat.and_one_is_mod, Nat.shiftRight_eq_div_pow, Nat.testBit_eq_decide_div_mod_eq]
  rcases Nat.mod_two_eq_zero_or_one (P / 2 ^ k) with h | h <;> simp [h]

theorem beq_bit (l j : Nat) : Nat.beq (Nat.land (Nat.shiftRight l j) 1) 1 = l.testBit j := by
  rw [land_shr_one]
  cases l.testBit j <;> rfl

theorem testBit_onesW (q : Nat) : onesW.testBit q = decide (q < 16777216) := by
  unfold onesW
  rw [nsub, nshl, Nat.one_shiftLeft, Nat.testBit_two_pow_sub_one]
  rfl

theorem dat_eq_shr (X q : Nat) : dat X q = (Nat.shiftRight X 64).testBit q := by
  rw [dat, nshr, Nat.testBit_shiftRight]

theorem dat_xor (X Y q : Nat) : dat (Nat.xor X Y) q = (dat X q ^^ dat Y q) := by
  rw [dat, dat, dat, nxor, Nat.testBit_xor]

theorem dat_land (X Y q : Nat) : dat (Nat.land X Y) q = (dat X q && dat Y q) := by
  rw [dat, dat, dat, nland, Nat.testBit_and]

theorem dat_lor (X Y q : Nat) : dat (Nat.lor X Y) q = (dat X q || dat Y q) := by
  rw [dat, dat, dat, nlor, Nat.testBit_or]

theorem dat_zero (q : Nat) : dat 0 q = false := Nat.zero_testBit _

theorem dat_shl (Y q : Nat) : dat (Nat.shiftLeft Y 64) q = Y.testBit q := by
  rw [dat, nshl, Nat.testBit_shiftLeft]
  simp

theorem dat_lt {s : Nat} (hs : s < 2 ^ 64) (q : Nat) : dat s q = false :=
  Nat.testBit_lt_two_pow (Nat.lt_of_lt_of_le hs (Nat.pow_le_pow_right (by decide) (by omega)))

theorem dat_allK (q : Nat) : dat allK q = decide (q < 16777216) := by
  unfold allK
  rw [dat_shl, testBit_onesW]

theorem saltK_lt (k : Nat) : saltK k < 2 ^ 64 := by
  unfold saltK
  rw [nland]
  exact Nat.lt_of_le_of_lt Nat.and_le_right (by decide)

theorem dat_salt (k q : Nat) : dat (saltK k) q = false := dat_lt (saltK_lt k) q

theorem testBit_bitW {j : Nat} (hj : j < 24) (q : Nat) :
    (bitW j).testBit q = (decide (q < 16777216) && q.testBit j) := by
  have hW : wW = 2 ^ (j + 1) * 2 ^ (23 - j) := by
    rw [← Nat.pow_add, show j + 1 + (23 - j) = 24 by omega]
    rfl
  have h := testBit_bitPlane hW q
  have e : decide (q < wW) = decide (q < 16777216) := rfl
  rw [e] at h
  rw [← h]
  unfold bitW repW onesW
  simp only [nmul, nshl, nsub, ndiv, nadd, Nat.one_shiftLeft]

theorem dat_bitK {j : Nat} (hj : j < 24) (q : Nat) :
    dat (bitK j) q = (decide (q < 16777216) && q.testBit j) := by
  unfold bitK
  rw [dat_lor, dat_shl, dat_salt, testBit_bitW hj, Bool.or_false]

@[expose] def parG (l q : Nat) : Nat → Bool
  | 0 => false
  | n + 1 => (parG l q n ^^ (l.testBit n && q.testBit n))

theorem parG_xor (l a b : Nat) : ∀ n, parG l (a ^^^ b) n = (parG l a n ^^ parG l b n)
  | 0 => rfl
  | n + 1 => by
    simp only [parG, parG_xor l a b n, Nat.testBit_xor]
    cases parG l a n <;> cases parG l b n <;> cases l.testBit n <;> cases a.testBit n <;>
      cases b.testBit n <;> rfl

theorem parG_zero (l : Nat) : ∀ n, parG l 0 n = false
  | 0 => rfl
  | n + 1 => by simp [parG, parG_zero l n]

theorem parG_two_pow {l t : Nat} (ht : l.testBit t = false) : ∀ n, parG l (2 ^ t) n = false
  | 0 => rfl
  | n + 1 => by
    simp only [parG, parG_two_pow ht n, Nat.testBit_two_pow, Bool.false_xor]
    by_cases h : t = n
    · subst h
      simp [ht]
    · simp [h]

theorem dat_parRec (l q : Nat) : ∀ n, n ≤ 24 →
    dat (Nat.rec (motive := fun _ => Nat) (saltK (nat_lit 64))
      (fun j acc => Bool.rec (motive := fun _ => Nat) acc (Nat.xor acc (bitK j))
        (Nat.beq (Nat.land (Nat.shiftRight l j) (nat_lit 1)) (nat_lit 1))) n) q =
      (decide (q < 16777216) && parG l q n)
  | 0, _ => by
    change dat (saltK 64) q = _
    rw [dat_salt, parG, Bool.and_false]
  | n + 1, hn => by
    have ih := dat_parRec l q n (by omega)
    change dat (Bool.rec (motive := fun _ => Nat) _ (Nat.xor _ (bitK n))
      (Nat.beq (Nat.land (Nat.shiftRight l n) 1) 1)) q = _
    rw [beq_bit, parG]
    cases hb : l.testBit n
    · simp only [Bool.false_and, Bool.xor_false]
      exact ih
    · simp only [Bool.true_and]
      rw [dat_xor, ih, dat_bitK (by omega)]
      cases decide (q < 16777216) <;> simp

theorem dat_parK (l q : Nat) : dat (parK l) q = (decide (q < 16777216) && parG l q 24) :=
  dat_parRec l q 24 (Nat.le_refl 24)

theorem dat_tmaskK {t : Nat} (ht : t < 24) (l q : Nat) :
    dat (tmaskK t l) q = (decide (q < 16777216) && !q.testBit t && parG l q 24) := by
  unfold tmaskK
  rw [dat_land, dat_parK, dat_xor, dat_allK, dat_bitK ht]
  cases decide (q < 16777216) <;> cases q.testBit t <;> simp

@[expose] def tvN (t l v : Nat) : Nat := v ^^^ (if parG l v 24 = true then 2 ^ t else 0)

theorem tvN_xor (t l a b : Nat) : tvN t l (a ^^^ b) = tvN t l a ^^^ tvN t l b := by
  unfold tvN
  rw [parG_xor]
  apply Nat.eq_of_testBit_eq
  intro j
  cases parG l a 24 <;> cases parG l b 24 <;>
    simp only [Bool.false_xor, Bool.xor_false, Bool.true_xor, Bool.not_true, Bool.false_eq_true, ite_false, ite_true, Nat.testBit_xor, Nat.zero_testBit] <;>
    cases a.testBit j <;> cases b.testBit j <;> cases (2 ^ t).testBit j <;> rfl

theorem parG_tvN {t l : Nat} (ht : l.testBit t = false) (v : Nat) :
    parG l (tvN t l v) 24 = parG l v 24 := by
  unfold tvN
  rw [parG_xor]
  split
  · rw [parG_two_pow ht, Bool.xor_false]
  · rw [parG_zero, Bool.xor_false]

theorem tvN_tvN {t l : Nat} (ht : l.testBit t = false) (v : Nat) : tvN t l (tvN t l v) = v := by
  have e : tvN t l (tvN t l v) = tvN t l v ^^^ (if parG l v 24 = true then 2 ^ t else 0) := by
    rw [← parG_tvN ht v]
    rfl
  rw [e]
  unfold tvN
  rw [Nat.xor_assoc, Nat.xor_self, Nat.xor_zero]

theorem tvN_lt {t l v : Nat} (ht : t < 24) (hv : v < 16777216) : tvN t l v < 16777216 := by
  unfold tvN
  have h24 : (16777216 : Nat) = 2 ^ 24 := rfl
  rw [h24] at hv ⊢
  refine Nat.xor_lt_two_pow hv ?_
  split
  · exact Nat.pow_lt_pow_right (by decide) ht
  · exact Nat.two_pow_pos 24

theorem tvN_zero (t l : Nat) : tvN t l 0 = 0 := by
  unfold tvN
  rw [parG_zero]
  simp

theorem add_two_pow_eq_xor {p t : Nat} (h : p.testBit t = false) : p + 2 ^ t = p ^^^ 2 ^ t := by
  have hd := Nat.div_add_mod p (2 ^ (t + 1))
  have hr : p % 2 ^ (t + 1) < 2 ^ (t + 1) := Nat.mod_lt _ (Nat.two_pow_pos _)
  generalize p / 2 ^ (t + 1) = b at hd
  generalize p % 2 ^ (t + 1) = r at hd hr
  subst hd
  have hrt : r.testBit t = false := by
    have := h
    rw [Nat.testBit_two_pow_mul_add _ hr, ite_eq_left (Nat.lt_succ_self t)] at this
    exact this
  have hr' : r < 2 ^ t := by
    apply Nat.lt_of_not_le
    intro hle
    have := Nat.testBit_of_two_pow_le_and_two_pow_add_one_gt hle hr
    rw [hrt] at this
    exact absurd this (by decide)
  have hlt : 2 ^ t + r < 2 ^ (t + 1) := by rw [Nat.pow_succ]; omega
  have e : 2 ^ (t + 1) * b + r + 2 ^ t = 2 ^ (t + 1) * b + (2 ^ t + r) := by omega
  rw [e]
  apply Nat.eq_of_testBit_eq
  intro j
  rw [Nat.testBit_xor, Nat.testBit_two_pow_mul_add _ hlt, Nat.testBit_two_pow_mul_add _ hr,
    Nat.testBit_two_pow]
  by_cases hj : j < t + 1
  · rw [ite_eq_left hj, ite_eq_left hj]
    rcases Nat.lt_succ_iff_lt_or_eq.1 hj with hj | rfl
    · rw [Nat.testBit_two_pow_add_gt hj, decide_eq_false (by omega), Bool.xor_false]
    · rw [Nat.testBit_two_pow_add_eq, hrt, decide_eq_true rfl]
      rfl
  · rw [ite_eq_right hj, ite_eq_right hj, decide_eq_false (by omega), Bool.xor_false]

theorem opValid_spec {c : Nat} (h : opValid c = true) :
    c &&& 31 < 24 ∧ c >>> 5 < 16777216 ∧ (c >>> 5).testBit (c &&& 31) = false := by
  obtain ⟨h1, h2⟩ := andB_true h
  obtain ⟨h2, h3⟩ := andB_true h2
  rw [Nat.blt_eq] at h1 h2
  rw [Nat.beq_eq, land_shr_one] at h3
  refine ⟨h1, h2, ?_⟩
  revert h3
  cases (Nat.shiftRight c 5).testBit (Nat.land c 31) <;> simp

theorem swK_shr (d m S : Nat) :
    Nat.shiftRight (swK d m S) 64 = dsw d (Nat.shiftRight m 64) (Nat.shiftRight S 64) := by
  apply Nat.eq_of_testBit_eq
  intro i
  simp only [swK, CFSG.KC.MonsterConv.Perm.dsw, nxor, nland, nshl, nshr, nadd, Nat.testBit_xor,
    Nat.testBit_and, Nat.testBit_shiftLeft, Nat.testBit_shiftRight]
  have e1 : d + (64 + i) = 64 + (d + i) := by omega
  rw [e1]
  by_cases hd : d ≤ i
  · have e2 : 64 + i - (64 + d) = i - d := by omega
    have e3 : d + (64 + (i - d)) = 64 + (d + (i - d)) := by omega
    simp [hd, e2, e3]
  · have h1 : ¬ (64 + d ≤ 64 + i) := by omega
    simp [hd, h1]

theorem swp_eq_tvN {t l : Nat} (ht : t < 24) (hl : l.testBit t = false) {q : Nat}
    (hq : q < 16777216) :
    swp (2 ^ t) (Nat.shiftRight (tmaskK t l) 64) q = tvN t l q := by
  have hM : ∀ p, (Nat.shiftRight (tmaskK t l) 64).testBit p =
      (decide (p < 16777216) && !p.testBit t && parG l p 24) := fun p => by
    rw [← dat_eq_shr, dat_tmaskK ht]
  have hpar : ∀ p, p.testBit t = false → parG l (p + 2 ^ t) 24 = parG l p 24 := fun p hp => by
    rw [add_two_pow_eq_xor hp, parG_xor, parG_two_pow hl, Bool.xor_false]
  unfold swp tvN
  rw [hM]
  by_cases h1 : (decide (q < 16777216) && !q.testBit t && parG l q 24) = true
  · rw [ite_eq_left h1]
    simp only [Bool.and_eq_true, Bool.not_eq_true', decide_eq_true_eq] at h1
    rw [ite_eq_left h1.2, add_two_pow_eq_xor h1.1.2]
  · rw [ite_eq_right h1]
    by_cases hb : q.testBit t = true
    ·
      have hle : 2 ^ t ≤ q := Nat.ge_two_pow_of_testBit hb
      have hc : (q - 2 ^ t).testBit t = false := by
        have e : q = 2 ^ t + (q - 2 ^ t) := by omega
        have := hb
        rw [e, Nat.testBit_two_pow_add_eq] at this
        simpa using this
      have hp : parG l q 24 = parG l (q - 2 ^ t) 24 := by
        have := hpar _ hc
        rwa [Nat.sub_add_cancel hle] at this
      rw [hM, hp]
      by_cases h3 : parG l (q - 2 ^ t) 24 = true
      · have e2 : q - 2 ^ t = q ^^^ 2 ^ t := by
          have h := add_two_pow_eq_xor hc
          rw [Nat.sub_add_cancel hle] at h
          calc q - 2 ^ t = (q - 2 ^ t) ^^^ 2 ^ t ^^^ 2 ^ t := by
                rw [Nat.xor_assoc, Nat.xor_self, Nat.xor_zero]
            _ = q ^^^ 2 ^ t := by rw [← h]
        have h4 : 2 ^ t ≤ q ∧ (decide (q - 2 ^ t < 16777216) && !(q - 2 ^ t).testBit t &&
            parG l (q - 2 ^ t) 24) = true := by
          refine ⟨hle, ?_⟩
          simp only [hc, h3, Bool.not_false, Bool.and_true, decide_eq_true_eq]
          exact Nat.lt_of_le_of_lt (Nat.sub_le q _) hq
        rw [ite_eq_left h4, ite_eq_left h3, e2]
      · have h4 : ¬ (2 ^ t ≤ q ∧ (decide (q - 2 ^ t < 16777216) && !(q - 2 ^ t).testBit t &&
            parG l (q - 2 ^ t) 24) = true) := by
          rintro ⟨-, h4⟩
          simp [h3] at h4
        rw [ite_eq_right h4, ite_eq_right h3, Nat.xor_zero]
    · have hb' : q.testBit t = false := by simpa using hb
      have h2 : parG l q 24 = false := by
        simpa [hq, hb'] using h1
      have hn : ¬ (2 ^ t ≤ q ∧ (Nat.shiftRight (tmaskK t l) 64).testBit (q - 2 ^ t) = true) := by
        rintro ⟨hle, h4⟩
        rw [hM] at h4
        simp only [Bool.and_eq_true, Bool.not_eq_true', decide_eq_true_eq] at h4
        have e := add_two_pow_eq_xor h4.1.2
        rw [Nat.sub_add_cancel hle] at e
        have h5 : q.testBit t = true := by
          rw [e, Nat.testBit_xor, Nat.testBit_two_pow, h4.1.2]
          simp
        rw [hb'] at h5
        exact absurd h5 (by decide)
      rw [ite_eq_right hn, h2]
      simp

end CFSG.KC.AxisPlane

end
