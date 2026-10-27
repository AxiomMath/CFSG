module

public import CFSG.Certificates.Kernel.BabyMonster.DyLaneFld
public import CFSG.Certificates.Kernel.BabyMonster.DyStab
import Mathlib.Algebra.Order.Group.Nat
import Mathlib.Tactic.Ring.RingNF

public section

namespace CFSG.KC.BM.Ln

set_option exponentiation.threshold 140000

open CFSG.KC.BM CFSG.KC.BM.Dy CFSG.KC.BM.Lat

@[expose] def LnRel (m j0 j : ℕ) (R : ℕ → ℕ) (Y CE : ℕ) (vs outs : ℕ → ℕ) : Prop :=
  (∀ t < 16, ∀ k, fld Y (16 * k + t) = fld (vs t) k) ∧
  (∀ t < 16, ∀ k, fld CE (16 * k + t) = if (R t).testBit (j + k) then 1 else 0) ∧
  (∀ t < 16, vs t < 2 ^ (16 * (4371 - j))) ∧
  (∀ t < 16, ∀ k, fld (vs t) k < m) ∧
  (∀ t < 16, ∀ b, (outs t).testBit b = (decide (j0 ≤ b ∧ b < j) && (R t).testBit b))

theorem fld_lt_of_lt {x n k : ℕ} (hx : x < 2 ^ (16 * n)) (hk : n ≤ k) : fld x k = 0 := fld_of_lt hx hk

theorem eq_of_xor_eq_zero {a b : ℕ} (h : a ^^^ b = 0) : a = b := by
  apply Nat.eq_of_testBit_eq
  intro i
  have := congrArg (Nat.testBit · i) h
  simp only [Nat.testBit_xor, Nat.zero_testBit] at this
  cases ha : a.testBit i <;> cases hb : b.testBit i <;> simp_all

theorem lnOne_lt : lnOne < 2 ^ 256 := by
  have := lt_of_fld (x := lnOne) (n := 16) (fun t ht => by rw [fld_lnOne, ite_eq_right (by omega)])
  exact this

theorem ln_step {e : ℕ} (he1 : 1 ≤ e) (he : e ≤ 8) {j0 j : ℕ} (hj0 : j0 ≤ j) (hj : j < 4371)
    {b : ℕ} (hrow : dyRowOK 4371 j b = true) {S sh p : ℕ}
    (hbind : Nat.land (Nat.shiftRight S sh) lnSM0 = lnSpr (lnKs 16 256) (lnD 16 256) b)
    (hp : p = Nat.land b (nat_lit 65535)) {R : ℕ → ℕ} {Y CE : ℕ} {vs outs : ℕ → ℕ}
    (hrel : LnRel (2 ^ e) j0 j R Y CE vs outs)
    (hbad : Nat.lor (Nat.lor 0 (Nat.land (Nat.land Y lnLM) (Nat.mul (Nat.sub p (nat_lit 1)) lnOne)))
      (Nat.xor (Nat.land (Nat.div (Nat.land Y lnLM) p) lnOne) (Nat.land CE lnLM)) = 0) :
    ∃ vs' outs' : ℕ → ℕ, LnRel (2 ^ e) j0 (j + 1) R
      (Nat.shiftRight (Nat.land (Nat.add Y (Nat.mul (Nat.sub (Nat.mul (2 ^ e) lnOne)
          (Nat.div (Nat.land Y lnLM) p)) (Nat.land (Nat.shiftRight S sh) lnSM0))) (lnMask (2 ^ e)))
        (nat_lit 256))
      (Nat.shiftRight CE (nat_lit 256)) vs' outs' ∧
      ∀ t < 16, ∀ K : ℕ → ℕ → ℕ → ℕ → ℕ,
        dyStep (2 ^ e) (dyMask (2 ^ e)) b K (vs t) (outs t) j 0 = K (vs' t) (outs' t) (j + 1) 0 := by
  obtain ⟨hY, hCE, hvb, hvf, hout⟩ := hrel
  obtain ⟨⟨e', he', hpv⟩, hb, hbf⟩ := dyRowOK_facts (by decide) hrow
  have hb : b < 2 ^ (16 * (4371 - j)) := hb
  have hp' : p = 2 ^ e' := by rw [hp, land65535, hpv]
  have hm0 : 0 < 2 ^ e := Nat.two_pow_pos e
  have hm8 : 2 ^ e ≤ 256 := Nat.pow_le_pow_right (by decide) he
  have hp8 : 2 ^ e' ≤ 128 := Nat.pow_le_pow_right (by decide) he'
  have hbk : ∀ k, fld b k ≤ 128 := fun k => by
    rcases Nat.eq_zero_or_pos k with rfl | hk
    · rw [hpv]
      exact hp8
    · exact (hbf k hk).le
  set x := Nat.land Y lnLM with hx
  have hxf : ∀ t, fld x t = if t < 16 then fld (vs t) 0 else 0 := fun t => by
    rw [hx, show Nat.land Y lnLM = Y &&& lnLM from rfl, fld_land_LM]
    split
    · rename_i ht
      have := hY t ht 0
      rwa [Nat.mul_zero, Nat.zero_add] at this
    · rfl
  obtain ⟨h1, h2⟩ := Nat.or_eq_zero_iff.1 hbad
  have h1' : Nat.land x (Nat.mul (Nat.sub p 1) lnOne) = 0 := (Nat.or_eq_zero_iff.1 h1).2
  have hdiv : ∀ t, fld x t % 2 ^ e' = 0 := by
    intro t
    have := congrArg (fld · t) h1'
    rw [show Nat.land x (Nat.mul (Nat.sub p 1) lnOne) = x &&& ((p - 1) * lnOne) from rfl, fld_land,
      fld_mul _ (fun f => by rw [fld_lnOne]; split <;> omega), fld_lnOne] at this
    rw [show fld 0 t = 0 by simp [fld]] at this
    split at this
    · rw [Nat.mul_one, hp', Nat.and_two_pow_sub_one_eq_mod] at this
      exact this
    · rw [hxf t, ite_eq_right (by omega)]
      rfl
  have hv0div : ∀ t < 16, fld (vs t) 0 % 2 ^ e' = 0 := fun t ht => by
    have := hdiv t
    rwa [hxf, ite_eq_left ht] at this
  set Q := Nat.div x p with hQ
  have hQf : ∀ t, fld Q t = fld x t / 2 ^ e' := fun t => by
    rw [hQ, hp', show Nat.div x (2 ^ e') = x / 2 ^ e' from rfl]
    exact fld_div_of_dvd (by omega) hdiv t
  have hq : ∀ t < 16, fld Q t = fld (vs t) 0 / 2 ^ e' := fun t ht => by
    rw [hQf, hxf, ite_eq_left ht]
  have hpar : ∀ t < 16, fld (vs t) 0 / 2 ^ e' % 2 = if (R t).testBit j then 1 else 0 := by
    intro t ht
    have := congrArg (fld · t) h2
    rw [show Nat.xor (Nat.land Q lnOne) (Nat.land CE lnLM) = (Q &&& lnOne) ^^^ (CE &&& lnLM) from rfl,
      fld_xor, fld_land, fld_lnOne, ite_eq_left ht, fld_land_LM, ite_eq_left ht,
      show fld 0 t = 0 by simp [fld]] at this
    have hc := hCE t ht 0
    rw [Nat.mul_zero, Nat.zero_add, Nat.add_zero] at hc
    rw [← hq t ht, ← Nat.and_one_is_mod, eq_of_xor_eq_zero this, hc]
  set MQ := Nat.mul (2 ^ e) lnOne with hMQ
  have hMQf : ∀ t, fld MQ t = if t < 16 then 2 ^ e else 0 := fun t => by
    rw [hMQ, show Nat.mul (2 ^ e) lnOne = 2 ^ e * lnOne from rfl,
      fld_mul _ (fun f => by rw [fld_lnOne]; split <;> omega), fld_lnOne]
    split <;> simp
  have hQle : ∀ f, fld Q f ≤ fld MQ f := fun f => by
    rw [hMQf, hQf, hxf]
    split
    · rename_i hf
      have := hvf f hf 0
      exact le_trans (Nat.div_le_self _ _) this.le
    · simp
  set NQ := Nat.sub MQ Q with hNQ
  have hNQf : ∀ t, fld NQ t = fld MQ t - fld Q t := fun t => fld_sub t hQle
  have hNQlt : NQ < 2 ^ 256 := by
    have hMQlt : MQ < 2 ^ 256 := by
      have := lt_of_fld (x := MQ) (n := 16) (fun t ht => by rw [hMQf, ite_eq_right (by omega)])
      exact this
    exact lt_of_le_of_lt (Nat.sub_le _ _) hMQlt
  have hNQle : ∀ t, fld NQ t ≤ 256 := fun t => by
    rw [hNQf, hMQf]
    split <;> omega
  have hb8192 : b < 2 ^ (8192 * 16) :=
    lt_of_lt_of_le hb (Nat.pow_le_pow_right (by decide) (by omega))
  have hSb : ∀ f, fld (Nat.land (Nat.shiftRight S sh) lnSM0) f = if f % 16 = 0 then fld b (f / 16) else 0 :=
    fun f => by rw [hbind, fld_spr16 hb8192]
  have hprod : ∀ t < 16, ∀ k, fld (NQ * Nat.land (Nat.shiftRight S sh) lnSM0) (16 * k + t) =
      fld NQ t * fld b k := fun t ht k => by
    rw [fld_mulSpr hNQlt hNQle (fun f hf => by rw [hSb, ite_eq_right hf])
      (fun k => by rw [hSb, ite_eq_left (by omega), Nat.mul_div_cancel_left _ (by decide)]; exact hbk k) ht k,
      hSb, ite_eq_left (by omega), Nat.mul_div_cancel_left _ (by decide)]
  have hprodle : ∀ f, fld (NQ * Nat.land (Nat.shiftRight S sh) lnSM0) f ≤ 256 * 128 := fun f => by
    have hf := Nat.div_add_mod f 16
    rw [show f = 16 * (f / 16) + f % 16 by omega, hprod _ (Nat.mod_lt _ (by decide))]
    exact Nat.mul_le_mul (hNQle _) (hbk _)
  have hYf : ∀ f, fld Y f < 2 ^ e := fun f => by
    have hf := Nat.div_add_mod f 16
    rw [show f = 16 * (f / 16) + f % 16 by omega, hY _ (Nat.mod_lt _ (by decide))]
    exact hvf _ (Nat.mod_lt _ (by decide)) _
  set Y' := Nat.shiftRight (Nat.land (Nat.add Y (Nat.mul NQ (Nat.land (Nat.shiftRight S sh) lnSM0)))
    (lnMask (2 ^ e))) (nat_lit 256) with hY'
  have hY'f : ∀ t < 16, ∀ k, fld Y' (16 * k + t) =
      if k + 1 < 4371 then (fld (vs t) (k + 1) + (2 ^ e - fld Q t) * fld b (k + 1)) % 2 ^ e else 0 := by
    intro t ht k
    rw [hY', show Nat.shiftRight (Nat.land (Nat.add Y (Nat.mul NQ (Nat.land (Nat.shiftRight S sh) lnSM0)))
        (lnMask (2 ^ e))) (nat_lit 256) =
        ((Y + NQ * Nat.land (Nat.shiftRight S sh) lnSM0) &&& lnMask (2 ^ e)) >>> 256 from rfl,
      fld_shr256, fld_land, fld_lnMask hm0 (by omega),
      fld_add _ (fun f => by have := hYf f; have := hprodle f; omega),
      show 16 * k + t + 16 = 16 * (k + 1) + t by ring, hY t ht, hprod t ht, hNQf, hMQf, ite_eq_left ht]
    by_cases hk : k + 1 < 4371
    · rw [ite_eq_left (by omega), ite_eq_left hk, Nat.and_two_pow_sub_one_eq_mod]
    · rw [ite_eq_right (by omega), ite_eq_right hk, Nat.and_zero]
  set vs' : ℕ → ℕ := fun t => if fld (vs t) 0 = 0 then vs t >>> 16
    else ((vs t + (2 ^ e - fld (vs t) 0 / 2 ^ e') * b) &&& dyMask (2 ^ e)) >>> 16 with hvs'
  set outs' : ℕ → ℕ := fun t => if fld (vs t) 0 = 0 then outs t
    else outs t ||| ((fld (vs t) 0 / 2 ^ e' % 2) <<< j) with houts'
  have hvf' : ∀ t < 16, ∀ k, fld (vs' t) k = if k + 1 < 4371 then
      (fld (vs t) (k + 1) + (2 ^ e - fld (vs t) 0 / 2 ^ e') * fld b (k + 1)) % 2 ^ e else 0 := by
    intro t ht k
    rw [hvs']
    simp only
    split
    · rename_i h0
      rw [h0, Nat.zero_div, Nat.sub_zero, fld_shr16, Nat.add_mul_mod_self_left]
      split
      · exact (Nat.mod_eq_of_lt (hvf t ht _)).symm
      · rename_i hk
        exact fld_of_lt (hvb t ht) (by omega)
    · rename_i h0
      have hn : 2 ^ e - fld (vs t) 0 / 2 ^ e' ≤ 256 := le_trans (Nat.sub_le _ _) hm8
      have hmul : ∀ f, (2 ^ e - fld (vs t) 0 / 2 ^ e') * fld b f < 65536 := fun f =>
        lt_of_le_of_lt (Nat.mul_le_mul hn (hbk f)) (by decide)
      rw [fld_shr16, fld_land_dyMask (by omega : e ≤ 16)]
      by_cases hk : k + 1 < 4371
      · rw [ite_eq_left hk, ite_eq_left hk, fld_add _ (fun f => by
          rw [fld_mul _ hmul]
          have := hvf t ht f
          have := Nat.mul_le_mul hn (hbk f)
          omega), fld_mul _ hmul]
      · rw [ite_eq_right hk, ite_eq_right hk]
  refine ⟨vs', outs',
    ⟨fun t ht k => ?_, fun t ht k => ?_, fun t ht => ?_, fun t ht k => ?_, fun t ht b' => ?_⟩,
    fun t ht K => ?_⟩
  ·
    rw [hY'f t ht k, hq t ht, hvf' t ht k]
  ·
    change fld (CE >>> 256) (16 * k + t) = _
    rw [fld_shr256, show 16 * k + t + 16 = 16 * (k + 1) + t by ring, hCE t ht,
      show j + (k + 1) = j + 1 + k by ring]
  ·
    apply lt_of_fld
    intro k hk
    rw [hvf' t ht k]
    split
    · rw [fld_of_lt (hvb t ht) (by omega), fld_of_lt hb (by omega)]
      simp
    · rfl
  ·
    rw [hvf' t ht k]
    split
    · exact Nat.mod_lt _ hm0
    · exact hm0
  ·
    rw [houts']
    simp only
    have hR := hpar t ht
    split
    · rename_i h0
      rw [hout t ht b']
      rw [h0, Nat.zero_div, Nat.zero_mod] at hR
      by_cases hbj : b' = j
      · subst hbj
        have hRj : (R t).testBit b' = false := by
          cases h : (R t).testBit b'
          · rfl
          · rw [h] at hR
            exact absurd hR (by decide)
        rw [hRj]
        simp
      · have : (decide (j0 ≤ b' ∧ b' < j)) = decide (j0 ≤ b' ∧ b' < j + 1) := by
          simp only [decide_eq_decide]
          omega
        rw [this]
    · rename_i h0
      rw [Nat.testBit_or, hout t ht b', testBit_mod2_shl]
      by_cases hbj : b' = j
      · subst hbj
        have : (decide (fld (vs t) 0 / 2 ^ e' % 2 = 1)) = (R t).testBit b' := by
          cases h : (R t).testBit b'
          · rw [h] at hR
            simp [hR]
          · rw [h] at hR
            simp [hR]
        rw [this]
        simp [hj0]
      · simp only [hbj, decide_false, Bool.false_and, Bool.or_false]
        have : (decide (j0 ≤ b' ∧ b' < j)) = decide (j0 ≤ b' ∧ b' < j + 1) := by
          simp only [decide_eq_decide]
          omega
        rw [this]
  ·
    rw [hvs', houts']
    simp only
    cases hx0 : Nat.beq (Nat.land (vs t) (nat_lit 65535)) (nat_lit 0)
    · have h0 : fld (vs t) 0 ≠ 0 := by
        intro h
        rw [land65535, h] at hx0
        exact absurd hx0 (by decide)
      rw [dyStep_ne _ _ _ _ _ _ _ _ hx0, land65535, land65535, hpv, ite_eq_right h0, ite_eq_right h0]
      have hbad0 : Nat.lor 0 (Nat.land (fld (vs t) 0) (Nat.sub (2 ^ e') 1)) = 0 := by
        change 0 ||| (fld (vs t) 0 &&& (2 ^ e' - 1)) = 0
        rw [Nat.zero_or, Nat.and_two_pow_sub_one_eq_mod, hv0div t ht]
      rw [hbad0]
      change K (((vs t + (2 ^ e - fld (vs t) 0 / 2 ^ e') * b) &&& dyMask (2 ^ e)) >>> 16)
        (outs t ||| ((fld (vs t) 0 / 2 ^ e' &&& 1) <<< j)) (j + 1) 0 = _
      rw [Nat.and_one_is_mod]
    · have h0 : fld (vs t) 0 = 0 := by
        rw [land65535] at hx0
        exact Nat.eq_of_beq_eq_true hx0
      rw [dyStep_zero _ _ _ _ _ _ _ _ hx0, ite_eq_left h0, ite_eq_left h0]
      rfl

end CFSG.KC.BM.Ln

end
