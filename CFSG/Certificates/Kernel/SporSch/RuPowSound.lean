module

import CFSG.Certificates.Kernel.Spor.PackFld
import CFSG.Certificates.Kernel.Spor.RawSiftK
public import CFSG.Certificates.Kernel.Spor.Loops
public import CFSG.Certificates.Kernel.Spor.RawDefs
public import CFSG.Sporadic.Schreier.RuCore
public import Certificates.Data.Kernel.SporSch.RuK
public import Mathlib.Data.Nat.Totient
public import Mathlib.Data.Rat.Floor
public import Mathlib.Data.Sym.Sym2.Init
public import Mathlib.Tactic.NormNum.GCD

public section

namespace CFSG.KS.SporSch

open CFSG.KC.Enum CFSG.KS CFSG.KS.Raw CFSG.Sporadic.RuSchreier CFSG.Monster.B.Co2.Native

private theorem pg_high {n w p j : Nat} (hp : Nat.shiftRight p (n * w) = 0) (hj : n ≤ j) :
    pg w (mask w) p j = 0 := by
  apply Nat.eq_of_testBit_eq
  intro k
  rw [CFSG.KS.PackFld.testBit_pgM, Nat.zero_testBit]
  by_cases hk : k < w
  · have e : p >>> (n * w) = 0 := hp
    have h1 : p.testBit (n * w + (w * j + k - n * w)) = false := by
      rw [← Nat.testBit_shiftRight, e, Nat.zero_testBit]
    have h2 : n * w + (w * j + k - n * w) = w * j + k := by
      have := Nat.mul_le_mul_left w hj
      rw [Nat.mul_comm w n] at this
      omega
    rw [h2] at h1
    simp [h1]
  · simp [hk]

private theorem unpack_pcomp {n w p q : Nat}
    (hc : CFSG.KS.Prim.canonK n w (mask w) (n * w) p = true) :
    unpack n w (pcomp n w (mask w) p q) = compA n (unpack n w p) (unpack n w q) := by
  unfold CFSG.KS.Prim.canonK at hc
  rw [bAnd_iff, bAnd_iff, Nat.beq_eq] at hc
  obtain ⟨hsz, hshr, -⟩ := hc
  have hn : n < 2 ^ 32 := by
    have := (CFSG.KS.Raw.Orb.szOK_facts hsz).1
    omega
  apply Array.ext
  · simp [unpack, compA]
  · intro i h1 _
    have hi : i < n := by simpa [unpack] using h1
    simp only [unpack, compA, Array.getElem_ofFn]
    rw [CFSG.KS.PackFld.pg_pcomp hn hi, getElem!_pos _ i (by simpa using hi), Array.getElem_ofFn]
    by_cases hq : pg w (mask w) q i < n
    · rw [getElem!_pos _ _ (by simpa using hq), Array.getElem_ofFn]
    · rw [getElem!_neg _ _ (by simpa using hq), pg_high hshr (by omega)]
      rfl

theorem powAppRK_sound {n w p e k P r : Nat} (hP : powA n (unpack n w p) k = unpack n w P)
    (h : powEqRK n w (mask w) (n * w) P p e r = true) :
    powA n (unpack n w p) (e + k) = unpack n w r := by
  unfold powEqRK at h
  rw [bAnd_iff, Nat.beq_eq] at h
  obtain ⟨hc, rfl⟩ := h
  induction e with
  | zero => rw [Nat.zero_add, hP]; rfl
  | succ e ih =>
    rw [Nat.add_right_comm, powA, ih]
    change _ = unpack n w (strictN (ppow n w (mask w) P p e) (fun q => pcomp n w (mask w) p q))
    rw [CFSG.KS.PackFld.strictN_eqP, unpack_pcomp hc]

theorem pow_chain {n w x c K : Nat} {Q : Nat → Nat} (h0 : unpack n w (Q 0) = idA n)
    (hs : ∀ q < K, powEqRK n w (mask w) (n * w) (Q q) x c (Q (q + 1)) = true) :
    ∀ q ≤ K, powA n (unpack n w x) (c * q) = unpack n w (Q q) := by
  intro q
  induction q with
  | zero =>
    intro _
    rw [Nat.mul_zero, h0]
    all_goals rfl
  | succ q ih =>
    intro hq
    rw [Nat.mul_succ, Nat.add_comm]
    exact powAppRK_sound (ih (by omega)) (hs q (by omega))

end CFSG.KS.SporSch

end
