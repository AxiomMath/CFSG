module

public import CFSG.Certificates.Kernel.Fi22Rk.PbChecks
import CFSG.Certificates.Kernel.Fi24Pl.Sound

public section

namespace CFSG.KC.Fi22RkS

open CFSG.KC.Enum CFSG.KC.Fi22Rk CFSG.KS CFSG.KS.Raw
open CFSG.Monster.B.Co2 CFSG.Monster.B.Co2.Native
open CFSG.LocalAnalysis.GLTheoremA.H1017.Fi24RankNative
open CFSG.KLie.CT (orB notB)

variable {n w C q : Nat} {I : Array (Array Nat)} {IK SMK CLK CMK POK POIK STK WK : Nat → Nat}

theorem strictMono_of_succ {f : Nat → Nat} {C : Nat} (h : ∀ c < C - 1, f c < f (c + 1)) :
    ∀ a < C, ∀ b < C, a < b → f a < f b := by
  intro a ha b hb hab
  induction b with
  | zero => exact absurd hab (Nat.not_lt_zero a)
  | succ b ih =>
    rcases Nat.lt_succ_iff_lt_or_eq.1 hab with h1 | rfl
    · exact lt_trans (ih (by omega) h1) (h b (by omega))
    · exact h a (by omega)

theorem class_inj (h : classK n C SMK CLK CMK = true) {p q : Nat} (hp : p < n) (hq : q < n)
    (e : SMK p = SMK q) : CLK p = CLK q := by
  unfold classK at h
  obtain ⟨h1, h2⟩ := (bAnd_iff _ _).1 h
  have hm := strictMono_of_succ (f := CMK) (C := C) fun c hc => Nat.blt_eq.mp (allN_spec h2 c hc)
  have a1 := allN_spec h1 p hp
  have a2 := allN_spec h1 q hq
  rw [strictB_eq] at a1 a2
  obtain ⟨b1, c1⟩ := (bAnd_iff _ _).1 a1
  obtain ⟨b2, c2⟩ := (bAnd_iff _ _).1 a2
  have e1 := Nat.eq_of_beq_eq_true c1
  have e2 := Nat.eq_of_beq_eq_true c2
  have hb1 := Nat.blt_eq.mp b1
  have hb2 := Nat.blt_eq.mp b2
  rcases lt_trichotomy (CLK p) (CLK q) with l | l | l
  · have := hm _ hb1 _ hb2 l
    omega
  · exact l
  · have := hm _ hb2 _ hb1 l
    omega

theorem stab_bit (hI : ∀ i < 243, ∀ x < n, (I[i]!)[x]! = pg w (mask w) (IK i) x)
    (h : stabAt w IK SMK q = true) {i : Nat} (hi : i < 243) (hq : q < n) :
    Nat.testBit (SMK q) i = ((I[i]!)[q]! == q) := by
  unfold stabAt at h
  rw [strictB_eq] at h
  obtain ⟨-, h2⟩ := (bAnd_iff _ _).1 h
  have h3 := Nat.eq_of_beq_eq_true (allN_spec h2 i hi)
  rw [CFSG.KC.Fi24PlS.fld_one_eq] at h3
  rw [hI i hi q hq, ← CFSG.KC.Fi24PlS.nbeq]
  cases hb : Nat.testBit (SMK q) i <;> cases hc : Nat.beq (pg w (mask w) (IK i) q) q <;>
    rw [hb, hc] at h3 <;> revert h3 <;> decide

theorem stab_top (h : stabAt w IK SMK q = true) : SMK q >>> 243 = 0 := by
  unfold stabAt at h
  rw [strictB_eq] at h
  exact Nat.eq_of_beq_eq_true ((bAnd_iff _ _).1 h).1

theorem stabs_get {p : Nat} (hp : p < n) : (stabs n I)[p]! = stabList I p := by
  unfold stabs
  rw [getElem!_pos _ p (by simpa using hp), Array.getElem_ofFn]

theorem mem_stabList {p i : Nat} : i ∈ stabList I p ↔ i < 243 ∧ ((I[i]!)[p]! == p) = true := by
  unfold stabList
  rw [List.mem_filter, List.mem_range]

theorem uniqAt_of (hI : ∀ i < 243, ∀ x < n, (I[i]!)[x]! = pg w (mask w) (IK i) x)
    (hIr : ∀ i < 243, ∀ x < n, pg w (mask w) (IK i) x < n)
    (hstab : ∀ q < n, stabAt w IK SMK q = true) (hcls : classK n C SMK CLK CMK = true)
    (hblk : blockK n CLK POK POIK STK = true) {q : Nat} (hq : q < n)
    (hu : uniqAtK w IK CLK POK STK WK q = true) : uniqAt n I (stabs n I) q = true := by
  unfold uniqAtK at hu
  rw [strictB_eq, strictB_eq, strictB_eq] at hu
  obtain ⟨u1, u2⟩ := (bAnd_iff _ _).1 hu
  unfold blockK at hblk
  obtain ⟨k1, k2⟩ := (bAnd_iff _ _).1 hblk
  unfold uniqAt
  rw [Bool.and_eq_true, allLt_iff, allLt_iff]
  constructor
  · intro q' hq'
    rw [Bool.or_eq_true]
    by_cases hS : (stabs n I)[q']! = (stabs n I)[q]!
    · right
      have hm : SMK q' = SMK q := by
        refine CFSG.KC.Fi24PlS.bits_eq (stab_top (hstab q' hq')) (stab_top (hstab q hq))
          fun i hi => ?_
        rw [stab_bit hI (hstab q' hq') hi hq', stab_bit hI (hstab q hq) hi hq]
        rw [stabs_get hq', stabs_get hq] at hS
        have := congrArg (fun l => i ∈ l) hS
        simp only [mem_stabList, hi, true_and, eq_iff_iff] at this
        exact Bool.eq_iff_iff.mpr this
      have hc := class_inj hcls hq' hq hm
      have b2 := allN_spec k2 q' hq'
      obtain ⟨b3, b4⟩ := (bAnd_iff _ _).1 b2
      have hs := Nat.blt_eq.mp b3
      have hpo := Nat.eq_of_beq_eq_true b4
      have b5 := allN_spec k1 (POIK q') hs
      rw [strictB_eq, hpo] at b5
      obtain ⟨-, b6⟩ := (bAnd_iff _ _).1 b5
      obtain ⟨-, b7⟩ := (bAnd_iff _ _).1 b6
      rw [strictB_eq, hc] at b7
      obtain ⟨b8, b9⟩ := (bAnd_iff _ _).1 b7
      have hlo := Nat.ble_eq.mp b8
      have hhi : POIK q' < STK (CLK q + 1) := Nat.blt_eq.mp b9
      have w1 := allN_spec u1 (POIK q' - STK (CLK q))
        (by change _ < STK (CLK q + 1) - STK (CLK q); omega)
      rw [strictB_eq] at w1
      obtain ⟨w2, w3⟩ := (bAnd_iff _ _).1 w1
      rw [anyLt_iff' ]
      refine ⟨_, Nat.blt_eq.mp w2, ?_⟩
      have e : Nat.add (STK (CLK q)) (POIK q' - STK (CLK q)) = POIK q' := by
        change STK (CLK q) + (POIK q' - STK (CLK q)) = POIK q'
        omega
      rw [hI _ (Nat.blt_eq.mp w2) q hq, Nat.eq_of_beq_eq_true w3, e, hpo]
      exact beq_self_eq_true _
    · left
      rw [bne_iff_ne]
      exact hS
  · intro i hi
    have v := allN_spec u2 i hi
    rw [strictB_eq, orB_eq', notB_eq, Bool.or_eq_true, Bool.not_eq_true'] at v
    have hy := hIr i hi q hq
    rw [hI i hi q hq, hI i hi _ hy, Bool.or_eq_true, bne_iff_ne, ne_eq, beq_iff_eq]
    rcases v with v | v
    · left
      intro e
      rw [e, Nat.beq_refl] at v
      exact absurd v (by decide)
    · right
      exact Nat.eq_of_beq_eq_true v

end CFSG.KC.Fi22RkS

end
