module

public import CFSG.Certificates.Kernel.S1277KMLPrim
import Mathlib.Analysis.SpecialFunctions.Pow.NNReal
import Mathlib.Tactic.Basify
import Mathlib.Tactic.ENatToNat
import Mathlib.Tactic.Echelon.Zsqrtd
import Mathlib.Tactic.Inclusion.Extension.Core.Core
import Mathlib.Tactic.Inclusion.Extension.IntervalDyadicReal.Hypotheses
import Mathlib.Tactic.Inclusion.Extension.IntervalDyadicReal.Rational
import Mathlib.Tactic.Measurability.Init
import Mathlib.Tactic.NormNum.Irrational
import Mathlib.Tactic.NormNum.IsCoprime
import Mathlib.Tactic.NormNum.IsSquare
import Mathlib.Tactic.NormNum.LegendreSymbol
import Mathlib.Tactic.NormNum.ModEq
import Mathlib.Tactic.NormNum.NatFib
import Mathlib.Tactic.NormNum.NatLog
import Mathlib.Tactic.NormNum.NatSqrt
import Mathlib.Tactic.NormNum.Ordinal
import Mathlib.Tactic.NormNum.Parity
import Mathlib.Tactic.NormNum.Prime
import Mathlib.Tactic.NormNum.RealSqrt

public section

namespace CFSG.KS.S1277ML

open CFSG.Quasithin.H13.S127.Mod CFSG.KC.S1277Gm CFSG.KC.S1277ML CFSG.KS.S1277Gm
open Certificates.Data.S1277MLine

theorem osChk_sound (P : List ℕ) (m18 m45 : ℕ) (h : osChk P m18 m45 = true) (c : ℕ) (hc : c < 64) :
    (Certificates.Data.S1277MLine.orbitSize (P.map B6.ofP) c = 18 ↔ bitN m18 c = true) ∧
      (Certificates.Data.S1277MLine.orbitSize (P.map B6.ofP) c = 45 ↔ bitN m45 c = true) := by
  have hall : (Nat.beq (pcN (imgM P c)) 18 == bitN m18 c) = true ∧
      (Nat.beq (pcN (imgM P c)) 45 == bitN m45 c) = true := by
    have h' := allBelow_true _ _ h c hc
    rw [strictB_ml, andB_eq, eqB_eq, eqB_eq, Bool.and_eq_true] at h'
    exact h'
  rw [orbitSize_pcN]
  obtain ⟨h1, h2⟩ := hall
  rw [beq_iff_eq] at h1 h2
  rw [← h1, ← h2, Nat.beq_eq, Nat.beq_eq]
  exact ⟨Iff.rfl, Iff.rfl⟩

theorem ofP_id : B6.ofP 34630287489 = B6.id := rfl

theorem isInvP_iff (p : ℕ) :
    isInvP p = true ↔ (B6.ofP p).comp (B6.ofP p) = B6.id ∧ p ≠ 34630287489 := by
  unfold isInvP isIdP
  rw [land63, fldN_eq, fldN_eq, fldN_eq, fldN_eq, fldN_eq]
  simp only [andB_eq, notB_eq, Bool.and_eq_true, Nat.beq_eq, Bool.not_eq_true', appQ_eq,
    B6.comp, B6.id, B6.mk.injEq, Bool.eq_false_iff, ne_eq]
  simp only [B6.ofP]
  tauto

theorem fixList_id : (fixList B6.id).length = 64 := by decide

theorem invL_eq (Q : List ℕ) : invL Q = (Q.filter isInvP).map fixMP := by
  induction Q with
  | nil => rfl
  | cons p Q ih =>
    change Bool.rec (motive := fun _ => List ℕ) (invL Q) (fixMP p :: invL Q) (isInvP p) = _
    rw [ih, List.filter_cons]
    cases isInvP p
    · rfl
    · rfl

theorem land_eq_self {m m' : ℕ} :
    Nat.land m m' = m ↔ ∀ i, m.testBit i = true → m'.testBit i = true := by
  change m &&& m' = m ↔ _
  constructor
  · intro h i hi
    have := congrArg (fun x => x.testBit i) h
    simp only [Nat.testBit_and, hi, Bool.true_and] at this
    exact this
  · intro h
    apply Nat.eq_of_testBit_eq
    intro i
    rw [Nat.testBit_and]
    cases hi : m.testBit i
    · rfl
    · rw [h i hi]
      rfl

theorem land_lt (m m' : ℕ) (hm : m < 2 ^ 64) : m &&& m' < 2 ^ 64 := by
  rw [Nat.and_comm]
  exact Nat.and_lt_two_pow _ hm

theorem pcN_bits (t : ℕ) (ht : t < 2 ^ 64) :
    ((List.range 64).filter fun c => t.testBit c).length = pcN t := by
  rw [pcN_eq _ ht, pc64]

theorem perD_of (Q : List ℕ) (m18 m45 : ℕ)
    (h18 : ∀ c < 64, (orbitSize gm6 c = 18 ↔ bitN m18 c = true))
    (h45 : ∀ c < 64, (orbitSize gm6 c = 45 ↔ bitN m45 c = true))
    (hQ : ∀ p ∈ Q, isInvP p = isInv (B6.ofP p)) (p₀ : ℕ)
    (h : perDP Q (invL Q) (fixMP p₀) m18 m45 = true) :
    perD (Q.map B6.ofP) (fixList (B6.ofP p₀)) = true := by
  set m := fixMP p₀ with hm
  set D := fixList (B6.ofP p₀) with hDdef
  have hm64 : m < 2 ^ 64 := fixMP_lt p₀
  have hDf : D = (List.range 64).filter fun c => m.testBit c := fixList_eq p₀
  have hD : ∀ x, x ∈ D ↔ m.testBit x = true := by
    intro x
    rw [hDf, List.mem_filter, List.mem_range]
    exact ⟨fun h => h.2, fun h => ⟨((testBit_fixMP p₀ x).1 h).1, h⟩⟩
  have hbits : bitsBelow m 64 [] = D := by rw [bitsBelow_eq, List.append_nil, hDf]
  have hcnt : cntSup (invL Q) m = (invsD (Q.map B6.ofP) D).length := by
    rw [cntSup, cntL_eq, List.countP_eq_length_filter, invL_eq, List.filter_map, List.length_map,
      List.filter_filter, invsD, List.filter_map, List.length_map]
    congr 1
    apply List.filter_congr
    intro p hp
    simp only [Function.comp]
    rw [hQ p hp]
    apply Bool.eq_iff_iff.2
    simp only [Bool.and_eq_true, Nat.beq_eq, land_eq_self, List.all_eq_true, beq_iff_eq, hD,
      testBit_fixMP]
    constructor
    · rintro ⟨h1, h2⟩
      exact ⟨h2, fun d hd => (h1 d hd).2⟩
    · rintro ⟨h1, h2⟩
      exact ⟨fun d hd => ⟨((testBit_fixMP p₀ d).1 hd).1, h2 d hd⟩, h1⟩
  have horb : ∀ (n : ℕ) (mn : ℕ), (∀ c < 64, (orbitSize gm6 c = n ↔ bitN mn c = true)) →
      orbD D n = bitsBelow (m &&& mn) 64 [] := by
    intro n mn hn
    rw [bitsBelow_eq, List.append_nil, orbD, hDf, List.filter_filter]
    apply List.filter_congr
    intro c hc
    have hc' : c < 64 := List.mem_range.1 hc
    rw [Nat.testBit_and]
    apply Bool.eq_iff_iff.2
    rw [Bool.and_eq_true, Bool.and_eq_true, beq_iff_eq, hn c hc', bitN_eq]
    exact And.comm
  have hO18 := horb 18 m18 h18
  have hO45 := horb 45 m45 h45
  have hstab : stabD (Q.map B6.ofP) D = (stabL Q m (bitsBelow m 64 [])).map B6.ofP := by
    rw [stabD, List.filter_map, stabL, filtL_eq, hbits]
    refine congrArg (List.map B6.ofP) (List.filter_congr fun p _ => ?_)
    simp only [Function.comp]
    rw [allL_eq]
    apply Bool.eq_iff_iff.2
    simp only [List.all_eq_true, List.contains_iff_mem, hD, bitN_eq, appQ_eq]
  rw [perDP, strictB_ml, andB_eq, orB_eq, Bool.and_eq_true, Bool.or_eq_true, Nat.ble_eq,
    Nat.blt_eq, hcnt] at h
  obtain ⟨hle, hlt | hS⟩ := h
  · rw [perD]
    simp [hle, hlt]
  set S := stabL Q m (bitsBelow m 64 []) with hSdef
  rw [stabFacts, strictB_ml, andB_eq, andB_eq, Bool.and_eq_true, Bool.and_eq_true, Nat.ble_eq,
    allL_eq, anyL_eq, List.all_eq_true, List.any_eq_true] at hS
  obtain ⟨h4, htr, c, hc, h9⟩ := hS
  have ht18 : m &&& m18 < 2 ^ 64 := land_lt _ _ hm64
  have hlen : (orbD D 18).length = pcN (m &&& m18) := by
    rw [hO18, bitsBelow_eq, List.append_nil, pcN_bits _ ht18]
  rw [perD, hstab, hO18, hO45]
  rw [hO18] at hlen
  simp only [Bool.and_eq_true, Bool.or_eq_true, decide_eq_true_eq, List.all_eq_true,
    List.any_eq_true, beq_iff_eq, List.mem_map]
  refine ⟨hle, Or.inr ⟨⟨?_, ?_⟩, ?_⟩⟩
  · rw [hlen]
    exact h4
  · intro t ht s hs
    have h1 := htr t ht
    rw [Nat.beq_eq, land_eq_self] at h1
    rw [bitsBelow_eq, List.append_nil, List.mem_filter] at hs
    obtain ⟨y, hy, hys⟩ := (testBit_maskF _ _ s).1 (h1 s hs.2)
    exact ⟨B6.ofP y, ⟨y, hy, rfl⟩, by rw [← appQ_eq]; exact hys⟩
  · refine ⟨c, hc, ?_⟩
    have e : (dedupN ((S.map B6.ofP).map fun B => B.app c)).length =
        orbitSize (S.map B6.ofP) c := rfl
    rw [e, orbitSize_pcN]
    rw [Nat.ble_eq] at h9
    exact h9

theorem mChk_sound (Q : List ℕ) (m18 m45 : ℕ)
    (h18 : ∀ c < 64, (Certificates.Data.S1277MLine.orbitSize gm6 c = 18 ↔ bitN m18 c = true))
    (h45 : ∀ c < 64, (Certificates.Data.S1277MLine.orbitSize gm6 c = 45 ↔ bitN m45 c = true))
    (h : mChk Q m18 m45 = true) :
    Certificates.Data.S1277MLine.mCheck (Q.map B6.ofP) () = true := by
  change mChkI Q (invL Q) m18 m45 = true at h
  rw [mChkI, andB_eq, Bool.and_eq_true, allL_eq, allL_eq, List.all_eq_true, List.all_eq_true] at h
  obtain ⟨hA, hB⟩ := h
  have hmem : ∀ p ∈ Q, isInvP p = true → fixMP p ∈ invL Q := fun p hp hi => by
    rw [invL_eq]
    exact List.mem_map_of_mem (List.mem_filter.2 ⟨hp, hi⟩)
  have hne : ∀ p ∈ Q, isInvP p = true → B6.ofP p ≠ B6.id := by
    intro p hp hi he
    have h1 := hA _ (hmem p hp hi)
    rw [Nat.ble_eq, pcN_fixMP, he, fixList_id] at h1
    exact absurd h1 (by decide)
  have hQ : ∀ p ∈ Q, isInvP p = isInv (B6.ofP p) := by
    intro p hp
    apply Bool.eq_iff_iff.2
    rw [isInvP_iff]
    simp only [isInv, Bool.and_eq_true, beq_iff_eq, bne_iff_ne, ne_eq]
    constructor
    · rintro ⟨h1, h2⟩
      exact ⟨h1, hne p hp ((isInvP_iff p).2 ⟨h1, h2⟩)⟩
    · rintro ⟨h1, h2⟩
      refine ⟨h1, fun he => h2 ?_⟩
      rw [he]
      exact ofP_id
  rw [mCheck, Bool.and_eq_true, List.all_eq_true, List.all_eq_true]
  refine ⟨fun B hBm => ?_, fun B hBm => ?_⟩
  · obtain ⟨p, hp, rfl⟩ := List.mem_map.1 hBm
    cases hi : isInv (B6.ofP p)
    · rfl
    · have h1 := hA _ (hmem p hp ((hQ p hp).trans hi))
      rw [Nat.ble_eq, pcN_fixMP] at h1
      simp [h1]
  · obtain ⟨p, hp, rfl⟩ := List.mem_map.1 hBm
    cases hi : isInv (B6.ofP p)
    · rfl
    · by_cases hl : (fixList (B6.ofP p)).length = 16
      · have h1 := hB _ (hmem p hp ((hQ p hp).trans hi))
        rw [orB_eq, notB_eq, Bool.or_eq_true, Bool.not_eq_true', pcN_fixMP, hl] at h1
        rcases h1 with h1 | h1
        · exact absurd h1 (by decide)
        · rw [perD_of Q m18 m45 h18 h45 hQ p h1]
          simp
      · simp [hl]

end CFSG.KS.S1277ML

end
