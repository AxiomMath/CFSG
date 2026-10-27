module

public import Certificates.Data.Kernel.GmsEdgeK
public import CFSG.Certificates.Kernel.Co1M.GmsWitSound
public import CFSG.Certificates.Kernel.Co1F2Sound
public import Certificates.Data.CFSGNative.Co1.EdgeSq
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

namespace CFSG.KC.GmsPath

open CFSG.KLie.CT CFSG.KC.Loop CFSG.KC.M1F2 CFSG.KC.Co1F2 CFSG.Sporadic.SmallF2.Native
  CFSG.Sporadic.Co1.EdgeSqNative CFSG.Sporadic.Co1.S365UNative

theorem unpackR_rowF (M j : Nat) (hj : j < 24) :
    (unpackR 24 M)[j]?.getD 0 = rowF 24 M j := by
  simp only [unpackR, Array.getElem?_ofFn, hj, ↓reduceDIte, Option.getD_some]
  change M / 2 ^ (24 * j) % 2 ^ 24 = (M >>> (j * 24)) &&& (1 <<< 24 - 1)
  rw [Nat.shiftLeft_eq, Nat.one_mul, Nat.and_two_pow_sub_one_eq_mod, Nat.shiftRight_eq_div_pow,
    Nat.mul_comm j 24]

theorem vecMulN_unpackR (M v : Nat) : vecMulN 24 (unpackR 24 M) v = vmF 24 M v :=
  vecMulN_eq_vmF (fun j hj => unpackR_rowF M j hj) v

theorem anyPar_iff (YL : List Nat) (a : Nat) :
    anyPar YL a = true ↔ ∃ y ∈ YL, parF (a &&& y) = true := by
  induction YL with
  | nil => exact ⟨fun h => Bool.noConfusion h, fun ⟨_, h, _⟩ => absurd h List.not_mem_nil⟩
  | cons y L ih =>
    change orB (parF (Nat.land a y)) (anyPar L a) = true ↔ _
    rw [orB_eq, Bool.or_eq_true, ih, List.exists_mem_cons_iff]
    rfl

theorem memFst_iff (ALP : List (Nat × Nat)) (a : Nat) :
    memFst ALP a = true ↔ ∃ c, (a, c) ∈ ALP := by
  induction ALP with
  | nil => exact ⟨fun h => Bool.noConfusion h, fun ⟨_, h⟩ => absurd h List.not_mem_nil⟩
  | cons e L ih =>
    obtain ⟨x, c⟩ := e
    change orB (Nat.beq x a) (memFst L a) = true ↔ _
    rw [orB_eq, Bool.or_eq_true, ih, beq_dec, decide_eq_true_iff]
    constructor
    · rintro (rfl | ⟨c', h⟩)
      · exact ⟨c, List.mem_cons_self⟩
      · exact ⟨c', List.mem_cons_of_mem _ h⟩
    · rintro ⟨c', h⟩
      rcases List.mem_cons.1 h with h | h
      · exact Or.inl (Prod.mk.inj h).1.symm
      · exact Or.inr ⟨c', h⟩

theorem crdOK_spec {D : Nat} {ALP : List (Nat × Nat)} (h : crdOK D ALP = true) {a c : Nat}
    (hm : (a, c) ∈ ALP) : vmF 24 D a = c := by
  induction ALP with
  | nil => exact absurd hm List.not_mem_nil
  | cons e L ih =>
    obtain ⟨x, c'⟩ := e
    change andB (Nat.beq (vmF 24 D x) c') (crdOK D L) = true at h
    rw [andB_eq, Bool.and_eq_true, beq_dec, decide_eq_true_iff] at h
    rcases List.mem_cons.1 hm with hm | hm
    · obtain ⟨rfl, rfl⟩ := Prod.mk.inj hm
      exact h.1
    · exact ih h.2 hm

theorem pairsK_spec {FM cb : Nat} {g : Nat → Bool} {ALP : List (Nat × Nat)}
    (h : pairsK FM cb g ALP = true) {a c : Nat} (hm : (a, c) ∈ ALP)
    (hb : bit FM (Nat.xor c cb) = true) : g a = true := by
  induction ALP with
  | nil => exact absurd hm List.not_mem_nil
  | cons e L ih =>
    obtain ⟨x, c'⟩ := e
    change andB (orB (notB (bit FM (Nat.xor c' cb))) (g x)) (pairsK FM cb g L) = true at h
    rw [andB_eq, Bool.and_eq_true, orB_eq, notB_eq] at h
    rcases List.mem_cons.1 hm with hm | hm
    · obtain ⟨rfl, rfl⟩ := Prod.mk.inj hm
      have h1 := h.1
      rw [hb, Bool.not_true, Bool.false_or] at h1
      exact h1
    · exact ih h.2 hm

theorem bChk_spec {T F0 FM : Nat} {BA ALP : List (Nat × Nat)} {b cb : Nat}
    (h : bChk T F0 FM BA ALP b cb = true) {a c : Nat} (hm : (a, c) ∈ ALP)
    (hb : bit FM (Nat.xor c cb) = true) :
    ∃ y, memPre BA b = some y ∧ y ^^^ vmF 24 T y = b ∧ parF (a &&& vmF 24 F0 y) = true := by
  unfold bChk at h
  rw [orB_eq, Bool.or_eq_true] at h
  rcases h with h | h
  · exact absurd (pairsK_spec h hm hb) Bool.false_ne_true
  · revert h
    cases memPre BA b with
    | none =>
      intro h
      exact absurd h Bool.false_ne_true
    | some y =>
      intro h
      change andB (Nat.beq (Nat.xor y (vmF 24 T y)) b) (strictB (vmF 24 F0 y) fun z =>
        pairsK FM cb (fun a => parF (Nat.land a z)) ALP) = true at h
      rw [andB_eq, Bool.and_eq_true, beq_dec, decide_eq_true_iff, strictB_eq] at h
      exact ⟨y, rfl, h.1, pairsK_spec h.2 hm hb⟩

theorem edgeV_spec {T D F0 FM : Nat} {YL : List Nat} {BA ALP : List (Nat × Nat)} {v : Nat}
    (h : edgeV T D F0 FM YL BA ALP v = true) (hf : vmF 24 T v = v) :
    bit FM (vmF 24 D v) = true ∧ (anyPar YL v = true ∨ ∃ c, (v, c) ∈ ALP) ∧
      bChk T F0 FM BA ALP v (vmF 24 D v) = true := by
  change orB (notB (Nat.beq (vmF 24 T v) v)) (strictB (vmF 24 D v) fun cb => andB (bit FM cb)
      (andB (orB (anyPar YL v) (memFst ALP v)) (bChk T F0 FM BA ALP v cb))) = true at h
  have hb : Nat.beq (vmF 24 T v) v = true := by
    rw [beq_dec, decide_eq_true_iff]
    exact hf
  rw [hb, strictB_eq, orB_eq, notB_eq, andB_eq, andB_eq, orB_eq, Bool.not_true, Bool.false_or,
    Bool.and_eq_true, Bool.and_eq_true, Bool.or_eq_true] at h
  exact ⟨h.1, h.2.1.imp_right (memFst_iff ALP v).1, h.2.2⟩

theorem edgeCheckN_of {qr f0t pts : Array Nat} {pos : Array UInt32} {n : Nat} {S : Array Nat}
    {T D F0 FM : Nat} {X YL : List Nat} {BA ALP : List (Nat × Nat)} {P : Nat → Nat}
    (hMt : transposeRows 24 S = unpackR 24 T) (hf0 : f0t = unpackR 24 F0)
    (hX : kerList (unpackR 24 T) = X) (hB : imBasis (unpackR 24 T) = BA)
    (hY : YL = X.map (vmF 24 F0))
    (hXok : (X.all fun x => decide (x < 2 ^ 24) &&
      CFSG.Sporadic.Co1.InvNative.isFixedN (unpackR 24 T) x) = true)
    (hcrd : crdOK D ALP = true)
    (hpts : ∀ i < n, pts[i]! = P i)
    (hsw : ∀ i < n, edgeV T D F0 FM YL BA ALP (P i) = true) :
    edgeCheckN qr f0t pts pos n S = true := by
  have fixE : ∀ v, CFSG.Sporadic.Co1.InvNative.isFixedN (unpackR 24 T) v = true ↔
      vmF 24 T v = v := by
    intro v
    unfold CFSG.Sporadic.Co1.InvNative.isFixedN
    rw [vecMulN_unpackR, beq_iff_eq]
  have bilE : ∀ a y, bil0N f0t a y = parF (a &&& vmF 24 F0 y) := by
    intro a y
    unfold bil0N
    rw [hf0, vecMulN_unpackR, parity24N_eq]
  have hin : ∀ w, CFSG.Sporadic.Co1.S365Native.inPtsN pts pos n w = true → ∃ i < n, P i = w := by
    intro w hw
    unfold CFSG.Sporadic.Co1.S365Native.inPtsN at hw
    rw [Bool.and_eq_true, decide_eq_true_eq, beq_iff_eq] at hw
    exact ⟨_, hw.1, (hpts _ hw.1).symm.trans hw.2⟩
  unfold edgeCheckN
  simp only [hMt, hX, hB]
  rw [Bool.and_eq_true]
  refine ⟨hXok, ?_⟩
  rw [List.all_eq_true]
  intro p hp
  rw [List.all_eq_true]
  intro p' hp'
  unfold fixedIdx at hp hp'
  rw [List.mem_filter, List.mem_range] at hp hp'
  have hfa := (fixE _).1 (hpts p hp.1 ▸ hp.2)
  have hfb := (fixE _).1 (hpts p' hp'.1 ▸ hp'.2)
  rw [hpts p hp.1, hpts p' hp'.1]
  obtain ⟨-, ha2, -⟩ := edgeV_spec (hsw p hp.1) hfa
  obtain ⟨-, -, hb3⟩ := edgeV_spec (hsw p' hp'.1) hfb
  unfold pairOKN
  rw [Bool.or_eq_true, Bool.or_eq_true]
  rcases ha2 with hany | ⟨c, hc⟩
  · left
    right
    obtain ⟨y, hy, hpy⟩ := (anyPar_iff YL (P p)).1 hany
    rw [hY, List.mem_map] at hy
    obtain ⟨x, hx, rfl⟩ := hy
    rw [List.any_eq_true]
    exact ⟨x, hx, (bilE _ _).trans hpy⟩
  · have hca := crdOK_spec hcrd hc
    by_cases hbit : bit FM (Nat.xor c (vmF 24 D (P p'))) = true
    · right
      obtain ⟨y, hy, hyb, hpar⟩ := bChk_spec hb3 hc hbit
      rw [hy]
      simp only [Bool.and_eq_true, beq_iff_eq]
      refine ⟨?_, (bilE _ _).trans hpar⟩
      unfold onePlus
      rw [vecMulN_unpackR]
      exact hyb
    · left
      left
      have hne : CFSG.Sporadic.Co1.S365Native.tyLabN qr pts pos n (P p ^^^ P p') ≠ 3 := by
        intro h3
        have hin' : CFSG.Sporadic.Co1.S365Native.inPtsN pts pos n (P p ^^^ P p') = true := by
          unfold CFSG.Sporadic.Co1.S365Native.tyLabN at h3
          split_ifs at h3 with h1 h2 h4 <;> first | exact h4 | omega
        obtain ⟨i, hi, hPi⟩ := hin _ hin'
        have hfw : vmF 24 T (P i) = P i := by rw [hPi, vmF_xor, hfa, hfb]
        obtain ⟨hbi, -, -⟩ := edgeV_spec (hsw i hi) hfw
        rw [hPi, vmF_xor, hca] at hbi
        exact hbit hbi
      simp [hne]

end CFSG.KC.GmsPath

end
