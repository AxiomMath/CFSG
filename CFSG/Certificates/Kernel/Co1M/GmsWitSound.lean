module

public import Certificates.Data.Kernel.GmsWitK
public import CFSG.Certificates.Kernel.Co1M.GmsPathSound
public import Certificates.Data.CFSGNative.Co1.S365CentWit
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

open CFSG.KLie.CT CFSG.KC.Loop CFSG.KC.M1F2 CFSG.KC.Co1M CFSG.KC.Co1F2

theorem strictB_eq (y : Nat) (k : Nat → Bool) : strictB y k = k y := by
  cases y <;> rfl

theorem beq_dec (a b : Nat) : Nat.beq a b = decide (a = b) := by
  rw [Bool.eq_iff_iff, Nat.beq_eq, decide_eq_true_iff]

theorem blt_dec (a b : Nat) : Nat.blt a b = decide (a < b) := by
  rw [Bool.eq_iff_iff, Nat.blt_eq, decide_eq_true_iff]

theorem l1K_true (Q : Nat) (O : Nat → Bool) (w : Nat) :
    l1K Q O w = true ↔ w ≠ 0 ∧ qK Q w = false ∧ O w = false := by
  unfold l1K
  rw [andB_eq, andB_eq, notB_eq, notB_eq, notB_eq, beq_dec]
  simp

theorem l3K_true (Q : Nat) (O : Nat → Bool) (w : Nat) :
    l3K Q O w = true ↔ w ≠ 0 ∧ qK Q w = false ∧ O w = true := by
  unfold l3K
  rw [andB_eq, andB_eq, notB_eq, notB_eq, beq_dec]
  simp

theorem applyK_eq (Ms path : List Nat) (v : Nat) :
    applyK Ms path v = path.foldl (fun acc l => vmF 24 (getL 0 Ms l) acc) v := by
  induction path generalizing v with
  | nil => rfl
  | cons l p ih => exact ih _

theorem mem_collectLt (p : Nat → Bool) :
    ∀ n acc x, x ∈ CFSG.Sporadic.Co1.S365CentNative.collectLt p n acc ↔
      (x < n ∧ p x = true) ∨ x ∈ acc := by
  intro n
  induction n with
  | zero => intro acc x; simp [CFSG.Sporadic.Co1.S365CentNative.collectLt]
  | succ n ih =>
    intro acc x
    rw [CFSG.Sporadic.Co1.S365CentNative.collectLt, ih]
    by_cases hp : p n = true
    · simp only [hp, ↓reduceIte, List.mem_cons]
      constructor
      · rintro (⟨h1, h2⟩ | rfl | h)
        · exact Or.inl ⟨by omega, h2⟩
        · exact Or.inl ⟨by omega, hp⟩
        · exact Or.inr h
      · rintro (⟨h1, h2⟩ | h)
        · rcases Nat.lt_succ_iff_lt_or_eq.1 h1 with h' | h'
          · exact Or.inl ⟨h', h2⟩
          · exact Or.inr (Or.inl h')
        · exact Or.inr (Or.inr h)
    · simp only [hp, Bool.false_eq_true, ↓reduceIte]
      constructor
      · rintro (⟨h1, h2⟩ | h)
        · exact Or.inl ⟨by omega, h2⟩
        · exact Or.inr h
      · rintro (⟨h1, h2⟩ | h)
        · rcases Nat.lt_succ_iff_lt_or_eq.1 h1 with h' | h'
          · exact Or.inl ⟨h', h2⟩
          · subst h'
            exact absurd h2 hp
        · exact Or.inr h

theorem getL_mem : ∀ (L : List Nat) (k : Nat), k < L.length → getL 0 L k ∈ L := by
  intro L
  induction L with
  | nil => intro k hk; exact absurd hk (Nat.not_lt_zero k)
  | cons a L ih =>
    intro k hk
    cases k with
    | zero => exact List.mem_cons_self ..
    | succ k =>
      exact List.mem_cons_of_mem _ (ih k (by simpa using hk))

theorem Xc_xor (CM a b : Nat) : Xc CM (a ^^^ b) = Xc CM a ^^^ Xc CM b := by
  unfold Xc
  change vmF 24 CM ((a ^^^ b) <<< 16) = vmF 24 CM (a <<< 16) ^^^ vmF 24 CM (b <<< 16)
  rw [Nat.shiftLeft_xor_distrib, vmF_xor]

theorem dual_spec {CM DM : Nat} {GS : List Nat} (h : dualK CM DM GS = true)
    (hlen : 16 ≤ GS.length) {x : Nat} (hx : x < 2 ^ 24) (hor : ∀ g ∈ GS, parF (x &&& g) = false) :
    vmF 24 DM x >>> 16 < 256 ∧ Xc CM (vmF 24 DM x >>> 16) = x := by
  unfold dualK at h
  simp only [allN_iff, andB_eq, Bool.and_eq_true, Nat.beq_eq, pw2_eq, beqB_eq, beq_iff_eq,
    land_eq] at h
  have hinv : ∀ z < 2 ^ 24, vmF 24 CM (vmF 24 DM z) = z :=
    addN_agree (f := fun z => vmF 24 CM (vmF 24 DM z)) (g := id)
      (fun a b => by simp only [vmF_xor]) (fun _ _ => rfl) (fun i hi => (h i hi).1)
  have hbit : ∀ k < 16, ∀ z < 2 ^ 24, (vmF 24 DM z).testBit k = parF (z &&& getL 0 GS k) :=
    fun k hk => add_agree (f := fun z => (vmF 24 DM z).testBit k)
      (g := fun z => parF (z &&& getL 0 GS k))
      (fun a b => by simp only [vmF_xor, Nat.testBit_xor])
      (fun a b => by simp only [Nat.and_xor_distrib_right, parF_xor])
      (fun i hi => by
        have := (h i hi).2.2 k hk
        rw [bit_eq] at this
        exact this)
  have hy : vmF 24 DM x < 16777216 := by
    have := vmF_lt 24 DM x
    simpa using this
  have hlow : ∀ k < 16, (vmF 24 DM x).testBit k = false := fun k hk => by
    rw [hbit k hk x hx]
    exact hor _ (getL_mem GS k (by omega))
  have hyy : (vmF 24 DM x >>> 16) <<< 16 = vmF 24 DM x := by
    apply Nat.eq_of_testBit_eq
    intro i
    rw [Nat.testBit_shiftLeft, Nat.testBit_shiftRight]
    by_cases hi : 16 ≤ i
    · simp only [ge_iff_le, hi, decide_true, Bool.true_and]
      congr 1
      omega
    · simp only [ge_iff_le, hi, decide_false, Bool.false_and]
      exact (hlow i (by omega)).symm
  refine ⟨?_, ?_⟩
  · rw [Nat.shiftRight_eq_div_pow]
    omega
  · unfold Xc
    change vmF 24 CM ((vmF 24 DM x >>> 16) <<< 16) = x
    rw [hyy, hinv x hx]

theorem mask_spec {Q : Nat} {O : Nat → Bool} {CM M2 M4 : Nat} (h : maskK Q O CM M2 M4 = true)
    {c : Nat} (hc : c < 256) : bit M2 c = l3K Q O (Xc CM c) ∧ bit M4 c = l1K Q O (Xc CM c) := by
  unfold maskK at h
  rw [allN_iff] at h
  have := h c hc
  rw [andB_eq, Bool.and_eq_true, beqB_eq, beqB_eq, beq_iff_eq, beq_iff_eq] at this
  exact this

theorem pair_spec {M2 M4 SH : Nat} (hS : shiftK M4 SH = true) (h : pairK M2 M4 SH = true)
    {a b g : Nat} (ha : a < 256) (hb : b < 256) (hg : g < 256) (h1 : bit M2 a = true)
    (h2 : bit M2 b = true) (h3 : bit M2 (a ^^^ b) = true) (h4 : bit M4 g = true)
    (h5 : bit M4 (g ^^^ a) = true) (h6 : bit M4 (g ^^^ b) = true)
    (h7 : bit M4 (g ^^^ a ^^^ b) = true) : False := by
  have hs : ∀ d < 256, bit (shK SH d) g = bit M4 (g ^^^ d) := by
    intro d hd
    unfold shiftK at hS
    rw [allN_iff] at hS
    have := hS d hd
    rw [allN_iff] at this
    have := this g hg
    rw [beqB_eq, beq_iff_eq] at this
    exact this
  have hab : a ^^^ b < 256 := Nat.xor_lt_two_pow (n := 8) ha hb
  unfold pairK at h
  rw [allN_iff] at h
  have ka := h a ha
  rw [orB_eq, notB_eq, h1, Bool.not_true, Bool.false_or, allN_iff] at ka
  have kb := ka b hb
  have h3' : bit M2 (Nat.xor a b) = true := h3
  rw [orB_eq, orB_eq, notB_eq, notB_eq, h2, h3', Bool.not_true, Bool.false_or, Bool.false_or,
    Nat.beq_eq] at kb
  have kt := congrArg (fun x => Nat.testBit x g) kb
  simp only [Nat.zero_testBit] at kt
  change (M4 &&& (shK SH a &&& (shK SH b &&& shK SH (a ^^^ b)))).testBit g = false at kt
  rw [Nat.testBit_and, Nat.testBit_and, Nat.testBit_and, ← bit_eq, ← bit_eq, ← bit_eq, ← bit_eq,
    hs a ha, hs b hb, hs _ hab, ← Nat.xor_assoc, h4, h5, h6, h7] at kt
  exact Bool.noConfusion kt

end CFSG.KC.GmsPath

end
