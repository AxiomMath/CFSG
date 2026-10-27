module

public import Certificates.Data.Kernel.SporSch.SylElts
public import CFSG.Certificates.Kernel.Spor.Loops
public import CFSG.Certificates.Kernel.Spor.RawDefs
public import CFSG.Certificates.Kernel.SporSch.SylowCount
public import CFSG.Monster.B.Mathieu.CertText5
public import Certificates.Data.CFSGNative.PairSchreier.Core
public import Mathlib.Algebra.Order.Floor.Extended
public import Mathlib.Algebra.Order.Interval.Basic
public import Mathlib.Algebra.Order.Ring.Star
public import Mathlib.Analysis.Complex.UpperHalfPlane.Basic
public import Mathlib.Analysis.SpecialFunctions.Bernstein
public import Mathlib.Analysis.SpecialFunctions.Gamma.Basic
public import Mathlib.Analysis.SpecialFunctions.Trigonometric.DerivHyp
public import Mathlib.Combinatorics.Enumerative.DyckWord
public import Mathlib.Combinatorics.SimpleGraph.Triangle.Removal
public import Mathlib.Data.NNRat.Floor
public import Mathlib.Data.Nat.Bitwise
public import Mathlib.Data.Nat.Choose.Multinomial
public import Mathlib.Geometry.Euclidean.Volume.Basic
public import Mathlib.NumberTheory.Chebyshev
public import Mathlib.NumberTheory.Height.NumberField
public import Mathlib.NumberTheory.Height.Projectivization
public import Mathlib.NumberTheory.LucasLehmer
public import Mathlib.NumberTheory.SelbergSieve
public import Mathlib.RingTheory.Radical.NatInt
public import Mathlib.Tactic.Echelon.Zsqrtd
public import Mathlib.Tactic.Inclusion.Extension.Core.Core
public import Mathlib.Tactic.Inclusion.Extension.IntervalDyadicReal.Hypotheses
public import Mathlib.Tactic.Inclusion.Extension.IntervalDyadicReal.Rational
public import Mathlib.Tactic.NormNum.Irrational
public import Mathlib.Tactic.NormNum.IsCoprime
public import Mathlib.Tactic.NormNum.IsSquare
public import Mathlib.Tactic.NormNum.LegendreSymbol
public import Mathlib.Tactic.NormNum.ModEq
public import Mathlib.Tactic.NormNum.NatFib
public import Mathlib.Tactic.NormNum.NatLog
public import Mathlib.Tactic.NormNum.NatSqrt
public import Mathlib.Tactic.NormNum.Ordinal
public import Mathlib.Tactic.NormNum.Parity
public import Mathlib.Tactic.NormNum.Prime
public import Mathlib.Tactic.NormNum.RealSqrt
public import Mathlib.Topology.Sheaves.Init
public import Std.Tactic.BVDecide.Normalize.BitVec

public section

namespace CFSG.KS.SporSch.MBT

open CFSG.KC.Enum CFSG.KS CFSG.KS.Raw CFSG.KS.Prim CFSG.KS.MEnum CFSG.KS.M11 CFSG.KS.SporSch.MOC
open CFSG.Certificates.Native CFSG.Sporadic.Schreier.PairNative CFSG.Monster.B.Co2.Native
open CFSG.Monster.B.Mathieu CFSG.KS.SylowCount Finset

variable {n w : Nat} {PS PSI LR TR TRI : Nat → Nat} {kS nb BP NS CH : Nat}
  {S : Array (Array Nat)} {base : Array Nat} {D : List (List Int)} {gA gB : Equiv.Perm (Fin n)}

open scoped Classical

theorem canonK_inj {X Y : Nat} (hX : canonK n w (mask w) (n * w) X = true)
    (hY : canonK n w (mask w) (n * w) Y = true)
    (h : (unpack n w X).toList = (unpack n w Y).toList) : X = Y := by
  have hfld : ∀ i < n, pg w (mask w) X i = pg w (mask w) Y i := fun i hi => by
    have e := congrArg (·[i]!) (Array.toList_inj.1 h)
    simp only [unpack] at e
    rwa [getElem!_pos _ i (by simpa using hi), getElem!_pos _ i (by simpa using hi),
      Array.getElem_ofFn, Array.getElem_ofFn] at e
  have hlt : ∀ {Z : Nat}, canonK n w (mask w) (n * w) Z = true → Z < 2 ^ (n * w) := @fun Z hZ => by
    unfold canonK at hZ
    simp only [bAnd_iff] at hZ
    have h0 : Z >>> (n * w) = 0 := Nat.eq_of_beq_eq_true hZ.2.1
    rw [Nat.shiftRight_eq_div_pow, Nat.div_eq_zero_iff] at h0
    rcases h0 with h0 | h0
    · exact absurd h0 (Nat.pos_iff_ne_zero.1 (Nat.two_pow_pos _))
    · exact h0
  have hm : mask w = 2 ^ w - 1 := by
    change 1 <<< w - 1 = _
    rw [Nat.one_shiftLeft]
  apply Nat.eq_of_testBit_eq
  intro b
  by_cases hb : n * w ≤ b
  · have hp : 2 ^ (n * w) ≤ 2 ^ b := Nat.pow_le_pow_right (by norm_num) hb
    rw [Nat.testBit_eq_false_of_lt (lt_of_lt_of_le (hlt hX) hp),
      Nat.testBit_eq_false_of_lt (lt_of_lt_of_le (hlt hY) hp)]
  · have hw : 0 < w := by
      rcases Nat.eq_zero_or_pos w with h0 | h0
      · subst h0
        omega
      · exact h0
    have hi : b / w < n := by
      rw [Nat.div_lt_iff_lt_mul hw]
      omega
    have key : ∀ Z : Nat, Z.testBit b = (pg w (mask w) Z (b / w)).testBit (b % w) := fun Z => by
      change Z.testBit b =
        (Nat.land (Nat.shiftRight Z (Nat.mul w (b / w))) (mask w)).testBit (b % w)
      rw [hm]
      change Z.testBit b = ((Z >>> (w * (b / w))) &&& (2 ^ w - 1)).testBit (b % w)
      rw [Nat.testBit_and, Nat.testBit_two_pow_sub_one, Nat.testBit_shiftRight,
        Nat.div_add_mod]
      simp [Nat.mod_lt b hw]
    rw [key X, key Y, hfld _ hi]

theorem memL_spec {x : Nat} : ∀ {L : List Nat}, memL x L = true → x ∈ L
  | [], h => absurd h Bool.false_ne_true
  | y :: L, h => by
    have h' : Bool.rec (motive := fun _ => Bool) (memL x L) true (Nat.beq y x) = true := h
    cases hb : Nat.beq y x
    · rw [hb] at h'
      exact List.mem_cons_of_mem _ (memL_spec h')
    · rw [← Nat.eq_of_beq_eq_true hb]
      exact List.mem_cons_self

theorem allL_spec {f : Nat → Bool} : ∀ {L : List Nat}, allL f L = true → ∀ y ∈ L, f y = true
  | [], _ => fun y hy => absurd hy List.not_mem_nil
  | y :: L, h => by
    have h' : Bool.rec (motive := fun _ => Bool) false (allL f L) (f y) = true := h
    obtain ⟨h1, h2⟩ := (bAnd_iff _ _).1 h'
    intro z hz
    rcases List.mem_cons.1 hz with rfl | hz
    · exact h1
    · exact allL_spec h2 z hz

theorem incL_spec : ∀ {L : List Nat} {p : Nat}, incL p L = true →
    L.Pairwise (· < ·) ∧ ∀ y ∈ L, p < y
  | [], _, _ => ⟨List.Pairwise.nil, fun y hy => absurd hy List.not_mem_nil⟩
  | y :: L, p, h => by
    have h' : Bool.rec (motive := fun _ => Bool) false (incL y L) (Nat.blt p y) = true := h
    obtain ⟨h1, h2⟩ := (bAnd_iff _ _).1 h'
    obtain ⟨ih1, ih2⟩ := incL_spec h2
    have hpy : p < y := by simpa [Nat.blt_eq] using h1
    refine ⟨List.Pairwise.cons ih2 ih1, fun z hz => ?_⟩
    rcases List.mem_cons.1 hz with rfl | hz
    · exact hpy
    · exact hpy.trans (ih2 z hz)

end CFSG.KS.SporSch.MBT

end
