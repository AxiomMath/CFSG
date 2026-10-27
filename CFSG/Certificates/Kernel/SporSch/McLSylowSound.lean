module

public import CFSG.Certificates.Kernel.SporSch.SylowCount
import CFSG.Certificates.Kernel.SporSch.ChainKPack
public import CFSG.Certificates.Kernel.Spor.RawDefs
public import CFSG.Monster.B.Mathieu.Order
public import Certificates.Data.CFSGNative.PairSchreier.Core
public import Certificates.Data.Kernel.Spor.MEnum
public import Certificates.Data.Kernel.Spor.Prim
public import Mathlib.Algebra.Order.Floor.Extended
public import Mathlib.Algebra.Order.Interval.Basic
public import Mathlib.Analysis.Complex.UpperHalfPlane.Basic
public import Mathlib.Analysis.SpecialFunctions.Bernstein
public import Mathlib.Analysis.SpecialFunctions.Gamma.Basic
public import Mathlib.Analysis.SpecialFunctions.Trigonometric.DerivHyp
public import Mathlib.Combinatorics.Enumerative.DyckWord
public import Mathlib.Combinatorics.SimpleGraph.Triangle.Removal
public import Mathlib.Data.NNRat.Floor
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

public section

namespace CFSG.KS.SporSch.MBT

open CFSG.KC.Enum CFSG.KS CFSG.KS.Raw CFSG.KS.Prim CFSG.KS.MEnum CFSG.KS.M11 CFSG.KS.SporSch.MOC
open CFSG.Certificates.Native CFSG.Sporadic.Schreier.PairNative CFSG.Monster.B.Co2.Native
open CFSG.Monster.B.Mathieu CFSG.KS.SylowCount Finset

@[expose] def gen2 {n : Nat} (a b : Equiv.Perm (Fin n)) : Subgroup (Equiv.Perm (Fin n)) :=
  Subgroup.closure {a, b}

@[expose] def patP {G : Type*} [Monoid G] (x y : G) (pat : List Bool) : G :=
  (pat.map fun b => if b then y else x).prod

@[expose] def xyWordP {G : Type*} [Monoid G] (x y xi yi : G) (wd : List Nat) : G :=
  (wd.map fun l => if l = 0 then x else if l = 1 then y else if l = 2 then xi else yi).prod

variable {n w : Nat} {PS PSI LR TR TRI : Nat → Nat} {kS nb BP NS CH : Nat}
  {S : Array (Array Nat)} {base : Array Nat} {D : List (List Int)} {gA gB : Equiv.Perm (Fin n)}

open scoped Classical

theorem exists_perm_of_permOK {X Xi : Nat} (h : permOK n w (mask w) (n * w) X Xi = true) :
    ∃ g : Equiv.Perm (Fin n), imageList g = (unpack n w X).toList :=
  ⟨_, imageList_of_prep (Orb.prep_of_rep
    (CFSG.Monster.B.Co2.rep_permOfArr (Orb.isInvA_unpack h)).1)⟩

theorem ordIs_sound (hsz : szOK n w = true) {g : Equiv.Perm (Fin n)} {P e : Nat}
    (hg : imageList g = (unpack n w P).toList) (hP : canonK n w (mask w) (n * w) P = true)
    (h : ordIs n w (mask w) (pidn n w) P e = true) : orderOf g = e + 1 :=
  ordIs_orderOf hsz (prep_of_imageList hg) (PF.canon_facts hP).2.2.1 (Nat.succ_pos e) h

theorem imageList_inj {g h : Equiv.Perm (Fin n)} (e : imageList g = imageList h) : g = h := by
  unfold imageList at e
  rw [List.ofFn_inj] at e
  exact Equiv.ext fun i => Fin.ext (congrFun e i)

theorem xyWordP_cond {G : Type*} [Monoid G] (x y xi yi : G) (pat : List Bool) :
    xyWordP x y xi yi (pat.map fun b => if b then 1 else 0) = patP x y pat := by
  induction pat with
  | nil => rfl
  | cons b pat ih =>
    simp only [xyWordP, patP, List.map_cons, List.map_map, List.prod_cons] at ih ⊢
    rw [← ih]
    cases b <;> rfl

theorem patP_xy {G : Type*} [Monoid G] (x y : G) : patP x y [false, true] = x * y := by
  simp [patP]

theorem patP_conj {G : Type*} [Group G] (g x y : G) (pat : List Bool) :
    patP (g * x * g⁻¹) (g * y * g⁻¹) pat = g * patP x y pat * g⁻¹ := by
  induction pat with
  | nil => simp [patP]
  | cons b pat ih =>
    simp only [patP, List.map_cons, List.prod_cons] at ih ⊢
    rw [ih]
    cases b <;> simp only [Bool.false_eq_true, ite_false, ite_true] <;> group

end CFSG.KS.SporSch.MBT

end
