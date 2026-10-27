module

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
public import Mathlib.GroupTheory.SpecificGroups.Alternating
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

@[expose] public section

namespace CFSG.AGLEmbeddingD2.McLaughlin.WeakBlockModuleData.A5Mod

open Equiv

abbrev A5 : Type := alternatingGroup (Fin 5)

def invTab : Fin 15 → Fin 5 → Fin 5 := ![
  ![0, 2, 1, 4, 3],
  ![0, 3, 4, 1, 2],
  ![0, 4, 3, 2, 1],
  ![1, 0, 2, 4, 3],
  ![1, 0, 3, 2, 4],
  ![1, 0, 4, 3, 2],
  ![2, 1, 0, 4, 3],
  ![2, 3, 0, 1, 4],
  ![2, 4, 0, 3, 1],
  ![3, 1, 4, 0, 2],
  ![3, 2, 1, 0, 4],
  ![3, 4, 2, 0, 1],
  ![4, 1, 3, 2, 0],
  ![4, 2, 1, 3, 0],
  ![4, 3, 2, 1, 0]]

def inv15 (j : Fin 15) : Perm (Fin 5) :=
  ⟨invTab j, invTab j, by revert j; decide, by revert j; decide⟩

def perm (g : A5) (j : Fin 15) : Fin 15 :=
  ((List.finRange 15).find? fun i =>
    decide (inv15 i = (g : Perm (Fin 5)) * inv15 j * (g : Perm (Fin 5))⁻¹)).getD 0

theorem perm_spec : ∀ (g : A5) (j : Fin 15),
    inv15 (perm g j) = (g : Perm (Fin 5)) * inv15 j * (g : Perm (Fin 5))⁻¹ := by
  decide +kernel

def S : Matrix (Fin 15) (Fin 15) (ZMod 2) :=
  !![1, 1, 0, 1, 0, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0;
  1, 1, 1, 0, 1, 0, 1, 0, 0, 0, 0, 0, 0, 0, 0;
  1, 1, 0, 0, 1, 1, 1, 0, 0, 0, 0, 0, 0, 0, 0;
  1, 0, 1, 1, 1, 1, 0, 1, 0, 1, 0, 0, 0, 0, 0;
  1, 0, 1, 0, 1, 0, 0, 0, 0, 0, 1, 0, 0, 0, 0;
  1, 1, 1, 0, 0, 0, 1, 0, 1, 0, 0, 0, 0, 0, 0;
  1, 0, 0, 1, 1, 1, 1, 0, 0, 0, 0, 0, 0, 0, 0;
  1, 1, 0, 1, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0;
  1, 0, 1, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0;
  1, 1, 1, 1, 1, 1, 1, 0, 0, 0, 0, 0, 0, 0, 0;
  1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1, 0, 1, 1, 1;
  1, 0, 0, 0, 1, 0, 0, 0, 0, 1, 0, 0, 0, 0, 0;
  1, 0, 0, 1, 0, 0, 0, 0, 0, 0, 0, 1, 1, 0, 0;
  1, 0, 1, 0, 0, 0, 1, 0, 1, 0, 0, 1, 0, 0, 1;
  1, 1, 0, 0, 0, 1, 0, 1, 0, 0, 0, 1, 0, 1, 0]

def Sinv : Matrix (Fin 15) (Fin 15) (ZMod 2) :=
  !![0, 0, 1, 0, 0, 0, 0, 0, 1, 1, 0, 0, 0, 0, 0;
  1, 1, 1, 0, 0, 0, 0, 0, 1, 0, 0, 0, 0, 0, 0;
  1, 1, 1, 0, 0, 0, 1, 0, 1, 1, 0, 0, 0, 0, 0;
  1, 1, 0, 0, 0, 0, 1, 0, 1, 0, 0, 0, 0, 0, 0;
  0, 0, 0, 0, 0, 0, 1, 1, 1, 1, 0, 0, 0, 0, 0;
  1, 0, 0, 0, 0, 0, 1, 0, 1, 1, 0, 0, 0, 0, 0;
  0, 1, 1, 0, 0, 0, 0, 1, 0, 1, 0, 0, 0, 0, 0;
  1, 0, 1, 1, 0, 0, 1, 0, 1, 0, 0, 1, 0, 0, 0;
  0, 1, 0, 0, 0, 1, 1, 1, 1, 1, 0, 0, 0, 0, 0;
  0, 0, 1, 0, 0, 0, 1, 1, 0, 0, 0, 1, 0, 0, 0;
  1, 1, 0, 0, 1, 0, 0, 1, 1, 1, 0, 0, 0, 0, 0;
  0, 0, 0, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1;
  1, 1, 1, 1, 1, 1, 0, 1, 1, 0, 1, 1, 0, 1, 1;
  1, 1, 1, 0, 1, 1, 1, 1, 1, 1, 1, 0, 1, 1, 0;
  1, 1, 1, 1, 1, 0, 1, 1, 0, 1, 1, 1, 1, 0, 1]

theorem S_mul_Sinv : S * Sinv = 1 := by decide +kernel

def Pm (g : A5) : Matrix (Fin 15) (Fin 15) (ZMod 2) := fun i j => if i = perm g j then 1 else 0

def Mt (g : A5) : Matrix (Fin 15) (Fin 15) (ZMod 2) := fun l k => ∑ j, Sinv l (perm g j) * S j k

def blk : Fin 15 → Fin 6 := ![0, 1, 1, 1, 1, 2, 3, 4, 4, 4, 4, 5, 5, 5, 5]

def bm (o : ℕ) (g : A5) (l k : Fin 4) : ZMod 2 :=
  if h : o + 4 ≤ 15 then Mt g ⟨o + l, by omega⟩ ⟨o + k, by omega⟩ else 0

def Dm (g : A5) (t k : Fin 4) : ZMod 2 :=
  (if (g : Perm (Fin 5)) k.castSucc = t.castSucc then 1 else 0) +
    (if (g : Perm (Fin 5)) 4 = t.castSucc then 1 else 0)

def om1 : Matrix (Fin 4) (Fin 4) (ZMod 2) :=
  !![0, 0, 1, 0;
  0, 0, 1, 1;
  1, 0, 1, 0;
  1, 1, 0, 1]

def om4 : Matrix (Fin 4) (Fin 4) (ZMod 2) :=
  !![0, 1, 1, 0;
  0, 1, 0, 1;
  1, 0, 1, 1;
  0, 1, 0, 0]

end CFSG.AGLEmbeddingD2.McLaughlin.WeakBlockModuleData.A5Mod
