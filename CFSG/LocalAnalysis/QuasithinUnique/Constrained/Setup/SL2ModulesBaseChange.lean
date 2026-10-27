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
public import Mathlib.NumberTheory.Chebyshev
public import Mathlib.NumberTheory.Height.NumberField
public import Mathlib.NumberTheory.Height.Projectivization
public import Mathlib.NumberTheory.LucasLehmer
public import Mathlib.NumberTheory.SelbergSieve
public import Mathlib.RingTheory.Henselian
public import Mathlib.RingTheory.Radical.NatInt
public import Mathlib.RingTheory.RegularLocalRing.Defs
public import Mathlib.RingTheory.SimpleRing.Principal
public import Mathlib.RingTheory.WittVector.IsPoly
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
public import Mathlib.Tactic.Polynomial.Basic
public import Mathlib.Tactic.ReduceModChar
public import Mathlib.Topology.Sheaves.Init

public section

namespace CFSG.QuasithinUnique.Setup.SL2Modules

section BaseChange

variable {D E : Type*} [Field D] [Field E] [Finite E] (ι : D →+* E)

theorem natCard_common_ker_map {m : ℕ} {κ : Type*} (Y : κ → Matrix (Fin m) (Fin m) D) :
    Nat.card {x : Fin m → E // ∀ a, ((Y a).map ι).mulVec x = 0} =
      Nat.card {x : Fin m → D // ∀ a, (Y a).mulVec x = 0} ^
        (letI := ι.toAlgebra; Module.finrank D E) := by
  let _ := ι.toAlgebra
  have : Module.Finite D E := Module.Finite.of_finite
  obtain ⟨ε, -⟩ : ∃ ε : Module.Basis (Fin (Module.finrank D E)) D E, True :=
    ⟨Module.finBasis D E, trivial⟩
  let coord : (Fin m → E) ≃ (Fin (Module.finrank D E) → (Fin m → D)) :=
    { toFun := fun x j i => ε.repr (x i) j
      invFun := fun z i => ∑ j, z j i • ε j
      left_inv := fun x => by
        funext i
        simp only
        conv_rhs => rw [← ε.sum_repr (x i)]
      right_inv := fun z => by
        funext j i
        show ε.repr (∑ j', z j' i • ε j') j = z j i
        rw [map_sum, Finsupp.finsetSum_apply]
        simp [Module.Basis.repr_self, Finsupp.single_apply] }
  have key : ∀ (x : Fin m → E) (Y : Matrix (Fin m) (Fin m) D) (k : Fin m) (j : Fin (Module.finrank D E)),
      ε.repr (((Y.map ι).mulVec x) k) j = (Y.mulVec (coord x j)) k := by
    intro x Y k j
    simp only [Matrix.mulVec, dotProduct, Matrix.map_apply]
    have : ∑ i, ι (Y k i) * x i = ∑ i, Y k i • x i := by
      refine Finset.sum_congr rfl fun i _ => ?_
      rw [Algebra.smul_def]; rfl
    rw [this]
    simp [map_sum, coord]
  have hbij : {x : Fin m → E // ∀ a, ((Y a).map ι).mulVec x = 0} ≃
      {z : Fin (Module.finrank D E) → (Fin m → D) // ∀ j, ∀ a, (Y a).mulVec (z j) = 0} :=
    Equiv.subtypeEquiv coord (fun x => by
      constructor
      · intro h j a
        funext k
        have := congrArg (fun v => ε.repr (v k) j) (h a)
        simpa [key] using this
      · intro h a
        funext k
        apply ε.repr.injective
        ext j
        simpa [key] using congrFun (h j a) k)
  have hpi : {z : Fin (Module.finrank D E) → (Fin m → D) // ∀ j, ∀ a, (Y a).mulVec (z j) = 0} ≃
      (Fin (Module.finrank D E) → {u : Fin m → D // ∀ a, (Y a).mulVec u = 0}) :=
    Equiv.subtypePiEquivPi (p := fun _ u => ∀ a, (Y a).mulVec u = 0)
  rw [Nat.card_congr hbij, Nat.card_congr hpi, Nat.card_pi, Finset.prod_const, Finset.card_univ,
    Fintype.card_fin]

end BaseChange

end CFSG.QuasithinUnique.Setup.SL2Modules
