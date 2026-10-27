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
public import Mathlib.Geometry.Euclidean.Altitude
public import Mathlib.NumberTheory.Chebyshev
public import Mathlib.NumberTheory.Height.NumberField
public import Mathlib.NumberTheory.Height.Projectivization
public import Mathlib.NumberTheory.LucasLehmer
public import Mathlib.NumberTheory.SelbergSieve
public import Mathlib.RepresentationTheory.Character
public import Mathlib.RepresentationTheory.Maschke
public import Mathlib.RingTheory.Radical.NatInt
public import Mathlib.RingTheory.SimpleRing.Principal
public import Mathlib.Tactic.Echelon.Zsqrtd
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

namespace CFSG

open scoped TensorProduct

namespace BrauerSplittingField.Helpers

noncomputable section

universe u

@[expose] def baseChangeRep
    {K A G W : Type u}
    [CommSemiring K] [CommSemiring A] [Algebra K A]
    [Monoid G] [AddCommMonoid W] [Module K W]
    (σ : Representation K G W) :
    Representation A G (A ⊗[K] W) where
  toFun g := (σ g).baseChange A
  map_one' := by
    rw [map_one]
    exact LinearMap.baseChange_one K W
  map_mul' g h := by
    rw [map_mul]
    exact LinearMap.baseChange_mul (σ g) (σ h)

@[simp]
lemma baseChangeRep_apply
    {K A G W : Type u}
    [CommSemiring K] [CommSemiring A] [Algebra K A]
    [Monoid G] [AddCommMonoid W] [Module K W]
    (σ : Representation K G W) (g : G) :
    (baseChangeRep (A := A) σ) g = (σ g).baseChange A := rfl

@[expose] def averagedIntertwiningMap
    {K G N P : Type u}
    [CommRing K] [Group G] [Fintype G]
    [AddCommGroup N] [Module K N]
    [AddCommGroup P] [Module K P]
    (ρ : Representation K G N) (σ : Representation K G P)
    (f : N →ₗ[K] P) : ρ.IntertwiningMap σ :=
  (_root_.Representation.IntertwiningMap.equivLinearMapAsModule ρ σ).symm
    (((σ.asModuleEquiv.symm.toLinearMap.comp
        (f.comp ρ.asModuleEquiv.toLinearMap)).sumOfConjugatesEquivariant G))

lemma averagedIntertwiningMap_apply
    {K G N P : Type u}
    [CommRing K] [Group G] [Fintype G]
    [AddCommGroup N] [Module K N]
    [AddCommGroup P] [Module K P]
    (ρ : Representation K G N) (σ : Representation K G P)
    (f : N →ₗ[K] P) (x : N) :
    averagedIntertwiningMap ρ σ f x =
      ∑ g : G, σ g⁻¹ (f (ρ g x)) := by
  change
    (σ.asModuleEquiv
      (((σ.asModuleEquiv.symm.toLinearMap.comp
        (f.comp ρ.asModuleEquiv.toLinearMap)).sumOfConjugatesEquivariant G)
          (ρ.asModuleEquiv.symm x))) = _
  rw [LinearMap.sumOfConjugatesEquivariant_apply]
  rw [map_sum]
  apply Finset.sum_congr rfl
  intro g _
  rw [LinearMap.conjugate_apply, Representation.asModuleEquiv_map_smul,
    Representation.asAlgebraHom_single_one]
  have hρ : MonoidAlgebra.single g (1 : K) • ρ.asModuleEquiv.symm x =
      ρ.asModuleEquiv.symm (ρ g x) := by
    simpa [MonoidAlgebra.of_apply] using (ρ.asModuleEquiv_symm_map_rho g x).symm
  rw [hρ]
  rfl

lemma averagedIntertwiningMap_of_intertwining
    {K G N P : Type u}
    [CommRing K] [Group G] [Fintype G]
    [AddCommGroup N] [Module K N]
    [AddCommGroup P] [Module K P]
    (ρ : Representation K G N) (σ : Representation K G P)
    (f : ρ.IntertwiningMap σ) :
    averagedIntertwiningMap ρ σ f.toLinearMap =
      (Fintype.card G : K) • f := by
  ext x
  simp [averagedIntertwiningMap_apply, f.isIntertwining,
    Nat.cast_smul_eq_nsmul]

lemma averagedIntertwiningMap_baseChange
    {K A G N P : Type u}
    [CommRing K] [CommRing A] [Algebra K A]
    [Group G] [Fintype G]
    [AddCommGroup N] [Module K N]
    [AddCommGroup P] [Module K P]
    (ρ : Representation K G N) (σ : Representation K G P)
    (f : N →ₗ[K] P) :
    (averagedIntertwiningMap ρ σ f).toLinearMap.baseChange A =
      (averagedIntertwiningMap (baseChangeRep (A := A) ρ)
        (baseChangeRep (A := A) σ) (f.baseChange A)).toLinearMap := by
  ext a
  simp [averagedIntertwiningMap_apply]
  rw [TensorProduct.tmul_sum]

end

end BrauerSplittingField.Helpers

section
open FDRep

open CategoryTheory

noncomputable section

universe u

open FDRep in
@[expose] noncomputable def _root_.FDRep.baseChange
    {K A G : Type u} [Field K] [Field A] [Algebra K A]
    [Monoid G] (V : FDRep K G) : FDRep A G :=
  FDRep.of (BrauerSplittingField.Helpers.baseChangeRep (A := A) V.ρ)

open FDRep in
@[simp]
lemma _root_.FDRep.baseChange_rho
    {K A G : Type u} [Field K] [Field A] [Algebra K A]
    [Monoid G] (V : FDRep K G) (g : G) :
    (FDRep.baseChange (A := A) V).ρ g = (V.ρ g).baseChange A := rfl

open FDRep in
@[simp]
lemma _root_.FDRep.baseChange_character
    {K A G : Type u} [Field K] [Field A] [Algebra K A]
    [Monoid G] (V : FDRep K G) (g : G) :
    (FDRep.baseChange (A := A) V).character g =
      algebraMap K A (V.character g) := by
  exact LinearMap.trace_baseChange (V.ρ g) A

end

end

end CFSG
