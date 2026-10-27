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
public import Mathlib.LinearAlgebra.Matrix.ProjectiveSpecialLinearGroup
public import Mathlib.NumberTheory.Chebyshev
public import Mathlib.NumberTheory.Height.NumberField
public import Mathlib.NumberTheory.Height.Projectivization
public import Mathlib.NumberTheory.LucasLehmer
public import Mathlib.NumberTheory.SelbergSieve
public import Mathlib.RingTheory.Radical.NatInt
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

open scoped MatrixGroups

namespace GorensteinWalter.FieldTransport

private lemma finite_field_normalize
    (K : Type) [Field K] [Fintype K] (hodd : Odd (Fintype.card K))
    (hge : 5 ≤ Fintype.card K) :
    ∃ p k : ℕ, ∃ _hp : Fact p.Prime, Odd p ∧ 5 ≤ p ^ k ∧
      Fintype.card K = p ^ k ∧ Nonempty (K ≃+* GaloisField p k) := by
  obtain ⟨p, _hcharp, k, hp, hcard⟩ := FiniteField.card' K
  let : Fact p.Prime := ⟨hp⟩
  let : Algebra (ZMod p) K := ZMod.algebra K p
  refine ⟨p, (k : ℕ), ⟨hp⟩, ?_, ?_, hcard, ?_⟩
  · apply hp.odd_of_ne_two
    rintro rfl
    rw [hcard] at hodd
    have hk : (k : ℕ) ≠ 0 := k.pos.ne'
    have hEven : Even (2 ^ (k : ℕ)) :=
      Nat.even_pow.mpr ⟨even_two, hk⟩
    exact (Nat.not_odd_iff_even.mpr hEven) hodd
  · rwa [← hcard]
  · exact
      ⟨(GaloisField.algEquivGaloisFieldOfFintype p (k : ℕ) hcard).toRingEquiv⟩

noncomputable def specialLinearGroupMulEquiv
    {n : Type*} [DecidableEq n] [Fintype n]
    {R S : Type*} [CommRing R] [CommRing S] (e : R ≃+* S) :
    Matrix.SpecialLinearGroup n R ≃* Matrix.SpecialLinearGroup n S where
  toFun := Matrix.SpecialLinearGroup.map e.toRingHom
  invFun := Matrix.SpecialLinearGroup.map e.symm.toRingHom
  left_inv := by
    intro x
    apply Subtype.ext
    ext i j
    exact e.symm_apply_apply (x i j)
  right_inv := by
    intro x
    apply Subtype.ext
    ext i j
    exact e.apply_symm_apply (x i j)
  map_mul' := (Matrix.SpecialLinearGroup.map e.toRingHom).map_mul

def quotientCenterHom {G H : Type*} [Group G] [Group H] (e : G ≃* H) :
    (G ⧸ Subgroup.center G) →* (H ⧸ Subgroup.center H) :=
  QuotientGroup.map (N := Subgroup.center G) (Subgroup.center H) e.toMonoidHom (by
    intro x hx
    exact MulEquivClass.apply_mem_center e hx)

@[simp]
lemma quotientCenterHom_mk {G H : Type*} [Group G] [Group H]
    (e : G ≃* H) (x : G) :
    quotientCenterHom e (QuotientGroup.mk' (Subgroup.center G) x) =
      QuotientGroup.mk' (Subgroup.center H) (e x) := by
  rfl

def quotientCenterMulEquiv {G H : Type*} [Group G] [Group H] (e : G ≃* H) :
    (G ⧸ Subgroup.center G) ≃* (H ⧸ Subgroup.center H) where
  toFun := quotientCenterHom e
  invFun := quotientCenterHom e.symm
  left_inv := by
    intro x
    induction x using Quotient.inductionOn' with
    | _ x =>
      change QuotientGroup.mk' (Subgroup.center G) (e.symm (e x)) =
        QuotientGroup.mk' (Subgroup.center G) x
      rw [e.symm_apply_apply]
  right_inv := by
    intro x
    induction x using Quotient.inductionOn' with
    | _ x =>
      change QuotientGroup.mk' (Subgroup.center H) (e (e.symm x)) =
        QuotientGroup.mk' (Subgroup.center H) x
      rw [e.apply_symm_apply]
  map_mul' := (quotientCenterHom e).map_mul

noncomputable def projectiveSpecialLinearGroupMulEquiv
    {n : Type*} [DecidableEq n] [Fintype n]
    {R S : Type*} [CommRing R] [CommRing S] (e : R ≃+* S) :
    Matrix.ProjectiveSpecialLinearGroup n R ≃*
      Matrix.ProjectiveSpecialLinearGroup n S :=
  quotientCenterMulEquiv (specialLinearGroupMulEquiv e)

noncomputable def pslZModEquivGaloisFieldOne (p : ℕ) [Fact p.Prime] :
    PSL(2, ZMod p) ≃* PSL(2, GaloisField p 1) :=
  (projectiveSpecialLinearGroupMulEquiv
    (GaloisField.equivZmodP (p := p)).toRingEquiv).symm

lemma conclusion_of_psl_over_finite_field
    {G K : Type} [Group G] [Field K] [Fintype K]
    (e : G ≃* PSL(2, K)) (hodd : Odd (Fintype.card K))
    (hge : 5 ≤ Fintype.card K) :
    ∃ p k : ℕ, ∃ _hp : Fact p.Prime, Odd p ∧ 5 ≤ p ^ k ∧
      Nonempty (G ≃* PSL(2, GaloisField p k)) := by
  obtain ⟨p, k, hp, hpOdd, hpFive, -, ⟨eK⟩⟩ :=
    finite_field_normalize K hodd hge
  let : Fact p.Prime := hp
  exact ⟨p, k, hp, hpOdd, hpFive,
    ⟨e.trans (projectiveSpecialLinearGroupMulEquiv eK)⟩⟩

end GorensteinWalter.FieldTransport

end CFSG
