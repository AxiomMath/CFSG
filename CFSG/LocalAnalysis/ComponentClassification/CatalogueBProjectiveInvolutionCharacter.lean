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
public import Mathlib.LinearAlgebra.Matrix.GeneralLinearGroup.Projective
public import Mathlib.NumberTheory.Chebyshev
public import Mathlib.NumberTheory.Height.NumberField
public import Mathlib.NumberTheory.Height.Projectivization
public import Mathlib.NumberTheory.LucasLehmer
public import Mathlib.NumberTheory.SelbergSieve
public import Mathlib.RingTheory.Radical.NatInt
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

public noncomputable section

namespace CFSG.ComponentClassification.CatalogueBProjectiveInvolution

open Matrix

variable {ι K : Type*} [Fintype ι] [DecidableEq ι] [Field K]

theorem scalarGL_injective [Nonempty ι] :
    Function.Injective (GeneralLinearGroup.scalar ι : Kˣ →* GL ι K) := by
  intro a b hab
  let i : ι := Classical.choice inferInstance
  apply Units.ext
  simpa [GeneralLinearGroup.scalar] using congrArg (fun A : GL ι K => A.val i i) hab

@[expose] def projectiveCentralizerLift (A : GL ι K) : Subgroup (GL ι K) :=
  (Subgroup.centralizer {ProjGenLinGroup.mk A}).comap ProjGenLinGroup.mk

theorem exists_scalarDisplacement (A : GL ι K) (B : projectiveCentralizerLift A) :
    ∃ c : Kˣ, A * B.val * GeneralLinearGroup.scalar ι c = B.val * A := by
  apply ProjGenLinGroup.mk_eq_mk_iff.mp
  simpa only [map_mul] using
    (Subgroup.mem_centralizer_singleton_iff.mp B.property).symm

@[expose] def scalarDisplacement (A : GL ι K) (B : projectiveCentralizerLift A) : Kˣ :=
  (exists_scalarDisplacement A B).choose

theorem scalarDisplacement_spec (A : GL ι K) (B : projectiveCentralizerLift A) :
    A * B.val * GeneralLinearGroup.scalar ι (scalarDisplacement A B) = B.val * A :=
  (exists_scalarDisplacement A B).choose_spec

theorem scalarDisplacement_unique [Nonempty ι] (A : GL ι K) (B : projectiveCentralizerLift A) (c : Kˣ)
    (hc : A * B.val * GeneralLinearGroup.scalar ι c = B.val * A) :
    scalarDisplacement A B = c :=
  scalarGL_injective (mul_left_cancel ((scalarDisplacement_spec A B).trans hc.symm))

@[expose] def scalarDisplacementHom [Nonempty ι] (A : GL ι K) : projectiveCentralizerLift A →* Kˣ where
  toFun := scalarDisplacement A
  map_one' := scalarDisplacement_unique A 1 1 (by simp)
  map_mul' B C := by
    apply scalarDisplacement_unique
    change A * (B.val * C.val) * GeneralLinearGroup.scalar ι
      (scalarDisplacement A B * scalarDisplacement A C) = B.val * C.val * A
    rw [map_mul]
    calc
      A * (B.val * C.val) *
          (GeneralLinearGroup.scalar ι (scalarDisplacement A B) *
            GeneralLinearGroup.scalar ι (scalarDisplacement A C)) =
        (A * B.val * GeneralLinearGroup.scalar ι (scalarDisplacement A B)) *
          C.val * GeneralLinearGroup.scalar ι (scalarDisplacement A C) := by
            simp only [mul_assoc]
            rw [← GeneralLinearGroup.scalar_commute _ C.val]
            rw [GeneralLinearGroup.scalar_commute _ C.val]
            rw [← mul_assoc C.val, ← GeneralLinearGroup.scalar_commute _ C.val, mul_assoc]
      _ = (B.val * A) * C.val *
          GeneralLinearGroup.scalar ι (scalarDisplacement A C) := by rw [scalarDisplacement_spec]
      _ = B.val * (A * C.val * GeneralLinearGroup.scalar ι (scalarDisplacement A C)) := by group
      _ = B.val * C.val * A := by rw [scalarDisplacement_spec]; group

theorem scalarDisplacement_eq_one_iff [Nonempty ι] (A : GL ι K) (B : projectiveCentralizerLift A) :
    scalarDisplacement A B = 1 ↔ B.val * A = A * B.val := by
  constructor
  · intro h
    simpa only [h, map_one, mul_one] using (scalarDisplacement_spec A B).symm
  · intro h
    exact scalarDisplacement_unique A B 1 (by simpa using h.symm)

theorem matrix_square_scalar (A : GL ι K) (hsquare : ProjGenLinGroup.mk A ^ 2 = 1) :
    ∃ lambda : Kˣ, A ^ 2 = GeneralLinearGroup.scalar ι lambda := by
  have hcentral : A ^ 2 ∈ Subgroup.center (GL ι K) := by
    apply ProjGenLinGroup.mk_eq_one.mp
    simpa only [map_pow] using hsquare
  rw [GeneralLinearGroup.center_eq_range_scalar] at hcentral
  obtain ⟨lambda, hlambda⟩ := hcentral
  exact ⟨lambda, hlambda.symm⟩

theorem scalarDisplacement_square_eq_one [Nonempty ι] (A : GL ι K)
    (hsquare : ProjGenLinGroup.mk A ^ 2 = 1) (B : projectiveCentralizerLift A) :
    scalarDisplacement A B ^ 2 = 1 := by
  let S := GeneralLinearGroup.scalar ι (scalarDisplacement A B)
  have hBA : B.val * A = A * B.val * S := (scalarDisplacement_spec A B).symm
  have hAS : S * A = A * S := GeneralLinearGroup.scalar_commute _ _
  have hcentral : A ^ 2 ∈ Subgroup.center (GL ι K) := by
    apply ProjGenLinGroup.mk_eq_one.mp
    simpa only [map_pow] using hsquare
  have hcomm := Subgroup.mem_center_iff.mp hcentral B.val
  have hcancel : (A ^ 2 * B.val) * (S ^ 2) = A ^ 2 * B.val := by
    calc
      (A ^ 2 * B.val) * (S ^ 2) = A * (A * B.val * S) * S := by
        simp only [pow_two, mul_assoc]
      _ = A * (B.val * A) * S := by rw [← hBA]
      _ = (A * B.val * S) * A := by simp only [mul_assoc]; rw [hAS]
      _ = B.val * A * A := by rw [← hBA]
      _ = A ^ 2 * B.val := by simpa only [pow_two, mul_assoc] using hcomm
  have hS : S ^ 2 = 1 := mul_left_cancel (by simpa only [mul_one] using hcancel)
  apply scalarGL_injective (ι := ι) (K := K)
  simpa only [map_pow, map_one, S] using hS

@[expose] def projectiveCentralizerProjection (A : GL ι K) :
    projectiveCentralizerLift A →* Subgroup.centralizer {ProjGenLinGroup.mk A} :=
  (ProjGenLinGroup.mk.comp (projectiveCentralizerLift A).subtype).codRestrict _
    (fun B => B.property)

theorem projectiveCentralizerProjection_surjective (A : GL ι K) :
    Function.Surjective (projectiveCentralizerProjection A) := by
  intro b
  obtain ⟨B, hB⟩ := ProjGenLinGroup.mk_surjective b.val
  refine ⟨⟨B, ?_⟩, Subtype.ext hB⟩
  change ProjGenLinGroup.mk B ∈ Subgroup.centralizer {ProjGenLinGroup.mk A}
  rw [hB]
  exact b.property

theorem projectiveCentralizerProjection_kernel_le [Nonempty ι] (A : GL ι K) :
    (projectiveCentralizerProjection A).ker ≤ (scalarDisplacementHom A).ker := by
  intro B hB
  change scalarDisplacement A B = 1
  apply (scalarDisplacement_eq_one_iff A B).mpr
  have hmk : ProjGenLinGroup.mk B.val = 1 := congrArg Subtype.val hB
  exact (Subgroup.mem_center_iff.mp (ProjGenLinGroup.mk_eq_one.mp hmk) A).symm

@[expose] def projectiveCentralizerQuotientEquiv (A : GL ι K) :
    (projectiveCentralizerLift A ⧸ (projectiveCentralizerProjection A).ker) ≃*
      Subgroup.centralizer {ProjGenLinGroup.mk A} :=
  QuotientGroup.quotientKerEquivOfSurjective _ (projectiveCentralizerProjection_surjective A)

@[expose] def projectiveScalarCharacter [Nonempty ι] (A : GL ι K) :
    Subgroup.centralizer {ProjGenLinGroup.mk A} →* Kˣ :=
  (QuotientGroup.lift (projectiveCentralizerProjection A).ker
    (scalarDisplacementHom A) (projectiveCentralizerProjection_kernel_le A)).comp
      (projectiveCentralizerQuotientEquiv A).symm.toMonoidHom

theorem projectiveScalarCharacter_projection [Nonempty ι] (A : GL ι K) (B : projectiveCentralizerLift A) :
    projectiveScalarCharacter A (projectiveCentralizerProjection A B) = scalarDisplacement A B := by
  have h := (projectiveCentralizerQuotientEquiv A).symm_apply_apply
    ((QuotientGroup.mk' (projectiveCentralizerProjection A).ker) B)
  change (projectiveCentralizerQuotientEquiv A).symm (projectiveCentralizerProjection A B) = _ at h
  change QuotientGroup.lift _ (scalarDisplacementHom A)
    (projectiveCentralizerProjection_kernel_le A)
    ((projectiveCentralizerQuotientEquiv A).symm (projectiveCentralizerProjection A B)) = _
  rw [h]
  rfl

@[expose] def ordinaryCentralizerProjection (A : GL ι K) :
    Subgroup.centralizer {A} →* Subgroup.centralizer {ProjGenLinGroup.mk A} where
  toFun B := ⟨ProjGenLinGroup.mk B.val, Subgroup.mem_centralizer_singleton_iff.mpr (by
    simpa only [map_mul] using congrArg ProjGenLinGroup.mk
      (Subgroup.mem_centralizer_singleton_iff.mp B.property))⟩
  map_one' := rfl
  map_mul' _ _ := rfl

theorem projectiveScalarCharacter_kernel_eq [Nonempty ι] (A : GL ι K) :
    (projectiveScalarCharacter A).ker = (ordinaryCentralizerProjection A).range := by
  ext b
  constructor
  · intro hb
    obtain ⟨B, hB⟩ := projectiveCentralizerProjection_surjective A b
    have hdisplacement : scalarDisplacement A B = 1 := by
      rw [← projectiveScalarCharacter_projection, hB]
      exact hb
    refine ⟨⟨B.val, Subgroup.mem_centralizer_singleton_iff.mpr
      ((scalarDisplacement_eq_one_iff A B).mp hdisplacement)⟩, ?_⟩
    exact hB
  · rintro ⟨B, rfl⟩
    let Blift : projectiveCentralizerLift A := ⟨B.val,
      (ordinaryCentralizerProjection A B).property⟩
    change projectiveScalarCharacter A (projectiveCentralizerProjection A Blift) = 1
    rw [projectiveScalarCharacter_projection]
    exact (scalarDisplacement_eq_one_iff A Blift).mpr
      (Subgroup.mem_centralizer_singleton_iff.mp B.property)

theorem ordinaryCentralizerProjection_range_normal [Nonempty ι] (A : GL ι K) :
    (ordinaryCentralizerProjection A).range.Normal := by
  rw [← projectiveScalarCharacter_kernel_eq]
  infer_instance

theorem projectiveScalarCharacter_square_eq_one [Nonempty ι] (A : GL ι K)
    (hsquare : ProjGenLinGroup.mk A ^ 2 = 1)
    (b : Subgroup.centralizer {ProjGenLinGroup.mk A}) :
    projectiveScalarCharacter A b ^ 2 = 1 := by
  obtain ⟨B, rfl⟩ := projectiveCentralizerProjection_surjective A b
  rw [projectiveScalarCharacter_projection]
  exact scalarDisplacement_square_eq_one A hsquare B

@[expose] def projectiveScalarRangeToRoots [Nonempty ι] (A : GL ι K)
    (hsquare : ProjGenLinGroup.mk A ^ 2 = 1) :
    (projectiveScalarCharacter A).range →* rootsOfUnity 2 K where
  toFun b := ⟨b.val, by
    obtain ⟨c, hc⟩ := b.property
    rw [mem_rootsOfUnity, ← hc]
    exact projectiveScalarCharacter_square_eq_one A hsquare c⟩
  map_one' := rfl
  map_mul' _ _ := rfl

theorem projectiveScalarRangeToRoots_injective [Nonempty ι] (A : GL ι K)
    (hsquare : ProjGenLinGroup.mk A ^ 2 = 1) :
    Function.Injective (projectiveScalarRangeToRoots A hsquare) := by
  intro b c h
  exact Subtype.ext (congrArg (fun x : rootsOfUnity 2 K => x.val) h)

theorem ordinaryCentralizerProjection_range_index_le_two [Nonempty ι] (A : GL ι K)
    (hsquare : ProjGenLinGroup.mk A ^ 2 = 1) :
    (ordinaryCentralizerProjection A).range.index ≤ 2 := by
  rw [← projectiveScalarCharacter_kernel_eq, Subgroup.index_ker]
  exact (Nat.card_le_card_of_injective _ (projectiveScalarRangeToRoots_injective A hsquare)).trans
    (card_rootsOfUnity K 2)

end CFSG.ComponentClassification.CatalogueBProjectiveInvolution
