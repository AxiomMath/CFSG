module

public import CFSG.LocalAnalysis.AGLEmbeddingD2.McLaughlin.WeakBlockModuleData.OutCover
public import CFSG.LocalAnalysis.ComponentClassification.OuterAutomorphisms
public import CFSG.Open.Defs
import CFSG.LocalAnalysis.SectionRank.PRank
import CFSG.LocalAnalysis.AGLEmbeddingD2.Tits.MsideParabolicEscape.I811.OvergroupDefs
import CFSG.LocalAnalysis.AGLEmbeddingD2.Tits.MsideParabolicEscape.TwoLocalSylow
import CFSG.LocalAnalysis.AGLEmbeddingD2.L34BetaHPara
import CFSG.LocalAnalysis.AGLEmbedding.OneSmallGEVL34Ph6
import CFSG.LocalAnalysis.AGLEmbedding.OneSmallGEVIbL34Cover
import CFSG.LocalAnalysis.AGLEmbedding.OneSmallGEVIbL34Esc
import CFSG.LocalAnalysis.AGLEmbedding.OneSmallGEVIbThreeMain
import CFSG.LocalAnalysis.AGLEmbedding.OneSmallGEVCoreL34
import CFSG.LocalAnalysis.AGLEmbedding.OneSmallGEVIbThreePerf
import CFSG.LocalAnalysis.AGLEmbedding.MSideAtFusion
import CFSG.LocalAnalysis.AGLEmbedding.MSideAtInner
import CFSG.LocalAnalysis.AGLEmbeddingD2.Tits.MsideParabolicEscape.AGL81I811Defs
import CFSG.Adapters.QiuzhenLegacy.FeitThompson.Gorenstein.RelativeZJ
import CFSG.GroupTheory.SteinbergCBFTCores
import CFSG.Sporadic.Schreier.J4SCheckBase
import CFSG.Sporadic.Schreier.J4SBinaryBase
import CFSG.LocalAnalysis.AGLEmbeddingD2.Tits.OrdinaryProofs.PSolvableClosure
import Lean.Data.Json
import Mathlib.Algebra.AffineMonoid.Basic
import Mathlib.Algebra.Algebra.Subalgebra.Basic
import Mathlib.Algebra.Algebra.Subalgebra.Lattice
import Mathlib.Algebra.BigOperators.Field
import Mathlib.Algebra.BigOperators.Group.Finset.Lemmas
import Mathlib.Algebra.Category.ModuleCat.Abelian
import Mathlib.Algebra.Category.ModuleCat.Colimits
import Mathlib.Algebra.CharP.Basic
import Mathlib.Algebra.CharP.Frobenius
import Mathlib.Algebra.CharP.Two
import Mathlib.Algebra.Field.Basic
import Mathlib.Algebra.Field.Shrink
import Mathlib.Algebra.Group.Action.End
import Mathlib.Algebra.Group.Action.Hom
import Mathlib.Algebra.Group.Action.Pointwise.Set.Basic
import Mathlib.Algebra.Group.Commutator
import Mathlib.Algebra.Group.Pointwise.Set.Card
import Mathlib.Algebra.Group.Subgroup.Even
import Mathlib.Algebra.Group.Subgroup.Ker
import Mathlib.Algebra.Group.Subgroup.Order
import Mathlib.Algebra.Group.Subgroup.ZPowers.Basic
import Mathlib.Algebra.Group.Submonoid.Operations
import Mathlib.Algebra.Group.TypeTags.Hom
import Mathlib.Algebra.GroupWithZero.TransferInstance
import Mathlib.Algebra.Module.Card
import Mathlib.Algebra.Module.Projective
import Mathlib.Algebra.Module.Submodule.Pointwise
import Mathlib.Algebra.MvPolynomial.Equiv
import Mathlib.Algebra.Order.Ring.GeomSum
import Mathlib.Algebra.Polynomial.BigOperators
import Mathlib.Algebra.Polynomial.Roots
import Mathlib.Algebra.QuadraticAlgebra.IsQuadraticExtension
import Mathlib.Algebra.QuadraticAlgebra.NormDeterminant
import Mathlib.Algebra.Ring.Action.End
import Mathlib.Algebra.Ring.Basic
import Mathlib.Algebra.Ring.Commute
import Mathlib.Algebra.Ring.Shrink
import Mathlib.Analysis.Fourier.FiniteAbelian.PontryaginDuality
import Mathlib.CategoryTheory.Limits.Shapes.ZeroObjects
import Mathlib.CategoryTheory.Preadditive.Schur
import Mathlib.Combinatorics.SimpleGraph.Finite
import Mathlib.Combinatorics.SimpleGraph.Paths
import Mathlib.Data.Fin.Tuple.Basic
import Mathlib.Data.Fin.Tuple.Sort
import Mathlib.Data.Fin.VecNotation
import Mathlib.SetTheory.Cardinal.NatCard
import Mathlib.Data.List.Basic
import Mathlib.Data.Matrix.Basis
import Mathlib.Data.Matrix.Mul
import Mathlib.Data.Nat.Factorial.Basic
import Mathlib.Data.Set.Finite.Lemmas
import Mathlib.Data.ZMod.QuotientGroup
import Mathlib.Data.ZMod.Units
import Mathlib.FieldTheory.Galois.Basic
import Mathlib.GroupTheory.Abelianization.Finite
import Mathlib.GroupTheory.GroupExtension.Basic
import Mathlib.GroupTheory.Perm.Closure
import Mathlib.GroupTheory.Perm.Fin
import Mathlib.GroupTheory.Perm.Finite
import Mathlib.GroupTheory.RegularWreathProduct
import Mathlib.GroupTheory.SpecificGroups.Cyclic.Basic
import Mathlib.LinearAlgebra.Basis.Fin
import Mathlib.LinearAlgebra.Basis.Submodule
import Mathlib.LinearAlgebra.Center
import Mathlib.LinearAlgebra.CliffordAlgebra.SpinGroup
import Mathlib.LinearAlgebra.Dimension.Finite
import Mathlib.LinearAlgebra.Dimension.RankNullity
import Mathlib.LinearAlgebra.LinearIndependent.Lemmas
import Mathlib.LinearAlgebra.Matrix.Basis
import Mathlib.LinearAlgebra.Matrix.Hermitian
import Mathlib.LinearAlgebra.Matrix.NonsingularInverse
import Mathlib.LinearAlgebra.Matrix.Notation
import Mathlib.LinearAlgebra.Matrix.Reindex
import Mathlib.LinearAlgebra.Matrix.Transvection
import Mathlib.LinearAlgebra.Projectivization.Basic
import Mathlib.LinearAlgebra.QuadraticForm.Prod
import Mathlib.LinearAlgebra.QuadraticForm.Radical
import Mathlib.LinearAlgebra.QuadraticForm.TensorProduct
import Mathlib.LinearAlgebra.Quotient.Basic
import Mathlib.LinearAlgebra.Span.Basic
import Mathlib.LinearAlgebra.StdBasis
import Mathlib.LinearAlgebra.TensorProduct.Basic
import Mathlib.LinearAlgebra.TensorProduct.Basis
import Mathlib.LinearAlgebra.TensorProduct.Free
import Mathlib.LinearAlgebra.TensorProduct.Lift
import Mathlib.LinearAlgebra.TensorProduct.Map
import Mathlib.LinearAlgebra.TensorProduct.Tower
import Mathlib.NumberTheory.LegendreSymbol.QuadraticChar.GaussSum
import Mathlib.NumberTheory.MulChar.Lemmas
import Mathlib.NumberTheory.NumberField.Cyclotomic.Basic
import Mathlib.NumberTheory.Padics.PadicVal.Basic
import Mathlib.Order.Atoms
import Mathlib.Order.Interval.Finset.Nat
import Mathlib.Order.KrullDimension
import Mathlib.Order.Preorder.Finite
import Mathlib.RingTheory.AlgebraicIndependent.Adjoin
import Mathlib.RingTheory.Finiteness.Cardinality
import Mathlib.RingTheory.Flat.Basic
import Mathlib.RingTheory.Norm.Transitivity
import Mathlib.RingTheory.Polynomial.RationalRoot
import Mathlib.RingTheory.RootsOfUnity.Basic
import Mathlib.RingTheory.RootsOfUnity.PrimitiveRoots
import Mathlib.RingTheory.TensorProduct.Finite
import Mathlib.RingTheory.TensorProduct.Free
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Module
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Positivity
import Mathlib.Tactic.Push
import TauCeti.Algebra.Central.TensorProduct
import TauCeti.Algebra.Group.Subgroup.Map
import TauCeti.LinearAlgebra.ExteriorAlgebra.Dimension
import TauCeti.LinearAlgebra.Matrix.GeneralLinearGroup.Diagonal.Basic
import TauCeti.LinearAlgebra.Matrix.GeneralLinearGroup.GraphAutomorphism
import TauCeti.LinearAlgebra.Matrix.GeneralLinearGroup.Symplectic.Levi
import TauCeti.LinearAlgebra.QuadraticForm.Isometry
import TauCeti.LinearAlgebra.QuadraticForm.Prod
import TauCeti.LinearAlgebra.SymplecticGroup
import TauCeti.RepresentationTheory.Spin.Polarization.Split.Even

public section

namespace CFSG.LocalAnalysis.RankThreeTheoremC.L28.OutThree

open CFSG.ComponentClassification.OuterAutomorphisms Subgroup
open CFSG.AGLEmbeddingD2.McLaughlin.WeakBlockModuleData (AutThreePowInner)

@[expose] def OutCommInner (X : Type*) [Group X] : Prop :=
  ∀ α β : MulAut X, α * β * α⁻¹ * β⁻¹ ∈ (MulAut.conj : X →* MulAut X).range

theorem mulAut_congr_conj {X X' : Type*} [Group X] [Group X'] (e : X ≃* X') (x : X) :
    MulAut.congr e (MulAut.conj x) = MulAut.conj (e x) := by
  ext y
  simp [MulAut.congr_apply, MulAut.conj_apply]

theorem OutCommInner.of_mulEquiv {X X' : Type*} [Group X] [Group X'] (e : X ≃* X')
    (h : OutCommInner X') : OutCommInner X := by
  intro α β
  obtain ⟨x', hx'⟩ := h (MulAut.congr e α) (MulAut.congr e β)
  refine ⟨e.symm x', (MulAut.congr e).injective ?_⟩
  rw [mulAut_congr_conj, MulEquiv.apply_symm_apply, hx']
  simp only [map_mul, map_inv]

theorem outCommInner_of_forall_inner {X : Type*} [Group X]
    (h : ∀ φ : MulAut X, ∃ g : X, φ = MulAut.conj g) : OutCommInner X := fun α β => by
  obtain ⟨g, hg⟩ := h (α * β * α⁻¹ * β⁻¹)
  exact ⟨g, hg.symm⟩

theorem outCommInner_of_outer_comm {X : Type*} [Group X]
    (h : ∀ a b : Outer X, a * b = b * a) : OutCommInner X := by
  intro α β
  have h1 : ((α * β * α⁻¹ * β⁻¹ : MulAut X) : Outer X) = 1 := by
    rw [QuotientGroup.mk_mul, QuotientGroup.mk_mul, QuotientGroup.mk_mul, QuotientGroup.mk_inv,
      QuotientGroup.mk_inv, h (α : Outer X) β]
    group
  exact (QuotientGroup.eq_one_iff (N := inner X) _).mp h1

theorem outCommInner_of_outer_commutator_mem {X : Type*} [Group X] (N : Subgroup (Outer X))
    (hN : Nat.card N = 1) (h : ∀ a b : Outer X, a * b * a⁻¹ * b⁻¹ ∈ N) : OutCommInner X := by
  have hbot : N = ⊥ := Subgroup.eq_bot_of_card_eq N hN
  refine outCommInner_of_outer_comm fun a b => ?_
  have h1 := h a b
  rw [hbot, Subgroup.mem_bot] at h1
  calc a * b = (a * b * a⁻¹ * b⁻¹) * (b * a) := by group
    _ = b * a := by rw [h1, one_mul]

variable {Y : Type*} [Group Y]

theorem sup_centralizer_eq_map_comap (K : Subgroup Y) :
    K ⊔ centralizer (K : Set Y) =
      ((MulAut.conj : K →* MulAut K).range.comap K.normalizerMonoidHom).map
        (normalizer (K : Set Y)).subtype := by
  apply le_antisymm
  · rw [sup_le_iff]
    constructor
    · intro k hk
      refine ⟨⟨k, le_normalizer hk⟩, ⟨⟨k, hk⟩, ?_⟩, rfl⟩
      ext x
      simp [MulAut.conj_apply]
    · intro c hc
      refine ⟨⟨c, centralizer_le_normalizer _ hc⟩, ⟨1, ?_⟩, rfl⟩
      ext x
      have hcx : c * (x : Y) = x * c := (mem_centralizer_iff.mp hc x x.2).symm
      simp only [map_one, MulAut.one_apply, normalizerMonoidHom_apply_apply_coe]
      calc (x : Y) = x * c * c⁻¹ := by group
        _ = c * x * c⁻¹ := by rw [hcx]
  · rintro _ ⟨⟨n, hn⟩, ⟨k, hk⟩, rfl⟩
    have hkn : ∀ x : K, (k : Y) * x * (k : Y)⁻¹ = n * x * n⁻¹ := by
      intro x
      have h1 := congrArg (fun φ : MulAut K => ((φ x : K) : Y)) hk
      simpa [MulAut.conj_apply] using h1
    have hc : (k : Y)⁻¹ * n ∈ centralizer (K : Set Y) := by
      rw [mem_centralizer_iff]
      intro x hx
      have h1 := hkn ⟨x, hx⟩
      simp only at h1
      calc x * ((k : Y)⁻¹ * n) = (k : Y)⁻¹ * ((k : Y) * x * (k : Y)⁻¹) * n := by group
        _ = (k : Y)⁻¹ * (n * x * n⁻¹) * n := by rw [h1]
        _ = (k : Y)⁻¹ * n * x := by group
    have hn' : n = k * ((k : Y)⁻¹ * n) := by group
    change n ∈ K ⊔ centralizer (K : Set Y)
    rw [hn']
    exact mul_mem_sup k.2 hc

theorem mulAut_pow_apply {X : Type*} [Group X] (ψ : MulAut X) (m : ℕ) (x : X) :
    (ψ ^ m) x = ψ^[m] x := by
  induction m generalizing x with
  | zero => rfl
  | succ m ih =>
    rw [pow_succ, Function.iterate_succ_apply, ← ih]
    rfl

theorem mem_sup_centralizer_of_autThreePowInner {K : Subgroup Y} (hK : AutThreePowInner K)
    {d : Y} (hd : d ∈ normalizer (K : Set Y)) {n : ℕ} (hn : d ^ 3 ^ n = 1) :
    d ∈ K ⊔ centralizer (K : Set Y) := by
  rw [sup_centralizer_eq_map_comap]
  refine ⟨⟨d, hd⟩, ?_, rfl⟩
  have hd1 : (⟨d, hd⟩ : normalizer (K : Set Y)) ^ 3 ^ n = 1 := Subtype.ext (by simpa using hn)
  have hψ : ∀ x, (K.normalizerMonoidHom ⟨d, hd⟩)^[3 ^ n] x = x := by
    intro x
    rw [← mulAut_pow_apply, ← map_pow, hd1, map_one]
    rfl
  obtain ⟨a, ha⟩ := hK _ n hψ
  exact ⟨a, MulEquiv.ext fun x => (ha x).symm⟩

theorem exists_threeComplement_of_outCommInner [Finite Y] {K : Subgroup Y}
    (hK : OutCommInner K) :
    ∃ R : Subgroup Y, R ≤ normalizer (K : Set Y) ∧
      (∀ g ∈ normalizer (K : Set Y), ∀ r ∈ R, g * r * g⁻¹ ∈ R) ∧
      K ⊔ centralizer (K : Set Y) ≤ R ∧
      (∀ d ∈ normalizer (K : Set Y), ∃ n : ℕ, d ^ 3 ^ n ∈ R) ∧
      ∀ d ∈ R, (∃ n : ℕ, d ^ 3 ^ n ∈ K ⊔ centralizer (K : Set Y)) →
        d ∈ K ⊔ centralizer (K : Set Y) := by
  set N := normalizer (K : Set Y) with hNdef
  set ρ : N →* MulAut K := K.normalizerMonoidHom
  set M : Subgroup N := (inner K).comap ρ with hMdef
  have hMn : M.Normal := (inner_normal K).comap ρ
  have hMKC : K ⊔ centralizer (K : Set Y) = M.map N.subtype := sup_centralizer_eq_map_comap K
  set φ : N →* N ⧸ M := QuotientGroup.mk' M
  have hφ : ∀ x : N, φ x = 1 ↔ x ∈ M := fun x => QuotientGroup.eq_one_iff x
  have hcomm : ∀ a b : N ⧸ M, a * b = b * a := by
    intro a b
    induction a using QuotientGroup.induction_on with
    | H x =>
    induction b using QuotientGroup.induction_on with
    | H y =>
    rw [← QuotientGroup.mk_mul, ← QuotientGroup.mk_mul, QuotientGroup.eq]
    change ρ ((x * y)⁻¹ * (y * x)) ∈ (MulAut.conj : K →* MulAut K).range
    have h1 : ρ ((x * y)⁻¹ * (y * x)) =
        (ρ y)⁻¹ * (ρ x)⁻¹ * ((ρ y)⁻¹)⁻¹ * ((ρ x)⁻¹)⁻¹ := by
      simp only [mul_inv_rev, map_mul, map_inv, inv_inv]
      group
    rw [h1]
    exact hK _ _
  set b := ordCompl[3] (Nat.card Y) with hb
  have hY0 : Nat.card Y ≠ 0 := Nat.card_pos.ne'
  have hb3 : ∀ n : ℕ, Nat.Coprime (3 ^ n) b := fun n =>
    Nat.Coprime.pow_left n (Nat.coprime_ordCompl Nat.prime_three hY0)
  let S : Subgroup (N ⧸ M) :=
    { carrier := {x | x ^ b = 1}
      mul_mem' := fun {x y} hx hy => by
        simp only [Set.mem_setOf_eq] at hx hy ⊢
        rw [(show Commute x y from hcomm x y).mul_pow, hx, hy, one_mul]
      one_mem' := by simp
      inv_mem' := fun {x} hx => by
        simp only [Set.mem_setOf_eq] at hx ⊢
        rw [inv_pow, hx, inv_one] }
  have hS : ∀ x, x ∈ S ↔ x ^ b = 1 := fun x => Iff.rfl
  refine ⟨(S.comap φ).map N.subtype, map_subtype_le _, ?_, ?_, ?_, ?_⟩
  · rintro g hg _ ⟨x, hx, rfl⟩
    refine ⟨⟨g, hg⟩ * x * ⟨g, hg⟩⁻¹, ?_, rfl⟩
    change φ (⟨g, hg⟩ * x * ⟨g, hg⟩⁻¹) ∈ S
    rw [map_mul, map_mul, hcomm (φ ⟨g, hg⟩) (φ x), mul_assoc, map_inv, mul_inv_cancel, mul_one]
    exact hx
  · rw [hMKC]
    refine map_mono fun x hx => ?_
    change φ x ∈ S
    rw [hS, (hφ x).mpr hx, one_pow]
  · intro d hd
    refine ⟨(Nat.card Y).factorization 3, ⟨⟨d, hd⟩ ^ 3 ^ (Nat.card Y).factorization 3, ?_, rfl⟩⟩
    change φ _ ∈ S
    rw [hS, ← map_pow, ← pow_mul, hb, Nat.ordProj_mul_ordCompl_eq_self]
    have h1 : (⟨d, hd⟩ : N) ^ Nat.card Y = 1 := Subtype.ext (by simp [pow_card_eq_one'])
    rw [h1, map_one]
  · rintro _ ⟨x, hx, rfl⟩ ⟨n, hn⟩
    rw [hMKC] at hn ⊢
    obtain ⟨z, hz, hzx⟩ := hn
    have hzx' : z = x ^ 3 ^ n := Subtype.ext (by simpa using hzx)
    have h3 : φ x ^ 3 ^ n = 1 := by rw [← map_pow, ← hzx', hφ]; exact hz
    have hbx : φ x ^ b = 1 := hx
    have h1 : φ x = 1 := by
      have := pow_gcd_eq_one.mpr ⟨h3, hbx⟩
      rwa [(hb3 n).gcd_eq_one, pow_one] at this
    exact ⟨x, (hφ x).mp h1, rfl⟩

theorem not_nine_dvd_of_factorization {n : ℕ} (h : n.factorization 3 = 1) : ¬ 9 ∣ n := by
  intro h9
  have hn : n ≠ 0 := by
    rintro rfl
    simp at h
  have h2 := (Nat.Prime.pow_dvd_iff_le_factorization (k := 2) Nat.prime_three hn).mp
    (by norm_num; exact h9)
  omega

theorem three_dvd_of_factorization {n : ℕ} (h : n.factorization 3 = 1) : 3 ∣ n :=
  Nat.dvd_of_factorization_pos (by omega)

theorem nine_dvd_sq_sub_one {p f : ℕ} (hp : ¬ 3 ∣ p) (hf : 3 ∣ f) : 9 ∣ (p ^ f) ^ 2 - 1 := by
  obtain ⟨g, rfl⟩ := hf
  have hp2 : p ^ 2 % 3 = 1 := by
    rcases (by omega : p % 3 = 1 ∨ p % 3 = 2) with h | h <;> rw [Nat.pow_mod, h]
  have hr : (p ^ 2) ^ g % 3 = 1 := by
    rw [Nat.pow_mod, hp2, one_pow]
    norm_num
  have h9 : ((p ^ 2) ^ g) ^ 3 % 9 = 1 := by
    rcases (by omega : (p ^ 2) ^ g % 9 = 1 ∨ (p ^ 2) ^ g % 9 = 4 ∨ (p ^ 2) ^ g % 9 = 7) with
      h | h | h <;> rw [Nat.pow_mod, h]
  have heq : (p ^ (3 * g)) ^ 2 = ((p ^ 2) ^ g) ^ 3 := by ring
  rw [heq]
  omega

theorem pRank_three_top_eq_one {X : Type} [Group X] [Finite X]
    (h : (Nat.card X).factorization 3 = 1) : CFSG.Open.pRank 3 (⊤ : Subgroup X) = 1 := by
  have : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  obtain ⟨g, hg⟩ := exists_prime_orderOf_dvd_card' 3 (three_dvd_of_factorization h)
  refine CFSG.AGLEmbeddingD2.Tits.MsideParabolicEscape.I811.pRank_three_eq_one_of_cyclic ?_
    (A := Subgroup.zpowers g) (by rw [Nat.card_zpowers, hg])
  intro P hP
  obtain ⟨k, hk⟩ := hP.exists_card_eq
  have hdvd : 3 ^ k ∣ Nat.card X := hk ▸ Subgroup.card_subgroup_dvd_card P
  have hk1 : k ≤ 1 := by
    have := (Nat.Prime.pow_dvd_iff_le_factorization Nat.prime_three Nat.card_pos.ne').mp hdvd
    omega
  interval_cases k
  · have : Subsingleton P := Finite.card_le_one_iff_subsingleton.mp (by rw [hk, pow_zero])
    infer_instance
  · exact isCyclic_of_prime_card (by rw [hk, pow_one])

theorem one_le_pRank_three_top {X : Type} [Group X] [Finite X] (h : 3 ∣ Nat.card X) :
    1 ≤ CFSG.Open.pRank 3 (⊤ : Subgroup X) := by
  have : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  obtain ⟨g, hg⟩ := exists_prime_orderOf_dvd_card' 3 h
  have hA : Nat.card (Subgroup.zpowers g) = 3 := by rw [Nat.card_zpowers, hg]
  have : IsCyclic (Subgroup.zpowers g) := isCyclic_of_prime_card hA
  refine CFSG.SectionRank.le_pRank (by norm_num) le_top
    ⟨IsCyclic.isMulCommutative, fun x hx => ?_⟩ (k := 1) (by rw [hA, pow_one])
  have h1 := pow_card_eq_one' (G := Subgroup.zpowers g) (x := ⟨x, hx⟩)
  rw [hA] at h1
  exact congrArg Subtype.val h1

end CFSG.LocalAnalysis.RankThreeTheoremC.L28.OutThree
