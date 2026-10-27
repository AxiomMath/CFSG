module

public import CFSG.GroupTheory.SteinbergBKFrobeniusPartition
public import CFSG.Foundations.Basic
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
public import Mathlib.RingTheory.WittVector.IsPoly
public import Mathlib.Tactic.Basify
public import Mathlib.Tactic.ENatToNat
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
public import Std.Tactic.BVDecide.Normalize.Prop

public section

open scoped Classical

namespace CFSG.CharacterTheory.SteinbergBY

open CFSG

theorem frobenius_representation_sum_identity {G F V : Type*} [Group G] [Fintype G] [Field F]
    [AddCommGroup V] [Module F V] {K R : Subgroup G} [K.Normal] (hKR : K.IsComplement' R)
    (hfix : ∀ r ∈ R, r ≠ 1 → ∀ k ∈ K, k * r = r * k → k = 1)
    (ρ : G →* LinearMap.GeneralLinearGroup F V) :
    (∑ g : G, (ρ g : V →ₗ[F] V)) + (Nat.card K : F) • LinearMap.id =
      (∑ k : K, (ρ k : V →ₗ[F] V)) + ∑ k : K, ∑ x : conjugate R (k : G), (ρ x : V →ₗ[F] V) := by
  set f : G → V →ₗ[F] V := fun g => (ρ g : V →ₗ[F] V) with hf
  obtain ⟨hcover, hdisjK, hpair⟩ := GroupTheory.SteinbergBK.frobenius_complement_partition hKR hfix
  have hf1 : f 1 = LinearMap.id := by simp [hf]; rfl
  have hconj : ∀ k : K, ∑ x : conjugate R (k : G), f x =
      f 1 + ∑ r ∈ (Finset.univ : Finset R).erase 1, f ((k : G)⁻¹ * r * k) := by
    intro k
    have h1 : ∑ x : conjugate R (k : G), f x = ∑ r : R, f ((k : G)⁻¹ * r * k) := by
      refine (Fintype.sum_equiv ((MulAut.conj (k : G)⁻¹).subgroupMap R).toEquiv _ _
        fun r => ?_).symm
      simp
    rw [h1, ← Finset.add_sum_erase _ _ (Finset.mem_univ (1 : R))]
    simp
  have hout : ∑ g ∈ Finset.univ.filter (fun g : G => g ∉ K), f g =
      ∑ k : K, ∑ r ∈ (Finset.univ : Finset R).erase 1, f ((k : G)⁻¹ * r * k) := by
    rw [← Finset.sum_product']
    symm
    refine Finset.sum_bij (fun p _ => ((p.1 : G))⁻¹ * p.2 * p.1) ?_ ?_ ?_ (fun _ _ => rfl)
    · rintro ⟨k, r⟩ hp
      simp only [Finset.mem_product, Finset.mem_univ, Finset.mem_erase, true_and, ne_eq] at hp
      simp only [Finset.mem_filter, Finset.mem_univ, true_and]
      intro hmem
      have hd := Set.disjoint_left.mp (hdisjK k k.2) hmem
      exact hd ⟨r, ⟨r.2, fun h => hp.1 (Subtype.ext h)⟩, rfl⟩
    · rintro ⟨k₁, r₁⟩ hp₁ ⟨k₂, r₂⟩ hp₂ heq
      simp only [Finset.mem_product, Finset.mem_univ, Finset.mem_erase, true_and, ne_eq] at hp₁ hp₂
      have hk : k₁ = k₂ := by
        by_contra hne
        have hne' : (k₁ : G) ≠ k₂ := fun h => hne (Subtype.ext h)
        have hd := hpair k₁.2 k₂.2 hne'
        rw [Function.onFun, Set.disjoint_left] at hd
        exact hd ⟨r₁, ⟨r₁.2, fun h => hp₁.1 (Subtype.ext h)⟩, rfl⟩
          ⟨r₂, ⟨r₂.2, fun h => hp₂.1 (Subtype.ext h)⟩, heq.symm⟩
      subst hk
      have hr : (r₁ : G) = r₂ := by
        have h := heq
        simp only at h
        exact mul_left_cancel (mul_right_cancel h)
      exact Prod.ext rfl (Subtype.ext hr)
    · intro g hg
      simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hg
      have hg' : g ∈ (K : Set G) ∪ ⋃ a ∈ K, (fun r => a⁻¹ * r * a) '' ((R : Set G) \ {1}) := by
        rw [hcover]
        trivial
      rcases hg' with hgK | hgU
      · exact absurd hgK hg
      · simp only [Set.mem_iUnion, Set.mem_image, Set.mem_sdiff, SetLike.mem_coe,
          Set.mem_singleton_iff] at hgU
        obtain ⟨a, ha, r, ⟨hr, hr1⟩, rfl⟩ := hgU
        refine ⟨(⟨a, ha⟩, ⟨r, hr⟩), ?_, rfl⟩
        simp only [Finset.mem_product, Finset.mem_univ, Finset.mem_erase, true_and, ne_eq,
          and_true]
        intro h
        exact hr1 (congrArg Subtype.val h)
  have hin : ∑ g ∈ Finset.univ.filter (fun g : G => g ∈ K), f g = ∑ k : K, f k :=
    Finset.sum_subtype _ (fun g => by simp) f
  rw [← Finset.sum_filter_add_sum_filter_not Finset.univ (fun g : G => g ∈ K), hin, hout]
  have hsumc : ∑ k : K, ∑ x : conjugate R (k : G), f x = ∑ _k : K, f 1 +
      ∑ k : K, ∑ r ∈ (Finset.univ : Finset R).erase 1, f ((k : G)⁻¹ * r * k) := by
    rw [← Finset.sum_add_distrib]
    exact Finset.sum_congr rfl fun k _ => hconj k
  rw [hsumc, Finset.sum_const, Finset.card_univ, ← Nat.card_eq_fintype_card, hf1,
    ← Nat.cast_smul_eq_nsmul F]
  abel

end CFSG.CharacterTheory.SteinbergBY
