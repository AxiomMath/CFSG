module

public import CFSG.ClassicalInvolution.Q3.TL4LinkZ2Defs
public import CFSG.ClassicalInvolution.Q3.TL4OddMu4Y

public section

namespace CFSG.ClassicalInvolution.Q3.TL4

open CFSG CFSG.Open CFSG.ClassicalInvolution CFSG.ClassicalInvolution.Generic
open CFSG.ClassicalInvolution.Asc77 CFSG.ClassicalInvolution.Disconnected.AschTight
open CFSG.ClassicalInvolution.Disconnected (DConnected)
open CFSG.Blueprint

@[expose] def InnerModOdd {Y : Type} [Group Y] (Λ : Subgroup Y) (x : Y) : Prop :=
  ∃ y ∈ Λ, ∀ z ∈ Λ, x * z * x⁻¹ * (y * z * y⁻¹)⁻¹ ∈ oddCoreOf Λ

section Cit3


@[expose] def TightLinkZ2L2BigR (r n : ℕ) : Prop :=
  ∀ (Y : Type) [Group Y] [Finite Y] (R : Subgroup Y) (S : Sylow 2 R) (t : Y),
    TightLargeHypR r n Y R S t → DConnected (CoreAssembly.conjClass (tightCore R)) →
      ¬ TriNbrAll R t → LinkAlphaBad R t → LinkZ2 R t →
      IsSimpleGroup ↥(genFittingFStar ↥(linkGrp R t)) →
      (genFittingFStar ↥(linkGrp R t)).index ≤ 2 →
      (∃ p f : ℕ, p.Prime ∧ p ≠ 2 ∧ Even f ∧ p ^ f ≠ 9 ∧
        LieModel (FStarQuot ↥(linkGrp R t)) .PSL 2 p f) →
        False

@[expose] def TightLinkZ2L2OuterR (r n : ℕ) : Prop :=
  ∀ (Y : Type) [Group Y] [Finite Y] (R : Subgroup Y) (S : Sylow 2 R) (t : Y),
    TightLargeHypR r n Y R S t → DConnected (CoreAssembly.conjClass (tightCore R)) →
      ¬ TriNbrAll R t → LinkZ2 R t →
      IsSimpleGroup ↥(genFittingFStar ↥(linkGrp R t)) →
      (genFittingFStar ↥(linkGrp R t)).index ≤ 2 →
      (∃ p f : ℕ, p.Prime ∧ p ≠ 2 ∧ Even f ∧ p ^ f ≠ 9 ∧
        LieModel (FStarQuot ↥(linkGrp R t)) .PSL 2 p f) →
      ∀ J ∈ omegaNbr (CoreAssembly.conjClass (tightCore R)) (tightCore R), ∀ u : Y,
        IsUniqueInvolution J u → alphaOf (Subgroup.closure ({t, u} : Set Y)) ≠ ⊥ →
      ∀ R₀ T₀ : Subgroup Y, IsSylow2In R₀ (tightCore R) →
        R₀ ≤ Subgroup.centralizer ({u} : Set Y) → IsSylow2In T₀ J →
        T₀ ≤ Subgroup.normalizer ((tightCore R : Subgroup Y) : Set Y) →
        (¬ ∃ w : Y, w * w = 1 ∧ w * t = t * w ∧ w * u = u * w ∧
          w ∉ Subgroup.closure ({t, u} : Set Y) ∧
          R₀ ≤ Subgroup.centralizer ({w} : Set Y) ∧ T₀ ≤ Subgroup.centralizer ({w} : Set Y)) →
        (∃ x : Y, IsPGroup 2 ↥(Subgroup.zpowers x) ∧ x * t = t * x ∧ x * u = u * x ∧
          (¬ InnerModOdd (linkLayer R t) x ∨
            ¬ InnerModOdd (linkLayerAt (CoreAssembly.conjClass (tightCore R)) J u) x)) →
          False

@[expose] def TightLinkZ2L2OuterAllR (r n : ℕ) : Prop :=
  ∀ (Y : Type) [Group Y] [Finite Y] (R : Subgroup Y) (S : Sylow 2 R) (t : Y),
    TightLargeHypR r n Y R S t → DConnected (CoreAssembly.conjClass (tightCore R)) →
      ¬ TriNbrAll R t → LinkZ2 R t →
      IsSimpleGroup ↥(genFittingFStar ↥(linkGrp R t)) →
      (genFittingFStar ↥(linkGrp R t)).index ≤ 2 →
      (∃ p f : ℕ, p.Prime ∧ p ≠ 2 ∧ Even f ∧ p ^ f ≠ 9 ∧
        LieModel (FStarQuot ↥(linkGrp R t)) .PSL 2 p f) →
      ∀ J ∈ omegaNbr (CoreAssembly.conjClass (tightCore R)) (tightCore R), ∀ u : Y,
        IsUniqueInvolution J u → alphaOf (Subgroup.closure ({t, u} : Set Y)) ≠ ⊥ →
      (∀ R₀ T₀ : Subgroup Y, IsSylow2In R₀ (tightCore R) →
        R₀ ≤ Subgroup.centralizer ({u} : Set Y) → IsSylow2In T₀ J →
        T₀ ≤ Subgroup.normalizer ((tightCore R : Subgroup Y) : Set Y) →
        ¬ ∃ w : Y, w * w = 1 ∧ w * t = t * w ∧ w * u = u * w ∧
          w ∉ Subgroup.closure ({t, u} : Set Y) ∧
          R₀ ≤ Subgroup.centralizer ({w} : Set Y) ∧ T₀ ≤ Subgroup.centralizer ({w} : Set Y)) →
      (∃ x : Y, IsPGroup 2 ↥(Subgroup.zpowers x) ∧ x * t = t * x ∧ x * u = u * x ∧
        (¬ InnerModOdd (linkLayer R t) x ∨
          ¬ InnerModOdd (linkLayerAt (CoreAssembly.conjClass (tightCore R)) J u) x)) →
          False

end Cit3

end CFSG.ClassicalInvolution.Q3.TL4
