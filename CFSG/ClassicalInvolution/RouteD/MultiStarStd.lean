module

public import CFSG.ClassicalInvolution.RouteD.MultiStarWeak
public import CFSG.ClassicalInvolution.RouteD.MultiD4

public section

namespace CFSG.ClassicalInvolution.RouteD

open CFSG.Open CFSG.ClassicalInvolution.Generic CFSG.ClassicalInvolution.Generic.CoreAssembly
open CFSG.ClassicalInvolution.WeakCT (LinearBlockStandardPair)

variable {p f : ℕ} [Fact p.Prime]

@[expose] def WeakStarImpossible (p f : ℕ) [Fact p.Prime] : Prop :=
  ∀ (G : Type) [Group G] [Finite G] [IsSimpleGroup G], (∃ x y : G, x * y ≠ y * x) →
    ∀ (K : Subgroup G) (z : G), RouteDSetup p f K z →
      ∀ D : LieSystemData p f (locQuot (conjClass K) z) (locFamily (conjClass K) z),
        ∀ (i₁ i₂ : Fin D.card) (a₁ a₂ q : Subgroup G), i₁ ≠ i₂ → ¬ IsA1Comp D i₁ →
          ¬ IsA1Comp D i₂ → a₁ ∈ Gaps.compMembers (conjClass K) z D i₁ →
          a₂ ∈ Gaps.compMembers (conjClass K) z D i₂ → q ∈ conjClass K → Commutes K a₁ →
          Commutes K a₂ → Commutes a₁ a₂ → ¬ Commutes q K → ¬ Commutes q a₁ →
          ¬ Commutes q a₂ → False

theorem multiPiece_of_weakStarImpossible (h : WeakStarImpossible p f) : MultiPiece p f := by
  intro G _ _ _ hnab K z hset hshape
  obtain ⟨D, hD⟩ := hshape
  obtain ⟨i₁, i₂, a₁, a₂, q, hne, hn₁, hn₂, ha₁, ha₂, hq, hKa₁, hKa₂, ha₁a₂, hqK, hqa₁,
    hqa₂⟩ := exists_weak_star hnab hset D hD
  exact (h G hnab K z hset D i₁ i₂ a₁ a₂ q hne hn₁ hn₂ ha₁ ha₂ hq hKa₁ hKa₂ ha₁a₂ hqK hqa₁
    hqa₂).elim

@[expose] def StarImprovement (p f : ℕ) [Fact p.Prime] : Prop :=
  ∀ (G : Type) [Group G] [Finite G] [IsSimpleGroup G], (∃ x y : G, x * y ≠ y * x) →
    ∀ (K : Subgroup G) (z : G), RouteDSetup p f K z →
      ∀ D : LieSystemData p f (locQuot (conjClass K) z) (locFamily (conjClass K) z),
        ∀ (i₁ i₂ : Fin D.card) (a₁ a₂ q : Subgroup G), i₁ ≠ i₂ → ¬ IsA1Comp D i₁ →
          ¬ IsA1Comp D i₂ → a₁ ∈ Gaps.compMembers (conjClass K) z D i₁ →
          a₂ ∈ Gaps.compMembers (conjClass K) z D i₂ → q ∈ conjClass K → Commutes K a₁ →
          Commutes K a₂ → Commutes a₁ a₂ → ¬ Commutes q K → ¬ Commutes q a₁ →
          ¬ Commutes q a₂ →
          ∃ (i₁' i₂' : Fin D.card) (a₁' a₂' β : Subgroup G), i₁' ≠ i₂' ∧ ¬ IsA1Comp D i₁' ∧
            ¬ IsA1Comp D i₂' ∧ a₁' ∈ Gaps.compMembers (conjClass K) z D i₁' ∧
            a₂' ∈ Gaps.compMembers (conjClass K) z D i₂' ∧ β ∈ conjClass K ∧
            (∃ W, LinearBlockStandardPair (GaloisField p f) W K β) ∧
            (∃ W, LinearBlockStandardPair (GaloisField p f) W a₁' β) ∧
            (∃ W, LinearBlockStandardPair (GaloisField p f) W a₂' β)

theorem multiStar_of_improvement (h : StarImprovement p f) : MultiStar p f := by
  intro G _ _ _ hnab K z hset D hD
  obtain ⟨i₁, i₂, a₁, a₂, q, hne, hn₁, hn₂, ha₁, ha₂, hq, hKa₁, hKa₂, ha₁a₂, hqK, hqa₁,
    hqa₂⟩ := exists_weak_star hnab hset D hD
  obtain ⟨i₁', i₂', a₁', a₂', β, hne', hn₁', hn₂', ha₁', ha₂', hβ, hKβ, ha₁β, ha₂β⟩ :=
    h G hnab K z hset D i₁ i₂ a₁ a₂ q hne hn₁ hn₂ ha₁ ha₂ hq hKa₁ hKa₂ ha₁a₂ hqK hqa₁ hqa₂
  exact ⟨i₁', i₂', a₁', a₂', β, hne', hn₁', hn₂', ha₁', ha₂', hβ, hKβ, ha₁β, ha₂β⟩

theorem multiPiece_of_improvement (h : StarImprovement p f) : MultiPiece p f :=
  multiPiece_of_multiStar (multiStar_of_improvement h)

end CFSG.ClassicalInvolution.RouteD
