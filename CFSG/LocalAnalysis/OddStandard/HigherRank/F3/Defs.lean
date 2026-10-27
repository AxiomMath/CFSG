module

public import CFSG.LocalAnalysis.ComponentClassification.HarrisLitTheorem1

public section

namespace CFSG.OddStandard.HigherRank.F3

open Subgroup CFSG CFSG.Open CFSG.ComponentClassification.HarrisLit

@[expose] def ClassBShape (J : Type) [Group J] : Prop :=
  ∃ (τ : StatedLieTag) (n : ℕ), CFSG.Blueprint.LieModel (J ⧸ Open.fusionZStar J) τ n 3 1 ∧
    ((τ = .PSL ∧ (n = 4 ∨ n = 6)) ∨ (τ = .PSU ∧ (n = 4 ∨ n = 6)) ∨ (τ = .PSp ∧ 2 ≤ n) ∨
      (τ = .POmegaPlus ∧ (n = 4 ∨ n = 6)) ∨ τ = .E7)

@[expose] def PartialCentre (J : Type) [Group J] : Prop :=
  ordProj[2] (Nat.card ↥(Open.fusionZStar J)) <
    ordProj[2] (Nat.card (Open.griessHopfMultiplier (J ⧸ Open.fusionZStar J)))

structure IsClassBMember (L : Type) [Group L] (J : Subgroup L) (u : L) : Prop where
  orderOf_eq_two : orderOf u = 2
  mem : u ∈ J
  not_mem_center : u ∉ center L
  perfect : Group.IsPerfect ↥J
  subnormal : IsSubnormal J (centralizer ({u} : Set L))
  mtype : IsMTypeSchur 3 ↥J

@[expose] def HasClassBMember (L : Type) [Group L] : Prop :=
  ∃ (J : Subgroup L) (u : L), IsClassBMember L J u ∧ ClassBShape ↥J

@[expose] def HasFullClassBMember (L : Type) [Group L] : Prop :=
  ∃ (J : Subgroup L) (u : L), IsClassBMember L J u ∧ ClassBShape ↥J ∧ ¬ PartialCentre ↥J

@[expose] def Theorem3Full : Prop :=
  ∀ (G : Type) [Group G] [Finite G] [IsSimpleGroup G], (∃ a b : G, a * b ≠ b * a) →
    Assembly.KProper Blueprint.Catalog G → ¬ Blueprint.Catalog G →
    ∀ W : Subgroup G, (∀ a ∈ W, a * a = 1) → Nat.card ↥W = 4 →
    ∀ J : Subgroup G, IsTwoComponentIn J (centralizer (W : Set G)) → IsMTypeSchur 3 ↥J →
      ClassBShape ↥J → ¬ PartialCentre ↥J → J ⊓ W ≠ ⊥ → ∀ w ∈ J ⊓ W, w ≠ 1 →
        IsTwoComponentIn (ComponentClassification.GSThmB.conjClosure J
          (ComponentClassification.GSThmB.layerIn (centralizer {w})))
          (centralizer {w})

theorem HasFullClassBMember.hasClassBMember {L : Type} [Group L] (h : HasFullClassBMember L) :
    HasClassBMember L := by
  obtain ⟨J, u, hJ, hs, -⟩ := h
  exact ⟨J, u, hJ, hs⟩

end CFSG.OddStandard.HigherRank.F3
