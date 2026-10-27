module

public import CFSG.LocalAnalysis.ProperTwoGeneratedCore.TheoremC.Config

public section

namespace CFSG.ProperTwoGeneratedCore.TheoremC

open CFSG.Open CFSG.ProperTwoGeneratedCore.Assembly

@[expose] def TheoremCStatement : Prop :=
  ∀ (X : Type) [Group X] [Finite X] (Y : Subgroup X) (u z : X), CoreConfig Y u z →
    ∃ J : Subgroup X, CFSG.IsComponent J ∧ u ∉ J

@[expose] def TheoremCBelow (n : ℕ) : Prop :=
  ∀ (X : Type) [Group X] [Finite X], Nat.card X < n →
    ∀ (Y : Subgroup X) (u z : X), CoreConfig Y u z →
      ∃ J : Subgroup X, CFSG.IsComponent J ∧ u ∉ J

variable {X : Type} [Group X] [Finite X]

abbrev componentImage (Y J : Subgroup X) : Subgroup (↥J ⧸ Subgroup.center ↥J) :=
  (Y.subgroupOf J).map (QuotientGroup.mk' (Subgroup.center ↥J))

structure HighRankCaseTwo (Y : Subgroup X) (u z : X) (P : Sylow 2 X) (J : Subgroup X) :
    Prop where
  sylow_le : (P : Subgroup X) ≤ Y
  core_le : properTwoGenCoreGamma (P : Subgroup X) 2 ≤ Y
  lever_mem : z ∈ (P : Subgroup X)
  lever_comm : ∀ p ∈ (P : Subgroup X), Commute p z
  component : CFSG.IsComponent J
  normal : J.Normal
  mem : u ∈ J
  rank : 2 ≤ CFSG.Open.pRank 2 J
  not_le : ¬ J ≤ Y
  lever : z ∈ J ∨ (z ∉ J ∧ ∃ y ∈ J ⊓ Y, ∃ t ∈ (P : Subgroup X) ⊓ J, orderOf t = 2 ∧
    (∃ c ∈ J, ¬ Commute c t) ∧ y⁻¹ * z * y = z * t)

@[expose] def CaseTwoReduction : Prop :=
  ∀ (X : Type) [Group X] [Finite X] (Y : Subgroup X) (u z : X), CoreConfig Y u z →
    (∀ J : Subgroup X, CFSG.IsComponent J → u ∈ J) →
      ∃ (P : Sylow 2 X) (J : Subgroup X), HighRankCaseTwo Y u z P J

@[expose] def HighRankStrongEmbedding : Prop :=
  ∀ (X : Type) [Group X] [Finite X] (Y : Subgroup X) (u z : X) (P : Sylow 2 X)
    (J : Subgroup X), TheoremCBelow (Nat.card X) → CoreConfig Y u z →
      HighRankCaseTwo Y u z P J → fusionStronglyEmbedded (componentImage Y J)

@[expose] def BenderCoverExclusion : Prop :=
  ∀ (X : Type) [Group X] [Finite X] (Y : Subgroup X) (u z : X) (P : Sylow 2 X)
    (J : Subgroup X), CoreConfig Y u z → HighRankCaseTwo Y u z P J →
      ¬ fusionStronglyEmbedded (componentImage Y J)

@[expose] def CaseOneInvolutions : Prop :=
  ∀ (X : Type) [Group X] [Finite X] (Y : Subgroup X) (u z : X), CoreConfig Y u z →
    ∀ J : Subgroup X, CFSG.IsComponent J → u ∉ J →
      IsSimpleGroup J ∧ J.Normal ∧ ∀ t : X, orderOf t = 2 → t ∈ J ∨ u * t ∈ J

@[expose] def QuotientLocalEmbedding : Prop :=
  ∀ (X : Type) [Group X] [Finite X] (Y : Subgroup X) (u z : X),
    TheoremCBelow (Nat.card X) → CoreConfig Y u z →
      CFSG.ShultStronglyClosedTI.InvolutionPointLocalEmbedding
        (Y.map (QuotientGroup.mk' (CFSG.Open.pCore 2 X)))
        (QuotientGroup.mk' (CFSG.Open.pCore 2 X) z)

theorem theoremC_of_parts (h₁ : CaseTwoReduction) (h₂ : HighRankStrongEmbedding)
    (h₃ : BenderCoverExclusion) : TheoremCStatement := by
  suffices key : ∀ n : ℕ, TheoremCBelow n by
    intro X _ _ Y u z hc
    exact key (Nat.card X + 1) X (Nat.lt_succ_self _) Y u z hc
  intro n
  induction n with
  | zero => intro X _ _ hX; omega
  | succ n IH =>
    intro X _ _ hX Y u z hc
    by_contra hII
    push Not at hII
    obtain ⟨P, J, hJ⟩ := h₁ X Y u z hc hII
    have hbelow : TheoremCBelow (Nat.card X) := fun X' _ _ hX' =>
      IH X' (lt_of_lt_of_le hX' (Nat.lt_succ_iff.mp hX))
    exact h₃ X Y u z P J hc hJ (h₂ X Y u z P J hbelow hc hJ)

end CFSG.ProperTwoGeneratedCore.TheoremC
