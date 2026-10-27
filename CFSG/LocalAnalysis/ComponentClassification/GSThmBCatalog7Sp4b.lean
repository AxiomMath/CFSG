module

public import CFSG.Adapters.ProjectiveSpecialLinear
public import CFSG.Assembly.ComponentTypeDefs
public import CFSG.Blueprint.Catalog
public import CFSG.Foundations.Basic
public import CFSG.LocalAnalysis.ComponentClassification.GSThmB7Basic

public section

namespace CFSG.ComponentClassification.GSThmB

open CFSG Subgroup

@[expose] def CFSp4D : Prop :=
  ∀ (Y : Type) [Group Y] [Finite Y] (p f : ℕ), p.Prime → p ≠ 2 → 1 ≤ f →
    Blueprint.LieModel Y .PSp 2 p f → ∀ t : Y, orderOf t = 2 → ∀ M : Subgroup Y,
      M ≤ centralizer ({t} : Set Y) → IsPComponent 2 (M.subgroupOf (centralizer ({t} : Set Y))) →
      center M = ⊥ → ∀ R : Subgroup Y, Seven.IsSylowIn R (centralizer ({t} : Set Y)) →
        ∃ D₁ : Subgroup Y, D₁ ≤ R ∧ D₁ ≤ centralizer (M : Set Y) ∧
          ∃ T : Sylow 2 ↥M, Nonempty (↥D₁ ≃* ↥(T : Subgroup ↥M))

end CFSG.ComponentClassification.GSThmB
