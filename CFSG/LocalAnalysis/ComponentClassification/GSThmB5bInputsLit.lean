module

public import CFSG.LocalAnalysis.ComponentClassification.GSThmB5bTypes

public section

namespace CFSG.ComponentClassification.GSThmB

open CFSG Subgroup CFSG.ComponentClassification.UnbalancedLayer

@[expose] def SolomonTwoSubgroupAltInput : Prop :=
  ∀ (X : Type) [Group X] [Finite X] [IsSimpleGroup X], (∃ a b : X, a * b ≠ b * a) →
    Assembly.KProper Blueprint.Catalog X →
    (∃ z : X, orderOf z = 2 ∧ oddCore (centralizer ({z} : Set X)) ≠ ⊥) →
    ¬ OutcomeLocal.UOutcome X →
    ∀ B₁ M : Subgroup X, IsPGroup 2 B₁ → M ≤ centralizer (B₁ : Set X) →
      IsPComponent 2 (M.subgroupOf (centralizer (B₁ : Set X))) →
      ¬ (Nonempty (ZStarBar M ≃* alternatingGroup (Fin 9)) ∨
        Nonempty (OddBar M ≃* alternatingGroup (Fin 11)))

@[expose] def HarrisSolomonA7Input : Prop :=
  ∀ (G : Type) [Group G] [Finite G], Assembly.KProper Blueprint.Catalog G →
    IsSimpleGroup ↥(generalizedFitting G) →
    ∀ t : G, orderOf t = 2 → ∀ L : Subgroup G, L ≤ centralizer ({t} : Set G) →
      IsPComponent 2 (L.subgroupOf (centralizer ({t} : Set G))) →
      Nonempty (OddBar L ≃* alternatingGroup (Fin 7)) →
      (∀ R : Sylow 2 ↥(coreActionKernel L), IsCyclic (R : Subgroup ↥(coreActionKernel L))) →
      Nonempty (↥(generalizedFitting G) ≃* alternatingGroup (Fin 9)) ∨
        Nonempty (↥(generalizedFitting G) ≃* Blueprint.NativeSporadic.He)

@[expose] def GenFittingSimpleStatement : Prop :=
  ∀ (H : Type) [Group H] [Finite H] (_ : Hyp59 H), IsSimpleGroup ↥(generalizedFitting H)

end CFSG.ComponentClassification.GSThmB
