module

public import CFSG.Foundations.Basic
import CFSG.Quasithin.Background.G8Core

public section

namespace CFSG.LocalCores

open Subgroup

variable {G : Type*} [Group G]

theorem le_centralizer_generalizedFitting {U : Subgroup G}
    (hF : U ≤ centralizer (CFSG.fittingSubgroup G : Set G))
    (hE : ∀ C : Subgroup G, CFSG.IsComponent C → U ≤ centralizer (C : Set G)) :
    U ≤ centralizer (CFSG.generalizedFitting G : Set G) := by
  rw [Subgroup.le_centralizer_iff]
  rw [CFSG.generalizedFitting.eq_sup, CFSG.layer.eq_sSup]
  refine sup_le (Subgroup.le_centralizer_iff.mp hF) (sSup_le ?_)
  intro C hC
  exact Subgroup.le_centralizer_iff.mp (hE C hC)

theorem eq_bot_of_isPGroup_of_le_centralizer_generalizedFitting [Finite G] {p : ℕ}
    [Fact p.Prime] (hp : CFSG.pCore p G = ⊥) {U : Subgroup G} (hU : IsPGroup p U)
    (hc : U ≤ centralizer (CFSG.generalizedFitting G : Set G)) : U = ⊥ := by
  have hB : U ≤ CFSG.fittingSubgroup G := by
    refine hc.trans ?_
    rw [CFSG.generalizedFitting_eq_componentClassification]
    exact CFSG.ComponentClassification.GeneralizedFitting.centralizer_le_fitting G
  have hUp : U ≤ CFSG.pCore p G :=
    CFSG.Quasithin.G8.le_pCore_of_le_fitting hB hU
  rw [hp] at hUp
  exact le_bot_iff.mp hUp

end CFSG.LocalCores
