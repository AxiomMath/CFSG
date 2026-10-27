module

public import CFSG.LocalAnalysis.ComponentClassification.LBalanceAssemblyCentralizers
public import CFSG.LocalAnalysis.ComponentClassification.CatalogueRelativeBMinimal

public section

namespace CFSG.ComponentClassification.LBalance

open CFSG.Open

theorem schreierSections_of_kGroup (hS : CatalogueRelativeB.CatalogueSchreier)
    {X : Type} [Group X] [Finite X] (hK : lBalanceIsKGroup X) : SchreierSections X :=
  SchreierSections.of_isKGroup (fun S _ _ _ hnc hcat => hS S hnc hcat) hK

theorem l_balance_clauses (hS : CatalogueRelativeB.CatalogueSchreier)
    (X : Type) [Group X] [Finite X] (hK : lBalanceIsKGroup X)
    (p : ℕ) (hp : p.Prime) (P : Subgroup X) (hP : IsPGroup p P) :
    lBalancePLayer p (Subgroup.normalizer (P : Set X)) ≤ lBalancePLayer p ⊤ ∧
    lBalancePLayer p (Subgroup.centralizer (P : Set X)) ≤ lBalancePLayer p ⊤ :=
  l_balance_clauses_of_schreierSections (schreierSections_of_kGroup hS hK) p hp P hP

end CFSG.ComponentClassification.LBalance
