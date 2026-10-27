module

public import CFSG.LargeExtraspecial.AS35QIxMain
public import CFSG.LargeExtraspecial.AS35QTSMain
public import CFSG.LargeExtraspecial.AS35QThAsm

public section

attribute [-instance] instAddCommGroupOfIsSimpleAddGroupOfIsNilpotent
  instCommGroupOfIsSimpleGroupOfIsNilpotent

namespace CFSG.LargeExtraspecial

namespace S14

theorem asc512ThomasBranchCore_of_indexTwo
    (h2 : Asc512ThomasIndexTwoStmt) :
    ∀ (G : Type) [Group G] [Finite G] (S : Setting G), S.SixHyp → S.Asc512Thomas →
      ∀ g₁ g₂ : G, orderOf (g₁ * S.z * g₁⁻¹ * (g₂ * S.z * g₂⁻¹)) ∈ ({1, 2, 3} : Set ℕ) := by
  intro G _ _ S hS hth g₁ g₂
  obtain ⟨T₀⟩ := AS35QTh.exists_setup asc512PbarStmt asc512FiveEightStmt h2 hS hth
  obtain ⟨T⟩ := AS35QTh.exists_lift T₀ hS
  obtain ⟨D⟩ := T.nonempty_thData asc512PbarStmt hS
  exact AS35QTS.orderOf_mem_of_iso S hS D.nonempty_mulEquiv g₁ g₂

theorem asc512ThomasBranchCore :
    ∀ (G : Type) [Group G] [Finite G] (S : Setting G), S.SixHyp → S.Asc512Thomas →
      ∀ g₁ g₂ : G, orderOf (g₁ * S.z * g₁⁻¹ * (g₂ * S.z * g₂⁻¹)) ∈ ({1, 2, 3} : Set ℕ) :=
  asc512ThomasBranchCore_of_indexTwo asc512ThomasIndexTwoStmt

end S14

end CFSG.LargeExtraspecial
