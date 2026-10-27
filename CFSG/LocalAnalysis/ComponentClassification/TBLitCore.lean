module

public import CFSG.LocalAnalysis.ComponentClassification.TBLitCaseA

public noncomputable section

namespace CFSG.ComponentClassification.TBLit

open CFSG Subgroup CFSG.Blueprint

variable {X : Type} [Group X] [Finite X]

theorem CoreConfig.false (hI : TBInputs) (hX : TBSetting X)
    {a b γ : X} {S E : Subgroup X} (hC : CoreConfig a b γ S E) : False := by
  obtain ⟨M, hM, hMc, hSK, hSKc, haM, hEM, hanM, henM⟩ := core_pumpUp hI hX hC
  by_cases hne : M = conjugate M b
  · obtain ⟨δ₁, δ₂, N₁, N₂, E', hS⟩ := caseA_star hI hX hC hM hMc hSK hSKc haM hEM hanM henM hne
    exact hS.false hI hX
  · obtain ⟨δ₁, δ₂, N₁, N₂, E', hS⟩ := caseB_star hI hX hC hM hMc hSK hSKc haM hEM hanM henM hne
    exact hS.false hI hX

end CFSG.ComponentClassification.TBLit
