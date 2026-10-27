module

public import CFSG.LargeExtraspecial.AS35YNMain
public import CFSG.LargeExtraspecial.A2ModMain
public import CFSG.LargeExtraspecial.AS35QTSBranch
public import CFSG.Sporadic.Co2Smith.GlNJMain
public import CFSG.LargeExtraspecial.AS35QCoMain
public import CFSG.LargeExtraspecial.AS35YFMain
public import CFSG.LargeExtraspecial.AS35YRPOm
public import CFSG.LargeExtraspecial.AS35YRPSL4
public import CFSG.LargeExtraspecial.AS35YRU33
public import CFSG.LargeExtraspecial.AS35ZNEnd
public import CFSG.LargeExtraspecial.AS35ZUMain
public import CFSG.LargeExtraspecial.S14LitFischer
public import CFSG.Sporadic.Co2Smith.GlCosetMain
public import CFSG.Sporadic.Co2Smith.GlU62Final
public import CFSG.Timmesfeld.ARSInputThm

public section

namespace CFSG.LargeExtraspecial.S14

theorem aschbacherFiveTwelveCoreStmt_of_piecesCore
    (hD : Asc512DichotomyStmt)
    (hI : ∀ (G : Type) [Group G] [Finite G] (S : Setting G), S.SixHyp → S.Asc512Standing →
      S.Asc512Unitary ∨ S.Asc512SpSix)
    (hU : Asc512UnitaryBranch) (hCo : Asc512Co2Branch)
    (hG1 : CFSG.Sporadic.Co2Smith.SmithG1Input)
    (hT : ∀ (G : Type) [Group G] [Finite G] (S : Setting G), S.SixHyp → S.Asc512Thomas →
      ∀ g₁ g₂ : G, orderOf (g₁ * S.z * g₁⁻¹ * (g₂ * S.z * g₂⁻¹)) ∈ ({1, 2, 3} : Set ℕ)) :
    AschbacherFiveTwelveCoreStmt := by
  intro G _ _ S hS
  rcases hD G S hS with hst | hth
  · rcases hI G S hS hst with hu | hsp
    · exact Or.inr (Or.inr (hU G S hS hst hu))
    · exact Or.inl ⟨hsp.1, hCo hG1 G S hS hst hsp⟩
  · exact Or.inr (Or.inl ⟨hth.1, hT G S hS hth⟩)

theorem aschbacherFiveTwelveCoreStmt_of_fixFree (hfix : Asc512FixFreeStmt)
    (hSU : SUModuleEndInput) : AschbacherFiveTwelveCoreStmt := by
  have hND := asc512InspNondeg_ofN DW.dw2FieldInput s12PSLModuleInputN s12SpModuleInputN
    s12OmegaModuleInputN s12ExcModuleInputN asc512FiveTwelveSevenStmt hfix
    asc512PSL4WidthThreeStmt asc512POmegaNatStmt asc512U33ModuleInput
  have hDg := asc512InspFor_degenerate asc512FiveEightStmt asc512PbarStmt
  have hCl := asc512ClassifyStmt_of_inputs CFSG.Timmesfeld.arsInput S12Tri.fischerTrialityInput
      s12FischerStatement asc512PbarStmt asc512FiveEightStmt
  refine aschbacherFiveTwelveCoreStmt_of_piecesCore
    (asc512DichotomyStmt_of asc512PbarStmt asc512FiveEightStmt) ?_
    (asc512UnitaryBranch_of asc512SymStmt asc512PbarStmt (suModuleInput_of_endInput hSU))
    (asc512Co2Branch asc512SymStmt asc512PbarStmt)
    (CFSG.Sporadic.Co2Smith.smithG1Input_of_U62 CFSG.Sporadic.Co2Smith.smithC0Input
      CFSG.Sporadic.Co2Smith.smithU62Input_holds)
    asc512ThomasBranchCore
  intro G _ _ S hS hst
  rcases hCl G S hS hst with h | h
  · exact hND G S hS hst h
  · exact hDg G S hS hst h

end CFSG.LargeExtraspecial.S14
