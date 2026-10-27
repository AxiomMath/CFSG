module

public import CFSG.LocalAnalysis.ComponentClassification.Foote5L513C
public import CFSG.LocalAnalysis.ComponentClassification.Foote5L512J
public import CFSG.LocalAnalysis.ComponentClassification.FooteLitL24V

public noncomputable section

namespace CFSG.ComponentClassification.Foote5

open CFSG Subgroup CFSG.ComponentClassification.UnbalancedLayer
  CFSG.ComponentClassification.UnbalancedCorr CFSG.ComponentClassification.FooteLit
  CFSG.ABGLocalTools GorensteinWalter

variable {G : Type} [Group G] [Finite G]

namespace Sec5

variable {L₀ L Q S T : Subgroup G} {z t : G} (h : Sec5 G L₀ L Q S T z t)
include h

theorem lemma513
    (hGH : GH74.GH74Statement)
    (hKG : Foote5KnownGroups) (hB4 : GoldschmidtCorB4) (hAut : Foote5AutStructure)
    (hMW : MacWilliamsStatement) (hDiag : Foote5DiagonalNotInQ)
    {𝕊 : Type} [Group 𝕊] [Finite 𝕊] (ε : L ⧸ pPrimeCore 2 L ≃* 𝕊)
    {Lin : Subgroup (MulAut 𝕊)} (hD : Foote5AutData 𝕊 Lin) {s : G} (hsT : s ∈ T)
    (hsS : s ∉ S) (hz : z = s⁻¹ * t * s) :
    ∀ g : G, g⁻¹ * z * g ∈ T → g⁻¹ * z * g ∈ S ⊓ L ∨ g⁻¹ * z * g ∈ conjugate (S ⊓ L) s ∨
      (actG L ε (g⁻¹ * z * g) ∈ Lin ∧ actG L ε (g⁻¹ * z * g) ∉ innAut5 𝕊) := by
  have hFC := Sol78.foote5FieldCentralizer
  have hST := h.not_isSylowOf_top hGH hKG hB4 hAut
  exact h.lemma513_of_lemmas ε hD (h.nonabelian_R_of_not_sylow hGH hKG hAut hMW hST)
    (h.card_T_eq_two_mul hGH hKG hB4 hAut hMW hFC) hsT hsS hz
    (h.conjugate_R_le_Q hGH hKG hB4 hAut hMW hFC hDiag hsT hsS)
    (fun g' hg' => h.lemma512 hGH hKG hB4 hAut hMW hDiag foote5Lemma24iiV_holds hsT hsS hz
      hg')

end Sec5

end CFSG.ComponentClassification.Foote5
