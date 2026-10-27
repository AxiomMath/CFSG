module

public import CFSG.LocalAnalysis.ComponentClassification.Foote5L512I
public import CFSG.LocalAnalysis.ComponentClassification.Sol78FooteFC

public noncomputable section

namespace CFSG.ComponentClassification.Foote5

open CFSG Subgroup CFSG.ComponentClassification.UnbalancedLayer
  CFSG.ComponentClassification.UnbalancedCorr CFSG.ComponentClassification.FooteLit
  CFSG.ABGLocalTools GorensteinWalter

variable {G : Type} [Group G] [Finite G]

namespace Sec5

variable {L₀ L Q S T : Subgroup G} {z t : G} (h : Sec5 G L₀ L Q S T z t)
include h

theorem lemma512
    (hGH : GH74.GH74Statement)
    (hKG : Foote5KnownGroups) (hB4 : GoldschmidtCorB4) (hAut : Foote5AutStructure)
    (hMW : MacWilliamsStatement) (hDiag : Foote5DiagonalNotInQ)
    (hL24 : Foote5Lemma24iiV) {s : G} (hsT : s ∈ T) (hsS : s ∉ S) (hz : z = s⁻¹ * t * s) {g : G}
    (hgT : g⁻¹ * z * g ∈ T) : g⁻¹ * z * g ∈ S := by
  have hFC := Sol78.foote5FieldCentralizer
  obtain ⟨Lin, hD⟩ := h.exists_autData hAut
  obtain ⟨ε⟩ := h.quotient_simple.2
  have hST := h.not_isSylowOf_top hGH hKG hB4 hAut
  have hna := h.nonabelian_R_of_not_sylow hGH hKG hAut hMW hST
  have hQ4 := h.four_lt_card_Q hGH hKG hB4 hAut hMW hFC
  have hT2 := h.card_T_eq_two_mul hGH hKG hB4 hAut hMW hFC
  have hRsQ := h.conjugate_R_le_Q hGH hKG hB4 hAut hMW hFC hDiag hsT hsS
  have hQd := dsdData_of_dihedral_or_semidihedral_L512
    (h.lemma511iii_of_lemmas ε foote5TwoSubgroupOverInner_holds h.sec4.footeFamilyType hD hna hQ4
      hT2 hsT hsS hRsQ).1 hQ4
  exact h.conj_z_mem_S_of_lemmas ε hD hL24 h.sec4.footeFamilyType hQd hna hT2 hsT hsS hz hRsQ
    hgT

end Sec5

end CFSG.ComponentClassification.Foote5
