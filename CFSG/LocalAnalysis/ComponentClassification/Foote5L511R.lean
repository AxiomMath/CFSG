module

public import CFSG.LocalAnalysis.ComponentClassification.Foote5L511Q
public import CFSG.LocalAnalysis.ComponentClassification.Foote5L511E
public import CFSG.LocalAnalysis.ComponentClassification.FooteLitFCC

public noncomputable section

namespace CFSG.ComponentClassification.Foote5

open CFSG Subgroup CFSG.ComponentClassification.UnbalancedLayer
  CFSG.ComponentClassification.UnbalancedCorr CFSG.ComponentClassification.FooteLit
  CFSG.ABGLocalTools GorensteinWalter

variable {G : Type} [Group G] [Finite G]

namespace Sec5

variable {L₀ L Q S T : Subgroup G} {z t : G} (h : Sec5 G L₀ L Q S T z t)
  {𝕊 : Type} [Group 𝕊] [Finite 𝕊] (ε : L ⧸ pPrimeCore 2 L ≃* 𝕊)
  {Lin : Subgroup (MulAut 𝕊)}
include h

include ε in
theorem conjugate_R_le_Q_of_lemmas (hMW : MacWilliamsStatement) (hGH : GH74.GH74Statement)
    (hKG : Foote5KnownGroups) (hAut : Foote5AutStructure) (hDiag : Foote5DiagonalNotInQ)
    (hKF : Foote5FieldCentralizerC) (h𝕊 : FooteSimpleType 𝕊) (hD : Foote5AutData 𝕊 Lin)
    (hna : ∃ a ∈ S ⊓ L, ∃ b ∈ S ⊓ L, a * b ≠ b * a) (hQ : 4 < Nat.card Q)
    (hCt : ∀ y ∈ T, y * t = t * y → y ∈ S) (hT2 : Nat.card T = 2 * Nat.card S) {s : G}
    (hsT : s ∈ T) (hsS : s ∉ S) (hz : z = s⁻¹ * t * s) : conjugate (S ⊓ L) s ≤ Q := by
  by_contra hnot
  obtain ⟨r, hr, hr2, hrlin⟩ := h.exists_field_involution_of_not_le_Q ε hDiag hAut hD hna hQ
    hCt hT2 hsT hsS hnot
  obtain ⟨E, hES, hTE, hEsq, hE8, htE, hzE⟩ := h.exists_normal_e8_zt ε hMW hGH hKG hD hna hCt
    hT2 hsT hsS
  rw [← hz] at hzE
  exact h.false_of_field_involution ε hKF h𝕊 hD hna hQ hT2 hsT hsS hz hr hr2 hrlin hES hTE hEsq
    hE8 htE hzE

theorem conjugate_R_le_Q
    (hGH : GH74.GH74Statement) (hKG : Foote5KnownGroups)
    (hB4 : GoldschmidtCorB4) (hAut : Foote5AutStructure) (hMW : MacWilliamsStatement)
    (hFC : Foote5FieldCentralizer) (hDiag : Foote5DiagonalNotInQ)
    {s : G} (hsT : s ∈ T) (hsS : s ∉ S) : conjugate (S ⊓ L) s ≤ Q := by
  obtain ⟨h', hRR⟩ := h.repoint_conj_t hGH hKG hB4 hAut hMW hFC hsT hsS
  obtain ⟨Lin, hD⟩ := h'.exists_autData hAut
  obtain ⟨ε'⟩ := h'.quotient_simple.2
  have hST := h.not_isSylowOf_top hGH hKG hB4 hAut
  have hna := h.nonabelian_R_of_not_sylow hGH hKG hAut hMW hST
  rw [← hRR] at hna
  have h1 := h'.conjugate_R_le_Q_of_lemmas ε' hMW hGH hKG hAut hDiag foote5FieldCentralizerC_holds
    h'.sec4.footeFamilyType hD hna (h.four_lt_card_Q hGH hKG hB4 hAut hMW hFC)
    (fun y hyT hyt => h.mem_S_of_commute_t_of_inputs hGH hKG hB4 hAut hMW hFC hyT hyt)
    (h.card_T_eq_two_mul hGH hKG hB4 hAut hMW hFC) hsT hsS rfl
  rwa [hRR] at h1

end Sec5

end CFSG.ComponentClassification.Foote5
