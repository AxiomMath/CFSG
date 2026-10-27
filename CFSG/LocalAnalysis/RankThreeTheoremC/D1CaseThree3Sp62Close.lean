module

public import CFSG.LocalAnalysis.RankThreeTheoremC.D1CaseThree3Sp62RankCent
public import CFSG.LocalAnalysis.RankThreeTheoremC.D1CaseThree3Sp62CloseCore
public import CFSG.LocalAnalysis.RankThreeTheoremC.D1CaseThree3Sp62CloseFrame
public import CFSG.LocalAnalysis.RankThreeTheoremC.D1CaseThree3Sp62CloseBlock

public section

namespace CFSG.LocalAnalysis.RankThreeTheoremC

open CFSG.Open CFSG.RankThreeCoreUniqueness.Helpers CFSG.AGLEmbedding
open CFSG.RankThree.PartTwo.Sec21 (GL83StronglyEmbeddedThreeSolvable)

variable {G : Type} [Group G] [Finite G]

theorem d1Sp62Omega8SylowResidue3_closed (hGL : GL83StronglyEmbeddedThreeSolvable)
    (hSchur : KFactChevTwoSurvivorSchur) (hK1 : KFactSp62Frame) (hK2 : KFactOmega8Frame) :
    D1Sp62Omega8SylowResidue3 G := by
  intro p _ P M H R Rbar hcfg K hK huniq _ hcent _ d hp3 hd e L hL _ _ hRP
  subst hp3
  have c : Sp62CloseCtx P M H R L Rbar K d := ⟨hcfg, hK, huniq, hcent, hd, e, hL, hRP⟩
  obtain ⟨J, b, hF, hJH, h48H, hidxH, hCB⟩ := sp62Close_frame hSchur hK1 c
  have h48 := sp62Close_normBound hK2 c hF.le_P hF.elem hF.card_J
  have hCn : ((Subgroup.centralizer (J : Set G)).subgroupOf
      (Subgroup.normalizer (J : Set G))).Normal := by
    rw [← Subgroup.normalizerMonoidHom_ker]
    infer_instance
  have hCS : Subgroup.centralizer (J : Set G) ≤
      Subgroup.normalizer ((Subgroup.zpowers b : Subgroup G) : Set G) :=
    (Subgroup.centralizer_le hF.le_J).trans (Subgroup.centralizer_le_normalizer _)
  have hidx : (Subgroup.normalizer ((Subgroup.zpowers b : Subgroup G) : Set G)).relIndex
      (Subgroup.normalizer (J : Set G)) = 3 := by
    rw [relIndex_eq_of_cover3 (A := Subgroup.normalizer (J : Set G) ⊓ H) inf_le_left hCS
      (h48.trans h48H)]
    exact hidxH
  obtain ⟨W, Wb, φ, hWC, hφ, hWbs, hWbna, hWb3⟩ := sp62Close_section hK2 c hF hidx
  have := hWbs
  exact false_of_simple_quotient_inf_centralizer3 hGL hcfg.glob hcfg.ext.sylow_le hcfg.loc.core
    hF.le_P hF.elem hF.card_J hF.le_J hF.card_B (sylow_of_elemFrame3 hF h48 hidx) hCB hWC
    hWbna φ hφ hWb3

end CFSG.LocalAnalysis.RankThreeTheoremC
