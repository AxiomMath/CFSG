module

public import CFSG.LocalAnalysis.RankFourTheoremC.InvariantTwo.KFacts.I294K29E8FiveFourData
public import CFSG.HardMathSupport.Timmesfeld.CrossChar.TwCompStabilizer
public import CFSG.LocalAnalysis.StandardType.GGE8TwoFiveFinite

public section

namespace CFSG.LocalAnalysis.RankFourTheoremC.E8FiveFour

open CFSG.Blueprint.Chevalley CFSG.HardMathSupport.Timmesfeld.Steinberg
  CFSG.HardMathSupport.Timmesfeld.CrossChar

theorem kacCands_map_toNat :
    CFSG.StandardType.FieldFiveE8.E8TwoFiveFin.kacCands.map (fun l => l.map Int.toNat) =
      kacRepsN := by
  decide +kernel

theorem kacRepsN_cover
    (b : Fin Tag.E8.rank → ZMod 5) :
    ∃ r ∈ kacRepsN, ∃ σ : List (Fin Tag.E8.rank), pAct σ (vecP (τ := .E8) 5 r) = b := by
  obtain ⟨μ, hμ, σ, hσ⟩ := kacE8.exists_pAct_isNormal (p := 5) (by norm_num) b
  have hmem := CFSG.StandardType.FieldFiveE8.E8TwoFiveFin.normal_mem_kacCands μ hμ
  refine ⟨(List.ofFn μ).map Int.toNat, ?_, σ, ?_⟩
  · rw [← kacCands_map_toNat]
    exact List.mem_map_of_mem hmem
  · convert hσ using 2
    funext j
    have h0 : 0 ≤ μ j := hμ.1 j
    have hg : ((List.ofFn μ).map Int.toNat).getD j 0 = (μ j).toNat := by
      simp [List.getD_eq_getElem?_getD]
    simp only [vecP, hg]
    rw [← Int.cast_natCast, Int.toNat_of_nonneg h0]

end CFSG.LocalAnalysis.RankFourTheoremC.E8FiveFour
