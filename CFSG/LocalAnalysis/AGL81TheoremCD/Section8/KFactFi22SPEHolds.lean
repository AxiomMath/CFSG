module

public import CFSG.LocalAnalysis.AGL81TheoremCD.Section8.Defs
public import CFSG.LocalAnalysis.AGLEmbedding.KFactProofs.Fi22GuestRank
import CFSG.HardMathSupport.Solomon.Coordinator.B0TSylow
import CFSG.RankThree.PartOne.CTP.StrongPGlue

public section

namespace CFSG.LocalAnalysis.AGL81TheoremCD.Section8

theorem kFactFi22SPEThreeRank : KFactFi22SPEThreeRank := by
  intro X _ _ _ hK N hN
  haveI : Fact (Nat.Prime 5) := ⟨by norm_num⟩
  set K : Subgroup X := CFSG.generalizedFitting X
  haveI : K.Normal := (CFSG.LocalCores.generalized_fitting_characteristic (G := X)).2
  obtain ⟨P, hP, hPN⟩ := hN.exists_isSylowOf_le
  let S := hP.2.1.toSylow (by simpa [Subgroup.relIndex_top_right] using hP.2.2)
  obtain ⟨T, hT⟩ := CFSG.HardMathSupport.Solomon.Coordinator.exists_sylow_inf_normal S K
  obtain ⟨E, hEΓ, hEa, hEc⟩ := CFSG.AGLEmbedding.kFactFi22GuestRank ↥K hK T
  have hΓ : (CFSG.Open.GLBCore 5 1 (T : Subgroup K)).map K.subtype ≤ N := by
    rw [Subgroup.map_le_iff_le_comap]
    refine sSup_le ?_
    rintro _ ⟨Q, hQT, hQ1, rfl⟩
    have hQne : Q ≠ ⊥ := by
      rintro rfl
      have h0 : CFSG.Open.pRank 5 (⊥ : Subgroup K) ≤ 0 :=
        CFSG.SectionRank.pRank_le (by norm_num) fun F hF _ => by
          rw [le_bot_iff.mp hF, Subgroup.card_bot]
          simp
      exact absurd (hQ1.trans h0) (by norm_num)
    have hUP : Q.map K.subtype ≤ P := ((Subgroup.map_mono hQT).trans hT.le).trans inf_le_left
    have hUne : Q.map K.subtype ≠ ⊥ := by
      rwa [Ne, Subgroup.map_eq_bot_iff_of_injective _ K.subtype_injective]
    intro k hk
    exact hN.normalizer_le hUne ((T.isPGroup'.to_le hQT).map K.subtype) (hUP.trans hPN)
      (Subgroup.le_normalizer_map K.subtype ⟨k, hk, rfl⟩)
  have h4 : 4 ≤ CFSG.Open.pRank 3 N :=
    CFSG.SectionRank.le_pRank (by norm_num) ((Subgroup.map_mono hEΓ).trans hΓ)
      (CFSG.SectionRank.isElemAbelian_map hEa K.subtype)
      (by rw [Subgroup.card_map_of_injective K.subtype_injective, hEc])
  omega

end CFSG.LocalAnalysis.AGL81TheoremCD.Section8
