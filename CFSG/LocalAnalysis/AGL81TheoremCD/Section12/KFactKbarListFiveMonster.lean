module

public import CFSG.LocalAnalysis.AGL81TheoremCD.Section12.KFactKbarListFiveTransport
import CFSG.LocalAnalysis.RankThreeTheoremC.KFactProofs.Stroth.I294SporRank
import CFSG.GH74.GLS.C3.Layer1.St1PumpCalc
public import CFSG.Monster.Generated.FiniteSimple

public section

namespace CFSG.LocalAnalysis.AGL81TheoremCD.Section12.KbarListFive

open CFSG.Open CFSG.Blueprint.NativeSporadic Subgroup


theorem false_of_monster {K S : Type} [Group K] [Finite K] [Group S] [Finite S]
    (hq : CFSG.IsQuasisimple K) (e : K ⧸ center K ≃* S) (hK : IsSporadic K .M)
    {Y : Subgroup (MulAut S)} (hY : (MulAut.conj : S →* MulAut S).range ≤ Y)
    (hr : CFSG.Open.pRank 3 Y ≤ 3) : False := by
  obtain ⟨a⟩ := hK
  let φ : K →* CFSG.Monster.Generated.Gmat := CFSG.YGroups.Y443.fM.comp
    ((CFSG.Sporadic.Bridge.Y443.commutatorMulEquiv).toMonoidHom.comp a.toMonoidHom)
  have hφ : Function.Surjective φ := CFSG.RankThree.PartOne.SPOR.fM_surjective.comp
    (CFSG.Sporadic.Bridge.Y443.commutatorMulEquiv.surjective.comp a.surjective)
  have : IsSimpleGroup CFSG.Monster.Generated.Gmat :=
    CFSG.Monster.Generated.generated_rational_group_finite_simple.2.1
  have : Finite CFSG.Monster.Generated.Gmat :=
    CFSG.Monster.Generated.generated_rational_group_finite_simple.2.2
  obtain ⟨b⟩ := CFSG.GH74.GLS.C3.Layer1.PumpCalc.equiv_quotient_center_of_surjective hq
    (inferInstance : IsSimpleGroup CFSG.Monster.Generated.Gmat) φ hφ
  let ψ : S ≃* CFSG.Monster.Generated.Gmat := e.symm.trans b.symm
  have : IsSimpleGroup S := ψ.isSimpleGroup
  have hnab : ∃ x y : S, x * y ≠ y * x := by
    obtain ⟨x, y, hxy⟩ := hq.2.2
    exact ⟨e x, e y, fun h => hxy (e.injective (by simpa only [map_mul] using h))⟩
  have hS := (pRank_top_le_of_inner_le (by norm_num : 1 < 3)
    (GL83.I713.center_eq_bot_of_simple hnab) hY).trans hr
  have h4 := CFSG.LocalAnalysis.RankThreeTheoremC.KFactProofs.Stroth.Bal3.four_le_pRank_Gmat
  rw [← CFSG.SectionRank.pRank_top_eq_of_mulEquiv (by norm_num : 1 < 3) ψ] at h4
  omega

end CFSG.LocalAnalysis.AGL81TheoremCD.Section12.KbarListFive

end
