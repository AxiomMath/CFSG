module

public import CFSG.LocalAnalysis.RankThreeTheoremC.Generic41Spor.GroupSz32
import CFSG.LocalAnalysis.RankFourTheoremC.PPointExoticSigSzCore
import CFSG.LocalAnalysis.AGLEmbedding.KFactProofs.ONanSz32Local
import CFSG.RankThree.PartOne.CTP.SeitzExcModels
import CFSG.RankThree.PartOne.K159.AutSzIso
import CFSG.RankThree.PartOne.K159.AutSzAbs
import CFSG.LieType.Ree.SuzukiSimple
import CFSG.LocalAnalysis.AGLEmbedding.CaseThreeFamilies
import CFSG.LocalAnalysis.AGLEmbedding.ResidualTools

public section

namespace CFSG.LocalAnalysis.RankThreeTheoremC.Generic41Spor

open CFSG.Open Subgroup

@[expose] def Sz32SigOne : Prop :=
  ∀ (K : Type) [Group K] [Finite K], IsSz32Type 5 K → ∀ x : K, orderOf x = 5 →
    ∀ W : Subgroup K, Nat.Coprime 5 (Nat.card W) → x ∈ Subgroup.normalizer (W : Set K) → W = ⊥

theorem sz32_sigOne :
    Sz32SigOne := by
  intro K _ _ hK x hx W hW hxW
  obtain ⟨-, hiso⟩ := hK
  haveI : Fact (Nat.Prime 5) := ⟨by norm_num⟩
  have hSz := CFSG.RankThree.PartOne.K159.SzAbs.szSylow_of_isoLie hiso
  have hmodel := CFSG.RankThree.PartOne.CTP.suzukiModel_of_isoLie 2 hiso
  obtain ⟨-, a, ha, F, _, _, hfa, hF, ⟨eF⟩⟩ := hmodel
  have hF' : Nat.card F = 2 ^ (2 * a + 1) := by rw [← hfa]; exact hF
  have hsimple : IsSimpleGroup K := by
    have := (CFSG.LieType.Ree.suzuki_simple ha hF').2.2
    exact eF.isSimpleGroup
  obtain rfl : a = 2 := by omega
  let σ : F ≃+* CFSG.AGLEmbedding.KFactProofs.Sz32.F32 :=
    CFSG.AGLEmbedding.KFactProofs.Sz32.F32.ringEquiv F hF'
  let ε : K ≃* CFSG.Blueprint.suzukiGroup 2 CFSG.AGLEmbedding.KFactProofs.Sz32.F32 :=
    eF.trans (CFSG.AGLEmbedding.KFactProofs.Sz32Local.modelEquiv σ)
  have hC : ∀ T : Sylow 5 K, ∀ t ∈ (T : Subgroup K), t ≠ 1 → ∀ g : K, g * t = t * g →
      g ∈ (T : Subgroup K) := fun T =>
    CFSG.AGLEmbedding.KFactProofs.Sz32Local.centralizer_le_of_equiv ε T
  have hW' : ¬ 5 ∣ Nat.card W := (Nat.Prime.coprime_iff_not_dvd Nat.prime_five).1 hW
  exact CFSG.LocalAnalysis.RankFourTheoremC.SzSignalizer.eq_bot_of_normalizes hSz hsimple hC hx hW' hxW

end CFSG.LocalAnalysis.RankThreeTheoremC.Generic41Spor
