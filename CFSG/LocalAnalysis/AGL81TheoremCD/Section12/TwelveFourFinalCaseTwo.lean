module

public import CFSG.LocalAnalysis.AGL81TheoremCD.Section12.TwelveFourSteps
public import CFSG.LocalAnalysis.RankThreeUC.AGL81CNineTwelveKer
public import CFSG.LocalAnalysis.RankThreeUC.AGL81CNineTenInputs
import CFSG.LocalAnalysis.AGL81TheoremCD.Section12.TwelveFourKerDecomp
import CFSG.LocalAnalysis.AGL81TheoremCD.Section12.HGenFinal
import CFSG.LocalAnalysis.AGL81TheoremCD.Section12.LThreeParabolic
import CFSG.RankThree.PartOne.U5K.Kf.Sylow
public import CFSG.GH74.GLS.Defs
public import CFSG.GH74.GLS.Stage2.Local.Statements
public import CFSG.LocalAnalysis.AGL81TheoremCD.Section12.TwelveThreeData
public import CFSG.LocalAnalysis.AGLEmbedding.CZeroOrbitLines
import CFSG.LocalAnalysis.AGL81I.Section3.GammaBasics
import CFSG.LocalAnalysis.AGL81I.Section3.ThreeTenBasics
import CFSG.LocalAnalysis.AGL81TheoremCD.Section12.HSubFinal
import CFSG.LocalAnalysis.AGL81TheoremCD.Section12.NineTenBranches
import CFSG.LocalAnalysis.AGL81TheoremCD.Section12.PCoreCharacteristic
import CFSG.LocalAnalysis.AGL81TheoremCD.Section12.StrongEmbedInput
import CFSG.LocalAnalysis.AGL81TheoremCD.Section12.ThreeTenConstrained
import CFSG.LocalAnalysis.AGL81TheoremCD.Section12.ThreeTenDvdP1
import CFSG.LocalAnalysis.RankThreeTheoremC.AGL81NineEightBridge
import CFSG.LocalAnalysis.RankThreeUC.AGL81CNineTenFiveA
import CFSG.LocalAnalysis.RankThreeUC.ModuleHypotheses
import CFSG.LocalAnalysis.RankThreeUC.ModuleRanks
import CFSG.LocalAnalysis.RankThreeUC.Notation
import CFSG.LocalAnalysis.RankThreeUC.SourceSetting.AschbacherCommon
import CFSG.LocalAnalysis.RankThreeUC.WeakModules

public section

namespace CFSG.LocalAnalysis.AGL81TheoremCD.Section12

open CFSG.Open Subgroup
open CFSG.LocalAnalysis.RankThreeUC.AGL81C
open CFSG.AGLEmbedding

variable {G : Type} [Group G] [Finite G] {M : Subgroup G} {p : ℕ} {Q H : Subgroup G} {d : ℕ}

theorem false_of_twelveFour_caseTwo (hKer : NineTwelveKerGen) (hI : NineNineOneInput)
    (h : TwelveCtx G M p Q H) (hd : d ∈ sigmaSet G M) (hA : TwelveFourStepA M d)
    (h2 : TwelveThreeCaseTwo M p H d) {W : Subgroup G} (hW3 : Nat.card W = 3)
    (hWX : W ≤ xSub p M H) (hN : normalizer (W : Set G) ≤ M) : False := by
  have : Fact p.Prime := ⟨h.p_prime⟩
  have hdp : d.Prime := CFSG.RankThreeCoreUniqueness.Helpers.sigmaA_prime d hd.1
  have hdvd : d ∣ p + 1 := h2.2.1.2.2.1
  have h5d : 5 ≤ d := hA.2.2
  have hp5le : 5 ≤ p :=
    five_le_of_odd_prime_dvd_add_one h.p_prime h.p_odd hdp (by omega) hdvd
  have hp3 : p ≠ 3 := by omega
  have hpndvd : ¬ p ∣ Nat.card W := by
    rw [hW3]
    exact fun hd3 => hp3 ((Nat.prime_dvd_prime_iff_eq h.p_prime Nat.prime_three).mp hd3)
  have hWOp : W ≤ relPPrimeCore p H := h2.2.2 W hWX hpndvd
  have : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  have hWp : IsPGroup 3 W := IsPGroup.of_card (n := 1) (by rw [hW3]; norm_num)
  obtain ⟨R, hR, hWR⟩ := exists_isSylowOf_ge (p := 3) hWOp hWp
  have h912 := h.nineTwelveKerConclusion hKer
  have hCW : Subgroup.centralizer (W : Set G) ≤ M :=
    (Subgroup.centralizer_le_normalizer (W : Set G)).trans hN
  have hno5 : ¬ (p = 5 ∧ CFSG.IsExtraspecialPGroup 3 ↥(omegaOnePSub 3 R) ∧
      Nat.card ↥(omegaOnePSub 3 R) = 3 ^ 5 ∧ Monoid.exponent ↥(omegaOnePSub 3 R) = 3) :=
    fun h5 => p_ne_five_of_dvd_p_add_one hdp hA.2.2 hdvd h5.1
  exact not_kSub_le_M_of_nineNineOne h hI
    (kSub_le_M_of_nineTwelveKer h h912 (h2.1 ▸ bot_le) hR hWR hCW hno5)

end CFSG.LocalAnalysis.AGL81TheoremCD.Section12
