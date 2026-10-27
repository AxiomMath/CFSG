module

public import CFSG.LocalAnalysis.AGL81TheoremCD.Section12.TwelveFourSteps
public import CFSG.LocalAnalysis.RankThreeUC.AGL81CNineTwelveKer
public import CFSG.LocalAnalysis.RankThreeUC.AGL81CNineTenInputs
import CFSG.LocalAnalysis.AGL81TheoremCD.Section12.TwelveFourKer
import CFSG.LocalAnalysis.AGL81TheoremCD.Section12.TwelveFourKerDecomp
import CFSG.LocalAnalysis.AGL81TheoremCD.Section12.TwelveFourOneProof
import CFSG.LocalAnalysis.AGL81TheoremCD.Section12.HGenFinal
import CFSG.LocalAnalysis.AGL81TheoremCD.Section12.TwelveSixWX
import CFSG.LocalAnalysis.AGL81TheoremCD.Section12.TwelveSixKCompCentral
import CFSG.LocalAnalysis.AGL81TheoremCD.Section12.TwelveSixCoprimeK
import CFSG.GroupTheory.PCore.NormalPCoreOf
public import CFSG.GH74.GLS.Defs
public import CFSG.GH74.GLS.Stage2.Local.Statements
public import CFSG.LocalAnalysis.AGL81TheoremCD.Section12.TwelveThreeData
public import CFSG.LocalAnalysis.AGLEmbedding.CZeroOrbitLines
import CFSG.GroupTheory.SylowNormalIndex
import CFSG.LocalAnalysis.AGL81TheoremCD.Section12.NineTenBranches
import CFSG.LocalAnalysis.AGL81TheoremCD.Section12.PCoreCharacteristic
import CFSG.LocalAnalysis.AGL81TheoremCD.Section12.TwelveFive
import CFSG.LocalAnalysis.AGL81TheoremCD.Section12.TwelveFour
import CFSG.LocalAnalysis.AGL81TheoremCD.Section12.WeakBlockThree
import CFSG.LocalAnalysis.RankThreeTheoremC.AGL81NineEightBridge
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

theorem false_of_twelveFour_caseSixSpor (hKer : NineTwelveKerGen) (hI : NineNineOneInput)
    (h : TwelveCtx G M p Q H) (_hD : TwelveThreeData M p H d)
    (hc : TwelveThreeCaseSix M p H d ∨ TwelveThreeCaseSpor M p H d) {W : Subgroup G}
    (hW3 : Nat.card W = 3) (hWX : W ≤ xSub p M H) (hN : normalizer (W : Set G) ≤ M) :
    False := by
  have hCW : Subgroup.centralizer (W : Set G) ≤ M :=
    (Subgroup.centralizer_le_normalizer (W : Set G)).trans hN
  have hL : ¬ pLayerIn p H ≤ M := hc.elim (fun h => h.1) (fun h => h.1)
  have hK : ((kSub p M H).subgroupOf H).Normal :=
    hc.elim (fun h => h.2.1) (fun h => h.2.1)
  by_cases hp3 : p = 3
  · subst hp3
    have : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
    have hWp : IsPGroup 3 W := IsPGroup.of_card (n := 1) (by rw [hW3]; norm_num)
    exact not_le_xSub_of_isPGroup h hI hWp hCW hWX
  · have : Fact p.Prime := ⟨h.p_prime⟩
    have : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
    have h912 := h.nineTwelveKerConclusion hKer
    obtain ⟨hperf, hNK⟩ := h.kSub_perfect_and_commutator_le h912 hL hp3
    have hWH : W ≤ H := hWX.trans (xSub_le_H p M H)
    have hWK : W ≤ Subgroup.normalizer (kSub p M H : Set G) :=
      hWH.trans ((Subgroup.normal_subgroupOf_iff_le_normalizer (kSub_le p M H)).mp hK)
    have hcomm := commutator_le_relPPrimeCore_kSub_of_le_xSub h hK hWX
    have hWp : IsPGroup 3 W := IsPGroup.of_card (n := 1) (by rw [hW3]; norm_num)
    have hdecomp := eq_inf_centralizer_sup_pCoreOf_two hWK hWp
      (CFSG.LocalAnalysis.RankThreeTheoremC.KFactProofs.Stroth.AlmostSimple.relPPrimeCore_le
        (kSub p M H)) hperf hcomm hNK
    have hO2M : pCoreOf 2 (kSub p M H) ≤ M := by
      have hle : pCoreOf 2 (kSub p M H) ≤ pCoreOf 2 H :=
        CFSG.GroupTheory.pCoreOf_le_pCoreOf_of_le_normalizer 2 (kSub_le p M H)
          ((Subgroup.normal_subgroupOf_iff_le_normalizer (kSub_le p M H)).mp hK)
      refine hle.trans ?_
      rw [h.pCore_two_inter]
      exact (CFSG.openPCoreOf_le 2 (H ⊓ M)).trans inf_le_right
    exact not_kSub_le_M_of_nineNineOne h hI (by
      rw [hdecomp]
      exact sup_le (inf_le_right.trans hCW) hO2M)

end CFSG.LocalAnalysis.AGL81TheoremCD.Section12
