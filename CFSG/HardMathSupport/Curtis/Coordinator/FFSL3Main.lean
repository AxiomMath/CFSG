module

public import CFSG.HardMathSupport.Curtis.Coordinator.FFSL3Assembly
public import CFSG.HardMathSupport.Curtis.Coordinator.AutCenterFFSplit
public import CFSG.Open.GriessAllModelsStatement
import CFSG.HardMathSupport.Curtis.Coordinator.CensusAssembly
import CFSG.HardMathSupport.Curtis.Coordinator.BlockGlue
import CFSG.LocalAnalysis.AGLEmbedding.BlockToralCensusDispatchIb
import CFSG.LocalAnalysis.AGLEmbedding.KFactProofs.CatalogSchreier
import CFSG.Quasithin.EmptyFaithfulMultiple.TheoremEB51
import CFSG.Quasithin.MS93.S32Types
import CFSG.CGT.Timmesfeld75.MultPrime
import CFSG.LocalAnalysis.AGLEmbeddingD2.McLaughlin.WeakBlockModuleData.BlockRank
public import CFSG.Fischer.Classification.Recognition.PSU6
public import CFSG.LocalAnalysis.RankTwoShapes.UnitaryFour.Bridge
public import CFSG.Monster.B.TwoA.Census.PermClasses

public section

namespace CFSG.HardMathSupport.Curtis.Coordinator

open CFSG.AGLEmbedding CFSG.Open CFSG.Quasithin CFSG.QuasithinUnique

theorem card_projectiveSL_three {f : ℕ} (hf : 1 ≤ f) :
    Nat.card (CFSG.LocalAnalysis.ComponentInitial.LinearFlag.projectiveSL 3 (GaloisField 2 f)) =
      ordA 2 (2 ^ f) := by
  have hF : Nat.card (GaloisField 2 f) = 2 ^ f := GaloisField.card 2 f (by omega)
  obtain ⟨-, -, hc⟩ := MS93.isPSL_quot_of_equiv_statedSL_three hF
    (MulEquiv.refl ↥(CFSG.Assembly.LowTwoRank.StatedSL 3 (GaloisField 2 f)))
  rw [← hc]
  let e3 : ↥(CFSG.Assembly.LowTwoRank.StatedSL 3 (GaloisField 2 f)) ⧸
      Subgroup.center ↥(CFSG.Assembly.LowTwoRank.StatedSL 3 (GaloisField 2 f)) ≃*
      CFSG.LocalAnalysis.ComponentInitial.LinearFlag.projectiveSL 3 (GaloisField 2 f) :=
    (SmithC27.quotCenterCongr
      (CFSG.Assembly.LowTwoRank.specialLinearGroupEquivStatedSL 3 (GaloisField 2 f)).symm).trans
      ((CFSG.Assembly.LowTwoRank.projectiveSpecialLinearGroupEquivStatedProj 3
        (GaloisField 2 f)).trans
      (CFSG.CGT.Timmesfeld75.projectiveSLMulEquivStatedProj 3 (GaloisField 2 f)).symm)
  exact Nat.card_congr e3.symm.toEquiv

theorem not_threeASix_of_psl_three {Y : Type} [Group Y] [Finite Y] {L : Subgroup Y} {f : ℕ}
    (hf : 1 ≤ f)
    (ι : ↥L ⧸ Subgroup.center ↥L ≃*
      CFSG.LocalAnalysis.ComponentInitial.LinearFlag.projectiveSL 3 (GaloisField 2 f)) :
    ¬ (Nat.card (Subgroup.center ↥L) = 3 ∧
      Nonempty (↥L ⧸ Subgroup.center ↥L ≃* alternatingGroup (Fin 6))) := by
  rintro ⟨-, ⟨eA⟩⟩
  have hc : Nat.card (↥L ⧸ Subgroup.center ↥L) = ordA 2 (2 ^ f) := by
    rw [Nat.card_congr ι.toEquiv, card_projectiveSL_three hf]
  have h360 : Nat.card (↥L ⧸ Subgroup.center ↥L) = 360 := by
    rw [Nat.card_congr eA.toEquiv, H13.card_alternatingGroup_fin 6 (by norm_num)]
    decide
  exact MS93.S32.ordA_two_ne_360 hf (hc.symm.trans h360)

theorem citedBlockAutCenterFFSL3_holds
    (hGA : CFSG.Open.GriessAllModelsStatement) : CitedBlockAutCenterFFSL3 := by
  intro G _ _ M S L hK hA hO2 hL h93 hX hS hperf h3Z u hu hu3 huC hV hfix Q hQM hQ3 hQL hQS hQC
  have hSL : S ≤ Subgroup.normalizer (L : Set G) :=
    CFSG.HardMathSupport.Cooperstein.Coordinator.le_normalizer_of_isWeakSBlock hK hA hL
  have hparab : CompParab (barM M L) (blockPL M S L) := compParab_of_nineThreeTwo hA hL hS h93
  have hcyc : CycPerfect 3 (blockPL M S L) := cycPerfect_of_ib Nat.prime_three hperf
  have hperfV : ∃ V : Subgroup (↥M ⧸ CFSG.pCore 2 ↥M), ⁅V, V⁆ = V ∧
      V ≤ Subgroup.normalizer (barM M L : Set (↥M ⧸ CFSG.pCore 2 ↥M)) ∧
      V ≤ Subgroup.normalizer (pCoreOf 2 (blockPL M S L) : Set (↥M ⧸ CFSG.pCore 2 ↥M)) ∧
      u ∈ V := by
    obtain ⟨V, hVV, hVL, hVS, huV⟩ := hV
    refine ⟨V, hVV, hVL, ?_, huV⟩
    rw [← h93.2.2]
    exact hVS
  obtain ⟨f₀, hf₀, ⟨ι⟩⟩ := kFactFixCensusThree_of_proved hGA kFactCatalogSchreier _ (barM M L)
    (blockPL M S L) hparab hcyc u hu hu3 huC hperfV hfix
  have h3A6 := not_threeASix_of_psl_three (by omega) ι
  have h3Z' : 3 ∣ Nat.card (Subgroup.center ↥(barM M L)) := by
    rwa [CFSG.AGLEmbeddingD2.McLaughlin.WeakBlockModuleData.card_inf_centralizer_eq_card_center]
      at h3Z
  obtain ⟨f, hfev, hf2, ⟨e⟩⟩ := kFactFixCensusCenter_holds hGA _ (barM M L) (blockPL M S L) hparab
    hcyc h3Z' h3A6 u (Subgroup.mem_sup_left hu) hu3 huC hfix
  exact commutator_inf_center_eq_bot_of_sl3 B5.asB51_holds CFSG.RankThree.PartOne.TCB.tauCetiCatalogBridge hK hA hL hSL hfev
    (by omega) e hQM hQ3 hQL hQS hQC

end CFSG.HardMathSupport.Curtis.Coordinator
