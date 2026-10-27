module

public import CFSG.LocalAnalysis.AGLEmbedding.UnitaryFacts
public import Certificates.Certificate113
public import Certificates.Certificate114
public import Certificates.Certificate117
import CFSG.LocalAnalysis.AGLEmbedding.KFactProofs.CenterHopf
import CFSG.LocalAnalysis.AGLEmbedding.KFactProofs.UnitaryModel
import CFSG.LieType.Steinberg.CentralExt.SUOddClosed
public import CFSG.Assembly.OrderReductions.InvertedSubgroup
public import CFSG.Assembly.OrderReductions.OddInversion
public import CFSG.Assembly.QuasithinDefs
public import CFSG.Foundations
public import CFSG.GroupTheory.LocalCores.Fitting
public import CFSG.LocalAnalysis.AGLEmbedding.CaseThreeFamilies
public import CFSG.LocalAnalysis.AGLEmbedding.JStarReducedDefs
public import CFSG.LocalAnalysis.AGLEmbedding.TwoCoreObstruction
public import CFSG.LocalAnalysis.ComponentClassification.CatalogueKProper
public import CFSG.LocalAnalysis.ComponentClassification.DisjointSolvableKernels
public import CFSG.LocalAnalysis.ComponentClassification.LBalanceComponentLifts
public import CFSG.LocalAnalysis.ComponentClassification.LayerMultiplication
public import CFSG.LocalAnalysis.ComponentClassification.MinimalBCenter
public import CFSG.LocalAnalysis.ComponentClassification.OrdinaryComponentJoins
public import CFSG.LocalAnalysis.ComponentClassification.TwoLayer
public import CFSG.LocalAnalysis.ComponentClassification.UniversalOrbitBlock
public import CFSG.LocalAnalysis.ComponentInitial.LayerComponentOrbit
public import CFSG.LocalAnalysis.RankThreeEvenClassification.ComponentCore
public import CFSG.RankThree.GroupTheory.SteinbergBYSectionNineResidual
public import CFSG.RankThree.LocalRank.SelectorCases
public import CFSG.RankThree.PartOne.Assembly
public import CFSG.RankThree.PartOne.CTP.StrongPSylow
public import CFSG.RankThree.PartOne.S10.ThetaContract
public import CFSG.RankThree.PartOne.S12.InputsBase
import CFSG.Permutation.UnitaryThreeRecognition.Model
import CFSG.ThirdParty.QiuzhenCFSG.GorensteinWalter.Defs
import CFSG.ThirdParty.QiuzhenCFSG.GorensteinWalter.FiniteFieldFixedSubfieldCard

public section

namespace CFSG.AGLEmbedding

theorem kFactUnitarySchur :
    KFactUnitarySchur := by
  intro K _ _ p d hd hqs hZ ⟨e⟩
  obtain ⟨⟨hp, hf, -, hne⟩, F, _, _, hF, ⟨φ⟩⟩ := UnitaryModel.statedClassicalModel hd ⟨e⟩
  have : Fact p.Prime := ⟨hp⟩
  have : CharP F p := UnitaryModel.charP_of_card hp hF
  have hdvd := card_center_dvd_card_griessHopfMultiplier (⟨hqs.1⟩ : Group.IsPerfect K) φ
  obtain ⟨-, ⟨ψ⟩⟩ := CFSG.LieType.Steinberg.CentralExt.SUOdd.psu_odd_hopfMultiplier hF hf
    (by norm_num : 3 ≤ 3) (by decide : ¬ Even 3) hne
  rw [Nat.card_congr ψ.toEquiv, ← Nat.card_congr (Multiplicative.ofAdd (α := ZMod _)),
    Nat.card_zmod] at hdvd
  obtain ⟨k, hk⟩ := hZ.exists_card_eq
  rw [← Subgroup.card_eq_one, hk]
  rw [hk] at hdvd
  rcases Nat.eq_zero_or_pos k with rfl | hk0
  · rfl
  · exfalso
    have h1 : p ∣ Nat.gcd 3 (p ^ d.1.fieldExponent + 1) := (dvd_pow_self p hk0.ne').trans hdvd
    have h3 : p ∣ 3 := h1.trans (Nat.gcd_dvd_left _ _)
    have h4 : p ∣ p ^ d.1.fieldExponent + 1 := h1.trans (Nat.gcd_dvd_right _ _)
    have h5 : p ∣ 1 := (Nat.dvd_add_right (dvd_pow_self p (by omega))).mp h4
    exact hp.one_lt.ne' (Nat.dvd_one.mp h5)

end CFSG.AGLEmbedding
