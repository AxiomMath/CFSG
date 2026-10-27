module

public import CFSG.LocalAnalysis.RankThreeTheoremC.AGL81ElevenElevenRankOneDefs
public import Certificates.Certificate113
public import Certificates.Certificate43
import CFSG.LocalAnalysis.AGLEmbedding.KFactProofs.CaseTwoSylow
import CFSG.LocalAnalysis.AGLEmbedding.KFactProofs.L28AutThree
import CFSG.RankThree.PartOne.K159F.SzAbs
public import CFSG.CGT.Timmesfeld75.L2Pair
public import CFSG.CGT.Timmesfeld75.ListWCBasic
public import CFSG.CharacterTheory.Wreathed.OddKernelSylowQuotient
public import CFSG.ClassicalGroups
public import CFSG.Goldschmidt.Statements
public import CFSG.Goldschmidt.StatementsG3
public import CFSG.Goldschmidt.StatementsH
public import CFSG.GroupTheory.QuasiDihedralFusion.InvolutionCentralizer
public import CFSG.GroupTheory.RegularModuleThree
public import CFSG.HardMathSupport.Cooperstein.Coordinator.Parts
public import CFSG.LocalAnalysis.AGLEmbedding.OneLieUniqueJCompetitor
public import CFSG.LocalAnalysis.AGLEmbedding.OneSmallGEVIaBlock
public import CFSG.LocalAnalysis.AGLEmbedding.OneSmallGEVIbThreeMSide
public import CFSG.LocalAnalysis.ComponentInitial.LinearInvolutionFixedField
public import CFSG.LocalAnalysis.RankThreeTheoremC.AGL81CZeroLeaves
public import CFSG.LocalAnalysis.RankThreeTheoremC.AGL81ElevenElevenOtherCfgOf
public import CFSG.LocalAnalysis.RankThreeTheoremC.AGL81ElevenSevenCfgOf
public import CFSG.LocalAnalysis.RankThreeTheoremC.AGL81TenThreeThreeAlt
public import CFSG.LocalAnalysis.RankThreeTheoremC.AGL81TenThreeThreeAtProof
public import CFSG.LocalAnalysis.RankThreeTheoremC.D1CaseOne3ACentralBaseXQ
public import CFSG.LocalAnalysis.RankThreeTheoremC.D1CaseThree3LinTwo
public import CFSG.LocalAnalysis.RankThreeTheoremC.D1CaseTwo3CentralU
public import CFSG.LocalAnalysis.RankThreeTheoremC.D1CaseTwo3InnerNotQRankTwo
public import CFSG.LocalAnalysis.RankThreeTheoremC.D1KlingenSp4Main
public import CFSG.Quasithin.Background.A3Structure319
public import CFSG.Quasithin.Background.B4ModelsAction
public import CFSG.Quasithin.Background.G2A5Setting
public import CFSG.Quasithin.Background.InternalSecData
public import CFSG.Quasithin.Background.InternalSecIso
public import CFSG.Quasithin.H13.Sp62D3
public import CFSG.Quasithin.Vol2.Ch10StatementsE
public import CFSG.Quasithin.Vol2.Ch11SecA02Setup
public import CFSG.Quasithin.Vol2.Ch11SecA03Basic
public import CFSG.Quasithin.Vol2.Ch11SecA04Glue
public import CFSG.Quasithin.Vol2.Ch11SecA11Exists
public import CFSG.Quasithin.Vol2.Ch11SecAFacts03
public import CFSG.Quasithin.Vol2.Ch11SecAFacts04
public import CFSG.Quasithin.Vol2.Ch11SecAVi2
public import CFSG.Quasithin.Vol2.Ch11SecSFacts
public import CFSG.Quasithin.Vol2.Ch11SecSSetup
public import CFSG.RankThree.PartTwo.Sec4.Item47Statement
public import CFSG.RankThree.PartTwo.Sec4.Item47Witness
public import CFSG.Sporadic.Schreier.J4SProfileNode
public import TauCeti.GroupTheory.SpecificGroups.CFSG.TypeC.Agreement

public section

namespace CFSG.LocalAnalysis.RankThreeTheoremC

open CFSG.AGLEmbedding

theorem card_mulAut_dvd_of_isCaseTwoGroup_five
    {L : Type} [Group L] (hL : IsCaseTwoGroup 5 L) :
    Nat.card (MulAut L) ∣ Nat.card L * 5 := by
  obtain ⟨⟨x, hv⟩, hd, he⟩ := id hL
  rcases hd with ⟨h53, -⟩ | ⟨-, hs⟩
  · omega
  · obtain rfl : x = TauCeti.LieTypeIndex.suzuki 2 := hs
    have hOut : (CFSG.ComponentClassification.OuterAutomorphisms.inner L).index ∣ 5 :=
      CFSG.RankThree.PartOne.K159F.card_outer_dvd_five
        (⟨hv, he⟩ : CFSG.RankThree.PartOne.Census3.IsoLie L (.suzuki 2))
    rw [← Subgroup.card_mul_index (CFSG.ComponentClassification.OuterAutomorphisms.inner L)]
    exact Nat.mul_dvd_mul (Subgroup.card_range_dvd (MulAut.conj : L →* MulAut L)) hOut

theorem card_le_of_isPGroup_mulAut_five
    {L : Type} [Group L] [Finite L] (hL : IsCaseTwoGroup 5 L)
    {A : Subgroup (MulAut L)} (hA : IsPGroup 5 A) : Nat.card A ≤ 5 ^ 3 := by
  have : Fact (Nat.Prime 5) := ⟨Nat.prime_five⟩
  have hL0 : Nat.card L ≠ 0 := Nat.card_pos.ne'
  have hL25 : (Nat.card L).factorization 5 = 2 := by
    have h := card_sylow_five_of_isCaseTwoGroup hL (default : Sylow 5 L)
    rw [Sylow.card_eq_multiplicity, show (25 : ℕ) = 5 ^ 2 by norm_num] at h
    exact Nat.pow_right_injective (by norm_num) h
  obtain ⟨k, hk⟩ := hA.exists_card_eq
  have hdvd : 5 ^ k ∣ Nat.card L * 5 := by
    rw [← hk]
    exact (Subgroup.card_subgroup_dvd_card A).trans (card_mulAut_dvd_of_isCaseTwoGroup_five hL)
  have hk3 : k ≤ 3 := by
    have hne : Nat.card L * 5 ≠ 0 := mul_ne_zero hL0 (by norm_num)
    have h := (Nat.Prime.pow_dvd_iff_le_factorization Nat.prime_five hne).1 hdvd
    rw [Nat.factorization_mul hL0 (by norm_num), Finsupp.add_apply, hL25,
      Nat.Prime.factorization_self Nat.prime_five] at h
    omega
  rw [hk]
  exact Nat.pow_le_pow_right (by norm_num) hk3

theorem kFactCaseTwoSylowAut :
    KFactCaseTwoSylowAut := by
  intro p L _ _ hL
  obtain ⟨d, hd, -⟩ := id hL
  rcases hd with ⟨rfl, -⟩ | ⟨rfl, -⟩
  · refine ⟨fun T => ?_, fun A hA => ?_⟩
    · have h := card_sylow_three_of_isCaseTwoGroup hL T
      omega
    · have h := kFactL28AutThree L hL A hA
      omega
  · exact ⟨fun T => by have h := card_sylow_five_of_isCaseTwoGroup hL T; omega,
      fun A hA => card_le_of_isPGroup_mulAut_five hL hA⟩

end CFSG.LocalAnalysis.RankThreeTheoremC
