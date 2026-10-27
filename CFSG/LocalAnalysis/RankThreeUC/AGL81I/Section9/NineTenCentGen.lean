module

public import CFSG.LocalAnalysis.RankThreeUC.AGL81CNineTenCent
public import CFSG.LocalAnalysis.RankThreeUC.AGL81CNineTenInputs
public import CFSG.LocalAnalysis.RankThreeUC.AGL81I.Section9.Base
public import CFSG.LocalAnalysis.RankThreeUC.AGL81I.Section9.NineTenCompGen
public import CFSG.LocalAnalysis.RankThreeUC.AGL81I.Section9.NineTenLayerGen
public import CFSG.LocalAnalysis.RankThreeUC.AGL81I.Section9.NineTenQuotGen
public import CFSG.LocalAnalysis.RankThreeUC.AGL81I.Section9.NineTenSigmaGen
public import CFSG.LocalAnalysis.RankThreeUC.AGL81I.Section9.NineTenRhoGen
public import CFSG.ClassicalInvolution.WeakCT.Main
public import CFSG.HardMathSupport.Lang.Coordinator.OuterFixedOrderE6Order
public import CFSG.HardMathSupport.Solomon.LocalBalance.Lemma32
public import CFSG.HardMathSupport.Solomon.LocalBalance.Sec2Statements
public import CFSG.HardMathSupport.Solomon.LocalBalance.Sec5Statements
public import CFSG.LocalAnalysis.AGLEmbeddingD2.Tits.MsideParabolicEscape.ExcTwistedE6
public import CFSG.LocalAnalysis.ComponentClassification.CatalogueBHigherLinearFieldDeterminant
public import CFSG.LocalAnalysis.ComponentClassification.GrSLitHeMax
public import CFSG.LocalAnalysis.ComponentClassification.OutcomeLocalOddCentralizer
public import CFSG.LocalAnalysis.ComponentInitial.SteinbergBUProjectivePlaneCoordinateLinear
public import CFSG.LocalAnalysis.ComponentInitial.SteinbergBUProjectivePlaneFieldRoot
public import CFSG.LocalAnalysis.ComponentInitial.SteinbergBUProjectivePlaneHilbertNinety
public import CFSG.LocalAnalysis.ComponentInitial.SteinbergBUProjectivePlaneLinearField
public import CFSG.LocalAnalysis.ComponentInitial.SteinbergBUProjectivePlanePureFieldMatrix
public import CFSG.LocalAnalysis.ProperTwoGeneratedCore.LocalCriterionNormalTwoFixedPointHull
public import CFSG.LocalAnalysis.ProperTwoGeneratedCore.LocalCriterionThreePointFullTransport
public import CFSG.LocalAnalysis.RankThreeTheoremC.D1Frontier3
public import CFSG.LocalAnalysis.RankThreeTheoremC.GL83Generic4_1P3L28Residues
public import CFSG.LocalAnalysis.RankThreeTheoremC.GL83Generic4_1P3P34Defs
public import CFSG.LocalAnalysis.RankThreeTheoremC.GL83P3KFacts
public import CFSG.LocalAnalysis.RankThreeTheoremC.GL83SmallRank614Defs
public import CFSG.LocalAnalysis.RankThreeTheoremC.GL83SmallRank614PrimeDefs
public import CFSG.LocalAnalysis.RankThreeTheoremC.GL83SmallRank632Defs
public import CFSG.LocalAnalysis.RankThreeTheoremC.GL83SmallRank65Defs
public import CFSG.LocalAnalysis.RankThreeTheoremC.KFactProofs.K3.Defs
public import CFSG.LocalAnalysis.RankThreeTheoremC.KFactProofs.T29.Defs
public import CFSG.LocalAnalysis.RankThreeTheoremC.RelativePairInputs
public import CFSG.LocalAnalysis.RankTwoShapes.UnitaryFourPresentation
public import CFSG.LocalAnalysis.ShultStronglyClosedTI.MinimalLocalFailureConjugation
public import CFSG.LocalAnalysis.ShultStronglyClosedTI.MinimalLocalFailureProperPair
public import CFSG.LocalAnalysis.ShultStronglyClosedTI.MinimalLocalFailureSylowAssemblyData
public import CFSG.LocalAnalysis.ShultStronglyClosedTI.MinimalLocalFailureSylowAssemblyProper
public import CFSG.Monster.GMS.Fi23Gen
public import CFSG.Monster.GMS.Fi23GenIso
public import CFSG.Monster.GMS.Fi23GenSix
public import CFSG.Monster.GMS.LeechCoh
public import CFSG.Monster.GMS.LeechCohGroup
public import CFSG.Monster.GMS.S365Center
public import CFSG.Monster.GMS.S37
public import CFSG.Monster.GMS.S4Assembly
public import CFSG.Monster.GMS.S4CohB
public import CFSG.Monster.GMS.S5Inputs
public import CFSG.RankThree.Chevalley.SteinbergBIE7ThreeA1
public import CFSG.RankThree.PartOne.KF.F128Count
public import CFSG.RankThree.PartOne.RF4.FinalSec66
public import CFSG.RankThree.PartOne.S11b.OuterPrimeTwoSporadicOpen
public import CFSG.RankThree.PartOne.S9.OddCore.RecognitionBasic
public import CFSG.Sporadic.Co1.Module.Co2Stab
public import CFSG.Sporadic.Schreier.J1QT
public import CFSG.Sporadic.SuzOddCore.GraphData
public import CFSG.Sporadic.SuzOddCore.SmallActionData
public import Certificates.Certificate16005
public import Certificates.Certificate3044
public import Certificates.Certificate3122
public import Certificates.Certificate3123
public import Certificates.Certificate3130
public import Certificates.Certificate3133
public import Certificates.Certificate3134
public import Certificates.Certificate3136
public import Certificates.Certificate3137
public import Certificates.Certificate3176
public import Certificates.Certificate3179
public import Certificates.Certificate7000
public import Certificates.Certificate7001
public import Certificates.Certificate7002
public import Certificates.Certificate7003
public import Certificates.Certificate7004
public import Certificates.Certificate7005
public import Certificates.Certificate7006
public import Certificates.Certificate7007
public import Certificates.Certificate7008
public import Certificates.Certificate7009
public import Certificates.Certificate7010
public import Certificates.Certificate7011
public import Certificates.Certificate8052

public section

namespace CFSG.LocalAnalysis.RankThreeUC.AGL81C

open CFSG.Open CFSG.RankThreeCoreUniqueness.Helpers CFSG.LocalAnalysis.RankThreeUC.S15 Subgroup

namespace NineSettingGen

variable {G : Type} [Group G] [Finite G] {M : Subgroup G} {p : ℕ} {Q H E : Subgroup G}

section Certified


theorem centralizer_pCore_le_starImg (h713 : SevenOneThree) (hI : NineTenInputs)
    (h : NineSettingGen G M p Q H E 2) (hH2 : H ∈ H2Fam M Q) (hp : p ∉ sigmaM G M)
    (hQ : CFSG.ABGLocalTools.IsSylowOf p Q H) (hNQ : normalizer (Q : Set G) ≤ M)
    (hQN : starImg p H Q ≤ compNormalizer (StarGroup p H)) (hL : pLayerIn p H ≤ M) :
    centralizer (CFSG.pCore p (StarGroup p H) : Set (StarGroup p H)) ≤ starImg p H M := by
  haveI : Fact p.Prime := ⟨h.prime⟩
  let R : Subgroup (StarGroup p H) := CFSG.pCore p (StarGroup p H)
  let L : Subgroup (StarGroup p H) := CFSG.layer (StarGroup p H)
  let Yc : Subgroup (StarGroup p H) := centralizer (L : Set (StarGroup p H))
  let Cc : Subgroup (StarGroup p H) := centralizer (R : Set (StarGroup p H))
  haveI hRn : R.Normal := inferInstance
  haveI hLc : L.Characteristic := CFSG.LocalCores.layer_characteristic
  haveI hLn : L.Normal := inferInstance
  haveI hYcN : Yc.Normal := inferInstance
  haveI hCcN : Cc.Normal := inferInstance
  let B : Subgroup (StarGroup p H) := starImg p H Q ⊔ Cc
  have hS := h.isSylowOf_starImg_top hQ
  have hSB : CFSG.ABGLocalTools.IsSylowOf p (starImg p H Q) B :=
    hS.of_le le_sup_left le_top
  have hSM : normalizer (starImg p H Q : Set (StarGroup p H)) ≤ starImg p H M :=
    h.normalizer_starImg_le h.Q_le_H hQ.isPGroup hNQ
  have hle : B ≤ (B ⊓ (L ⊔ Yc)) ⊔ starImg p H M :=
    h.le_inf_sup_starImg h713 hI hH2 hp (h.not_dvd_index_compNormalizer hQ hQN)
      (B := B) (S := starImg p H Q) hSB hSM
  have hLstar : L ≤ starImg p H M := h.pLayerIn_le_iff.mp hL
  have hLC : L ≤ Cc := Subgroup.le_centralizer_iff.mp (pCore_le_centralizer_layer h.prime H)
  have hLB : L ≤ B := hLC.trans le_sup_right
  have hTp : IsPGroup p ↥(B ⊓ Yc) := by
    change ∀ b : ↥(B ⊓ Yc), ∃ k, b ^ p ^ k = 1
    intro b
    obtain ⟨q, hq, c, hc, hqc⟩ :=
      (Subgroup.mem_sup_of_normal_right.mp b.2.1 : ∃ y ∈ starImg p H Q,
        ∃ z ∈ Cc, y * z = (b : StarGroup p H))
    obtain ⟨a, ha⟩ := hS.isPGroup.exists_orderOf_eq_pow ⟨q, hq⟩
    have hqpow : q ^ p ^ a = 1 := by
      have h := pow_orderOf_eq_one (⟨q, hq⟩ : ↥(starImg p H Q))
      rw [ha] at h
      simpa using h
    have hbq : (QuotientGroup.mk' Cc) (b : StarGroup p H) = (QuotientGroup.mk' Cc) q := by
      have hc1 : (QuotientGroup.mk' Cc) c = 1 :=
        MonoidHom.mem_ker.mp (by rw [QuotientGroup.ker_mk']; exact hc)
      rw [show (b : StarGroup p H) = q * c from hqc.symm, map_mul, hc1, mul_one]
    have hbpowC : (b : StarGroup p H) ^ p ^ a ∈ Cc := by
      have h1 : (QuotientGroup.mk' Cc) ((b : StarGroup p H) ^ p ^ a) = 1 := by
        rw [map_pow, hbq, ← map_pow, hqpow, map_one]
      have h2 : (b : StarGroup p H) ^ p ^ a ∈ (QuotientGroup.mk' Cc).ker :=
        MonoidHom.mem_ker.mpr h1
      rwa [QuotientGroup.ker_mk'] at h2
    have hRY : Yc ⊓ Cc ≤ R := by
      have h' := cStarL_inf_centralizer_le_pCore h.prime H
      rwa [cStarL_eq_centralizer_layer h.prime H] at h'
    have hbpowR : (b : StarGroup p H) ^ p ^ a ∈ R :=
      hRY ⟨Yc.pow_mem b.2.2 _, hbpowC⟩
    obtain ⟨d, hd⟩ := (CFSG.pCore_isPGroup (p := p) (G := StarGroup p H)).exists_orderOf_eq_pow
      ⟨(b : StarGroup p H) ^ p ^ a, hbpowR⟩
    have hd' : orderOf ((b : StarGroup p H) ^ p ^ a) = p ^ d :=
      (Subgroup.orderOf_coe ⟨_, hbpowR⟩).trans hd
    refine ⟨a + d, ?_⟩
    apply Subtype.ext
    rw [Subgroup.coe_pow, Subgroup.coe_one, pow_add, pow_mul, ← hd', pow_orderOf_eq_one]
  have hBnorm : B ≤ Subgroup.normalizer ((B ⊓ Yc : Subgroup (StarGroup p H)) :
      Set (StarGroup p H)) := by
    have hsub : ((B ⊓ Yc).subgroupOf B).Normal := by
      rw [Subgroup.inf_subgroupOf_left]
      exact hYcN.subgroupOf B
    exact (Subgroup.normal_subgroupOf_iff_le_normalizer inf_le_left).mp hsub
  have hQnT : starImg p H Q ≤ Subgroup.normalizer ((B ⊓ Yc : Subgroup (StarGroup p H)) :
      Set (StarGroup p H)) := le_sup_left.trans hBnorm
  have hQT_eq : starImg p H Q ⊔ (B ⊓ Yc) = starImg p H Q :=
    hS.eq_of_le le_sup_left le_top (hS.isPGroup.to_sup_of_normal_right' hTp hQnT)
  have hstep6 : B ⊓ Yc ≤ starImg p H Q := by
    rw [← hQT_eq]; exact le_sup_right
  have hstep7 : B ⊓ (L ⊔ Yc) ≤ starImg p H M := by
    intro x hx
    obtain ⟨l, hl, y, hy, hly⟩ := (Subgroup.mem_sup_of_normal_left.mp hx.2 :
      ∃ a ∈ L, ∃ b ∈ Yc, a * b = (x : StarGroup p H))
    have hyB : y ∈ B := by
      have hy_eq : y = l⁻¹ * x := by rw [← hly]; group
      rw [hy_eq]
      exact B.mul_mem (B.inv_mem (hLB hl)) hx.1
    have hyM : y ∈ starImg p H M :=
      Subgroup.map_mono (Subgroup.comap_mono h.Q_le_M) (hstep6 ⟨hyB, hy⟩)
    have hmul : l * y ∈ starImg p H M := (starImg p H M).mul_mem (hLstar hl) hyM
    rw [hly] at hmul
    exact hmul
  have hBle : B ≤ starImg p H M := hle.trans (sup_le hstep7 le_rfl)
  exact le_sup_right.trans hBle

theorem isPSLType_oPPrimeHull_quotKer_of_le (h713 : SevenOneThree) (hI : NineTenInputs)
    (h : NineSettingGen G M 3 Q H E 2) (hH2 : H ∈ H2Fam M Q) (hp : 3 ∉ sigmaM G M)
    (hU : NineNineOne M 3) (hQ : CFSG.ABGLocalTools.IsSylowOf 3 Q H)
    (hNQ : normalizer (Q : Set G) ≤ M)
    (hQN : starImg 3 H Q ≤ compNormalizer (StarGroup 3 H)) (hL : pLayerIn 3 H ≤ M)
    (hR : CFSG.Open.pRank 3 (CFSG.pCore 3 (StarGroup 3 H)) ≤ 2) :
    IsPSLType 2 (ZMod 3) ↥(oPPrimeHull 3 (⊤ : Subgroup (QuotKer M H))) := by
  have hcent := h.centralizer_pCore_le_starImg h713 hI hH2 hp hQ hNQ hQN hL
  refine h.isPSLType_oPPrimeHull_quotKer_of_centralizer_le hp hU hR ?_
  have hstar : starImg 3 H
      (((Subgroup.centralizer (CFSG.pCore 3 (StarGroup 3 H) : Set (StarGroup 3 H))).comap
        (QuotientGroup.mk' (primeComplementCore (G := ↥H) 3))).map H.subtype)
      = Subgroup.centralizer (CFSG.pCore 3 (StarGroup 3 H) : Set (StarGroup 3 H)) := by
    unfold starImg
    have h1 : (Subgroup.map H.subtype
        ((Subgroup.centralizer (CFSG.pCore 3 (StarGroup 3 H) : Set (StarGroup 3 H))).comap
          (QuotientGroup.mk' (primeComplementCore (G := ↥H) 3)))).subgroupOf H
        = (Subgroup.centralizer (CFSG.pCore 3 (StarGroup 3 H) :
            Set (StarGroup 3 H))).comap
          (QuotientGroup.mk' (primeComplementCore (G := ↥H) 3)) :=
      Subgroup.comap_map_eq_self_of_injective H.subtype_injective _
    rw [h1, Subgroup.map_comap_eq_self_of_surjective (QuotientGroup.mk'_surjective _)]
  exact (h.le_iff_starImg_le (Subgroup.map_subtype_le _)).mpr (by rw [hstar]; exact hcent)

end Certified

end NineSettingGen

end CFSG.LocalAnalysis.RankThreeUC.AGL81C
