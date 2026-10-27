module

public import CFSG.LocalAnalysis.GLTheoremA.CatA.S171U42Red
public import CFSG.LocalAnalysis.GLTheoremA.CatA.S171Basic
public import CFSG.LocalAnalysis.GLTheoremA.CatA.KSubTDistinct
public import CFSG.LocalAnalysis.GLTheoremA.CatA.HSubTU5
public import CFSG.LocalAnalysis.GLTheoremA.CatA.HSubTFinU6
public import CFSG.LocalAnalysis.GLTheoremA.CatA.HSubTResD4
public import CFSG.LocalAnalysis.GLTheoremA.CatA.HSubTResGU
public import CFSG.LocalAnalysis.GLTheoremA.CatA.HSubTFinZ
public import CFSG.LocalAnalysis.GLTheoremA.CatA.HSubTFinOmega

public section

namespace CFSG.LocalAnalysis.GLTheoremA.S171

open CFSG.Open CFSG.Yardstones.Md0ec50421ce4 CFSG.LocalAnalysis.GLTheoremA CFSG.LocalAnalysis.GLTheoremA.S10
open CFSG.HardMathSupport.Solomon.Coordinator (lieOrderBridge_holds)
open CFSG.HardMathSupport.Solomon.UniquenessMaximal (isComponentOf_eq_of_isQuasisimple)

private theorem bridge_card_alt6 : Nat.card (alternatingGroup (Fin 6)) = 360 := by
  have h := two_mul_nat_card_alternatingGroup (α := Fin 6)
  have hp : Nat.card (Equiv.Perm (Fin 6)) = 720 := by
    rw [Nat.card_eq_fintype_card, Fintype.card_perm, Fintype.card_fin]; rfl
  omega

private theorem bridge_card_quot_center_le (K : Type) [Group K] [Finite K] :
    Nat.card (K ⧸ Subgroup.center K) ≤ Nat.card K := by
  rw [← Subgroup.index_eq_card]
  exact Nat.le_of_dvd Nat.card_pos (Subgroup.index_dvd_card (Subgroup.center K))

theorem noAlt6CompOf_of_catalog {X Q : TauCeti.CFSGIndex → Prop}
    (hX : ∀ (S : Type) [Group S] [Finite S], catalogIs S X → 3 ∣ Nat.card S ∧ 360 < Nat.card S)
    (hQ : ∀ (S : Type) [Group S] [Finite S], catalogIs S Q → 360 < Nat.card S)
    (hfact : KSubT.CompFact X Q) : NoAlt6CompOf X := by
  intro G _ _ L K b hq hcat hidm hb3 hcomp hA
  obtain ⟨h3q, hbig⟩ := hX _ hcat
  have hdvd : Nat.card (↥L ⧸ Subgroup.center ↥L) ∣ Nat.card ↥L := by
    rw [← Subgroup.index_eq_card]
    exact Subgroup.index_dvd_card (Subgroup.center ↥L)
  have hL : CFSG.Open.GLAPComponent 3 L L :=
    CFSG.RankThree.PartTwo.Sec4.Ronan148L.glaPComponent_three_self hq (h3q.trans hdvd)
  obtain ⟨eA6⟩ := hA
  have hK360 : Nat.card ↥K = 360 := (Nat.card_congr eA6.toEquiv).trans bridge_card_alt6
  by_cases hbC : b ∈ Subgroup.centralizer (L : Set G)
  ·
    have hLC : L ⊓ Subgroup.centralizer ({b} : Set G) = L :=
      inf_eq_left.2 fun l hl =>
        Subgroup.mem_centralizer_singleton_iff.2 (Subgroup.mem_centralizer_iff.1 hbC l hl)
    rw [hLC] at hcomp
    have hKL : K = L := isComponentOf_eq_of_isQuasisimple hcomp hq
    rw [hKL] at hK360
    have h1 := bridge_card_quot_center_le ↥L
    omega
  ·
    have hJ : catalogIs (PSimple 3 L) X :=
      (catalogIs_pSimple_iff Nat.prime_three hL hq).1 hcat
    have hIn : InnDiagOn 3 (Subgroup.zpowers b) L := (S10.innDiagOn_iff hL hq).1 hidm
    have hKc := hfact G L (Subgroup.zpowers b) b hq hJ (Subgroup.mem_zpowers b) hIn hb3 hbC K hcomp
    have h1 := hQ _ hKc
    have h2 := bridge_card_quot_center_le ↥K
    omega

section U5U6Cert


theorem noAlt6CompOf_u5 : NoAlt6CompOf S9.isU5two :=
  noAlt6CompOf_of_catalog
    (fun S _ _ h => by rw [CatDistinct.card_isU5two lieOrderBridge_holds h]; norm_num)
    (fun S _ _ h => by rw [CatDistinct.card_isU4two lieOrderBridge_holds h]; norm_num)
    HSubT.u5_holds

theorem noAlt6CompOf_u6 : NoAlt6CompOf S9.isU6two :=
  noAlt6CompOf_of_catalog
    (fun S _ _ h => by rw [CatDistinct.card_isU6two lieOrderBridge_holds h]; norm_num)
    (fun S _ _ h => by
      rcases catalogIs_three h with h1 | h1 | h1
      · rw [CatDistinct.card_isU4two lieOrderBridge_holds h1]; norm_num
      · rw [CatDistinct.card_isU5two lieOrderBridge_holds h1]; norm_num
      · rw [KSubT.card_isL2eight lieOrderBridge_holds h1]; norm_num)
    (HSubT.u6_of_residual lieOrderBridge_holds (HSubT.u6CompRes_of_threeDvd HSubT.u6ThreeDvdComp_holds))

end U5U6Cert

section D4Cert


theorem noAlt6CompOf_d4_of_gaps (hOU : HSubT.OmegaUnitaryInOm8 CFSG.AGLEmbedding.Om8)
    (hO2 : HSubT.OmegaOrthRank2Solvable CFSG.AGLEmbedding.Om8)
    (hO1 : HSubT.OmegaOrthRank1U4 CFSG.AGLEmbedding.Om8) : NoAlt6CompOf S9.isD4two :=
  noAlt6CompOf_of_catalog
    (fun S _ _ h => by rw [CatDistinct.card_isD4two lieOrderBridge_holds h]; norm_num)
    (fun S _ _ h => by rw [CatDistinct.card_isU4two lieOrderBridge_holds h]; norm_num)
    (HSubT.d4_of_residuals lieOrderBridge_holds HSubT.d4InnerDiagRes_holds
      (HSubT.omegaPlusCompRes_of_residuals
        (HSubT.omegaCentDecomp_of_gaps HSubT.center_aglOm8_eq_bot hOU hO2 hO1)
        HSubT.guBlockFacts_holds))

theorem i171SmallIsU42Fact_of_omegaGaps (hOU : HSubT.OmegaUnitaryInOm8 CFSG.AGLEmbedding.Om8)
    (hO2 : HSubT.OmegaOrthRank2Solvable CFSG.AGLEmbedding.Om8)
    (hO1 : HSubT.OmegaOrthRank1U4 CFSG.AGLEmbedding.Om8) : I171SmallIsU42Fact :=
  i171SmallIsU42Fact_of_noAlt6
    (noAlt6CompOf_split noAlt6CompOf_u5 noAlt6CompOf_u6 (noAlt6CompOf_d4_of_gaps hOU hO2 hO1))

end D4Cert

end CFSG.LocalAnalysis.GLTheoremA.S171

end
