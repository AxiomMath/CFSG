module

public import CFSG.LocalAnalysis.GLTheoremA.CatA.I264tTD42Aux
public import CFSG.LocalAnalysis.GLTheoremA.CatA.I264sTD42
public import CFSG.LocalAnalysis.GLTheoremA.CatB.TD4
public import CFSG.LocalAnalysis.AGLEmbedding.KFactProofs.ONanChevOuterD42Link
public import CFSG.RankThree.PartTwo.Sec19.SeitzTrialityQ2Model
public import CFSG.LieType.Simplicity.TrialityD4
public import Certificates.Certificate264001
public import CFSG.HardMathSupport.Seitz.G2Anisotropic.Coordinator.Cover
public import CFSG.HardMathSupport.Seitz.G2Anisotropic.ExceptionsTransport.FamilyProved
public import CFSG.LocalAnalysis.AGLEmbedding.CaseThreeA3pSurvivor
public import CFSG.LocalAnalysis.AGLEmbedding.GapROneBS
public import CFSG.LocalAnalysis.AGLEmbedding.J3InSitu
public import CFSG.LocalAnalysis.AGLEmbedding.J3MSide
public import CFSG.LocalAnalysis.AGLEmbedding.KFactProofs.ONanChevOuterD42Spec
public import CFSG.LocalAnalysis.AGLEmbedding.KFactProofs.ONanSL3CoverGenAssembly
public import CFSG.LocalAnalysis.AGLEmbedding.KFactProofs.ONanSL3FourGenData
public import CFSG.LocalAnalysis.AGLEmbedding.MonomialWeightsOne
public import CFSG.LocalAnalysis.AGLEmbedding.ReeData
public import CFSG.LocalAnalysis.GLTheoremA.CatB.I131T4
public import CFSG.LocalAnalysis.GLTheoremA.CatB.U52
public import CFSG.LocalAnalysis.GLTheoremA.CatC.YS03KD264
public import CFSG.LocalAnalysis.GLTheoremA.S10.Inputs
public import CFSG.LocalAnalysis.GLTheoremA.S4.FullCover.CatalogToCover
public import CFSG.LocalAnalysis.GLTheoremA.S4S.I145GW
public import CFSG.LocalAnalysis.GLTheoremA.S4S.KData
public import CFSG.LocalAnalysis.GLTheoremA.S6.InputsAlt72
public import CFSG.LocalAnalysis.RankThreeTheoremC.D1Frontier3
public import CFSG.LocalAnalysis.SeitzReduction.F4PilotXiCaseLTorus
public import CFSG.Milestones.CL_LIT_Gorenstein_Walter_L_balance
public import CFSG.Quasithin.Recognition.CertTrialityCheckInputs
public import CFSG.RankThree.PartOne.FOCD.G2OddQPlus
public import CFSG.RankThree.PartOne.FOCD.PRank
public import CFSG.RankThree.PartOne.KC.UnitaryDefining
public import CFSG.RankThree.PartOne.N143.LowTwoRankSplit
public import CFSG.RankThree.PartOne.N143.SectionCenter
public import CFSG.RankThree.PartOne.N143.SectionRankBound
public import CFSG.RankThree.PartOne.N143.SectionRankProof
public import CFSG.RankThree.PartOne.N143.SectionRankSplit
public import CFSG.RankThree.PartOne.SEITZ11.G2OddFinal
public import CFSG.RankThree.PartOne.SEITZ7.D4Wire
public import CFSG.RankThree.PartOne.SEITZ7.SlPair
public import CFSG.RankThree.PartOne.SEITZ7.SzPairK
public import CFSG.RankThree.PartTwo.Sec14.Item148Steps
public import CFSG.RankThree.PartTwo.Sec19.SeitzScopeProofExc
public import CFSG.RankThree.PartTwo.Sec19.SeitzScopeProofSec19
public import CFSG.RankThree.PartTwo.Sec19.SeitzScopeProofSec4
public import CFSG.RankThree.PartTwo.Sec19.Step1914Split
public import CFSG.RankThree.PartTwo.Sec4.Item4Res6ProofL364
public import CFSG.RankThree.PartTwo.Sec4.Item4Res6ProofSeitzOther
public import CFSG.RankThree.PartTwo.Sec4.Item4Res6ProofSeitzRest
public import CFSG.RankThree.PartTwo.Sec4.T444.Item434RowsProofSeitzSz

public section

namespace CFSG.LocalAnalysis.GLTheoremA.HTD42

open CFSG.AGLEmbedding.D4Two CFSG.Quasithin CFSG.Open
local notation "Inn" => CFSG.ComponentClassification.OuterAutomorphisms.inner
open CFSG.RankThree.PartTwo.Sec4.Item434D42

theorem core_lineGroup (hZ : Subgroup.center lineGroup = ⊥)
    (hA : Nat.card (MulAut lineGroup) = 3 * 211341312)
    (D : Subgroup (MulAut lineGroup)) (hD : IsElemAbelian 3 D) (hDn : ¬ D ≤ Inn lineGroup) :
    ∃ α ∈ D, α ∉ Inn lineGroup ∧ ∃ F : Subgroup lineGroup, IsElemAbelian 3 F ∧
      Nat.card F = 9 ∧ ∀ x ∈ F, α x = x := by
  obtain ⟨α, hαD, hαI⟩ : ∃ α ∈ D, α ∉ Inn lineGroup := by
    by_contra hcon
    push Not at hcon
    exact hDn fun α hα => hcon α hα
  have hout : ∀ h : lineGroup, α ≠ MulAut.conj h := by
    intro h hαh
    apply hαI
    rw [hαh]
    exact ⟨h, rfl⟩
  exact ⟨α, hαD, hαI, Certificates.certificate264001 hZ hA α hout (hD.2 α hαD)⟩

end CFSG.LocalAnalysis.GLTheoremA.HTD42

namespace CFSG.LocalAnalysis.GLTheoremA

open CFSG.LocalAnalysis.GLTheoremA.HTD42 CFSG.AGLEmbedding.D4Two CFSG.Quasithin
open CFSG.RankThree.PartTwo.Sec4.Item434D42 CFSG.Open
local notation "Inn" => CFSG.ComponentClassification.OuterAutomorphisms.inner

section Main


theorem TD42OuterFix_holds : TD42OuterFix := by
  intro S _ _ hS D hD _ hDn
  obtain ⟨q, hv, hq2, ⟨e⟩⟩ := CFSG.LocalAnalysis.GLTheoremA.CatB.lieIndex_isTD4two hS
  obtain ⟨h1, h2⟩ :=
    primePower_eq_of_card_eq Nat.prime_two (s := 1) (by norm_num) (hq2.trans (by norm_num))
  obtain ⟨hmod, -⟩ := CFSG.AGLEmbedding.ChevOuter.exists_model_equiv ⟨.trialityD4 q, hv⟩ q h1 h2 rfl e
  haveI : IsSimpleGroup S := (CFSG.LieType.Simplicity.fam_3d4_simplicity S 2 1 hmod).2
  obtain ⟨⟨eT⟩, hZ, hA⟩ :=
    CFSG.RankThree.PartTwo.Sec19.lineGroup_facts_of_isoLie q h1 h2 ⟨hv, ⟨e⟩⟩
  let c : MulAut S ≃* MulAut lineGroup := MulAut.congr eT
  have hcomm : ∀ x ∈ D, ∀ y ∈ D, x * y = y * x := by
    intro x hx y hy
    haveI := hD.1
    exact comm_mem_of_isMulCommutative D hx hy
  have hD' : IsElemAbelian 3 (D.map c.toMonoidHom) :=
    isElemAbelian_map_of_forall c.toMonoidHom c.injective hcomm hD.2
  have hD'n : ¬ D.map c.toMonoidHom ≤ Inn lineGroup := by
    intro hle
    apply hDn
    intro α hα
    have hcα : c α ∈ Inn lineGroup := hle (Subgroup.mem_map_of_mem _ hα)
    rw [← CFSG.ComponentClassification.OuterAutomorphisms.inner_map_congr eT] at hcα
    obtain ⟨β, hβ, hβeq⟩ := Subgroup.mem_map.1 hcα
    have : α = β := c.injective hβeq.symm
    rw [this]
    exact hβ
  obtain ⟨α', hα'D, hα'I, F', hF', hF'9, hF'fix⟩ :=
    core_lineGroup hZ hA (D.map c.toMonoidHom) hD' hD'n
  obtain ⟨α, hαD, rfl⟩ := Subgroup.mem_map.1 hα'D
  have hαI : α ∉ Inn S := by
    intro hα
    apply hα'I
    rw [← CFSG.ComponentClassification.OuterAutomorphisms.inner_map_congr eT]
    exact Subgroup.mem_map_of_mem _ hα
  refine ⟨α, hαD, hαI, F'.map (MulEquiv.symm eT).toMonoidHom, ?_, ?_, ?_⟩
  · have hcommF : ∀ x ∈ F', ∀ y ∈ F', x * y = y * x := fun x hx y hy =>
      by haveI := hF'.1; exact comm_mem_of_isMulCommutative F' hx hy
    exact isElemAbelian_map_of_forall (MulEquiv.symm eT).toMonoidHom (MulEquiv.symm eT).injective
      hcommF hF'.2
  · rw [Subgroup.card_map_of_injective (MulEquiv.symm eT).injective, hF'9]
  · intro x hx
    obtain ⟨z, hz, rfl⟩ := Subgroup.mem_map.1 hx
    have hfz := hF'fix z hz
    change eT (α (eT.symm z)) = z at hfz
    have h2 : α (eT.symm z) = eT.symm z := by
      have := congrArg eT.symm hfz
      simpa using this
    exact h2

end Main

end CFSG.LocalAnalysis.GLTheoremA
