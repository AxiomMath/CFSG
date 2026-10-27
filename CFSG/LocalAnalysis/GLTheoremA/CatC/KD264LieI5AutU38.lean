module

public import CFSG.LocalAnalysis.GLTheoremA.CatC.KD264LieInputs
public import CFSG.LocalAnalysis.GLTheoremA.CatC.KD264LieI5AutGen
public import CFSG.StronglyEmbedded.Catalog.Unitary
public import CFSG.RankThree.PartTwo.Sec4.Item413AutU3
public import CFSG.RankThree.PartTwo.Sec20.SimsAsc1411U3
public import CFSG.LocalAnalysis.ComponentClassification.GMS78Basic
public import CFSG.RankThree.PartTwo.Sec13.Item13Models
public import CFSG.RankThree.PartTwo.Sec19.Step1914Tri
public import CFSG.Models.BenderSuzuki
public import CFSG.LocalAnalysis.GLTheoremA.CatC.KD264Parts
public import CFSG.LocalAnalysis.GLTheoremA.S4.Assembly
public import CFSG.LocalAnalysis.GLTheoremA.S4.Inputs
public import CFSG.LocalAnalysis.GLTheoremA.S4S.I145GW
public import CFSG.LocalAnalysis.GLTheoremA.S4S.KData
public import CFSG.Milestones.CL_LIT_Gorenstein_Walter_L_balance
public import CFSG.RankThree.PartTwo.KFacts.KS12MovesSL
public import CFSG.RankThree.PartTwo.Sec20.Alt20
public import CFSG.RankThree.PartTwo.Sec20.OneSteps

public section

namespace CFSG.LocalAnalysis.GLTheoremA.KD264Lie

open CFSG.Open

theorem kd264I5Aut_u38 (e : TauCeti.ValidLieTypeIndex) [Finite (TauCeti.CFSGIndex.lie e).Group]
    (q : TauCeti.PrimePower) (he : e.1 = .twistedA 2 q) (hq : q.card = 8) :
    CFSG.Open.pRank 3 (⊤ : Subgroup (MulAut (TauCeti.CFSGIndex.lie e).Group)) ≤ 3 := by
  obtain ⟨d, hd⟩ := e
  change d = _ at he
  subst he
  obtain ⟨p, k, hpr, hk⟩ := q
  have hq8 : p ^ k = 8 := (TauCeti.PrimePower.card_def ⟨p, k, hpr, hk⟩).symm.trans hq
  obtain ⟨rfl, rfl⟩ := CFSG.LocalAnalysis.GLTheoremA.KD264Lie.I5Aut.prime_pow_eq_eight hpr hk hq8
  haveI : Fact (Nat.Prime 2) := ⟨hpr⟩
  obtain ⟨φ₁⟩ := CFSG.ComponentClassification.GMS78.nonempty_mulEquiv_psu3_of_stated (m := 3)
    (by norm_num) (CFSG.RankThree.PartTwo.Sec20.statedClassicalModel_of_mulEquiv_projSU3
      (m := 3) (by norm_num) (MulEquiv.refl _))
  have hPerf := CFSG.RankThree.PartTwo.Sec13.isPerfect_center_projSU 2 3 (by norm_num)
    (by norm_num) (by norm_num)
  have hsimpP : IsSimpleGroup ↥(CFSG.PGLModel.projSU 3 2 3) :=
    CFSG.RankThree.PartTwo.Sec19.Step1914TriProof.isSimpleGroup_projSU_three_of_ne_two 2 3
      (by norm_num) (by norm_num)
  have hnc : ¬ IsMulCommutative ↥(CFSG.PGLModel.projSU 3 2 3) := by
    intro hc
    have h1 := Subgroup.center_eq_top_iff.mpr hc
    rw [hPerf.2] at h1
    exact bot_ne_top h1
  let e₁ : ↥(CFSG.PGLModel.projSU 3 2 3) ≃* ↥(CFSG.Theory.Comparator.PSU3Model 3) :=
    φ₁.trans (MulEquiv.subgroupCongr (CFSG.Models.benderPSU3Model_eq_psu3 3).symm)
  haveI : IsSimpleGroup ↥(CFSG.Theory.Comparator.PSU3Model 3) := e₁.symm.isSimpleGroup
  have hP : ¬ IsMulCommutative ↥(CFSG.Theory.Comparator.PSU3Model 3) := by
    rintro ⟨hc⟩
    exact hnc ⟨⟨fun a b => e₁.injective (by rw [map_mul, map_mul]; exact hc.comm _ _)⟩⟩
  obtain ⟨eC⟩ : Nonempty ((TauCeti.CFSGIndex.lie ⟨.twistedA 2 ⟨2, 3, hpr, hk⟩, hd⟩).Group ≃*
      ↥(CFSG.Theory.Comparator.PSU3Model 3)) :=
    ⟨CFSG.BenderSuzuki.Catalog.groupEquivPSU3Model (by norm_num) hd hP⟩
  let eS := eC.trans e₁.symm
  have hr := CFSG.RankThree.PartTwo.Sec4.rankAutU3_holds 2 3 (by norm_num) (by norm_num)
    (by norm_num)
  rw [CFSG.SectionRank.pRank_eq_open_pRank_top] at hr
  rw [CFSG.SectionRank.pRank_top_eq_of_mulEquiv (p := 3) (by norm_num) (MulAut.congr eS)]
  exact hr

end CFSG.LocalAnalysis.GLTheoremA.KD264Lie

end
