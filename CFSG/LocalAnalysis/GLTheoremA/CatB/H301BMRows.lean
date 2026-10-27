module

public import CFSG.LocalAnalysis.GLTheoremA.CatB.H301BMRowOf
public import CFSG.LocalAnalysis.GLTheoremA.CatB.H301BMThree
public import CFSG.LocalAnalysis.GLTheoremA.CatB.H301BMFive
public import CFSG.LocalAnalysis.GLTheoremA.CatB.H301BBabyRank
public import CFSG.LocalAnalysis.GLTheoremA.CatB.H1017Co1
public import CFSG.LocalAnalysis.GLTheoremA.CatB.H1017Co1Five
public import CFSG.LocalAnalysis.GLTheoremA.CatB.H1016M3Co1
public import CFSG.LocalAnalysis.GLTheoremA.CatB.H1016M5Co1Cube
public import CFSG.LargeExtraspecial.S12Seven

public section

attribute [-instance] instCommGroupOfIsSimpleGroupOfIsNilpotent
  instAddCommGroupOfIsSimpleAddGroupOfIsNilpotent

namespace CFSG.LocalAnalysis.GLTheoremA.H301B

open CFSG.Open CFSG.Yardstones.Md0ec50421ce4 CFSG.LocalAnalysis.GLTheoremA
  CFSG.LocalAnalysis.GLTheoremA.S8 CFSG.LocalAnalysis.GLTheoremA.H1017 CFSG.Sporadic.Co1Schreier


section RowThree


theorem rowM3_holds : I301BRow .m3 := by
  haveI : Finite ↥GA := CFSG.Sporadic.Co1Schreier.finite_GA
  have hb0 : Nonempty (CFSG.Blueprint.NativeSporadic.Co1 ≃*
      (TauCeti.CFSGIndex.sporadic .Co1).Group) := CFSG.Sporadic.Bridge.Co1.nonempty_mulEquiv
  obtain ⟨b⟩ := hb0
  have hcat : catalogIs ↥GA (sporIs .Co1) :=
    ⟨.sporadic .Co1, rfl, ⟨CFSG.Sporadic.Co1Block.co1MatEquiv.symm.trans b⟩⟩
  have hrk : GLATwoLocalRank 3 ↥GA < 6 := (i1016Co1Fact_holds ↥GA hcat).trans_lt (by norm_num)
  exact i301BRow_of_M (p := 3) (r := 6) (k := 2) rfl rfl rfl (by decide) (by norm_num)
    (fun j hj0 hj2 => by interval_cases j <;> decide) twoRankLe_three_B hrk
    (fun F hF hFc v hv =>
      let ⟨j, hj, hj0⟩ := H1016M3.co1ThreeSixFixFact_holds F hF hFc
      hj0 v (hv j hj))
    (fun F H hF hFc hHF hHc => card_fixed_le_of_hyperplane_three_six hF hFc hHF hHc)

end RowThree

section RowFive


theorem rowM5_of_leB5 (h : TwoRankLe 5 .B 2) : I301BRow .m5 := by
  haveI : Finite ↥GA := CFSG.Sporadic.Co1Schreier.finite_GA
  haveI : Fact (Nat.Prime 5) := ⟨Nat.prime_five⟩
  have hb0 : Nonempty (CFSG.Blueprint.NativeSporadic.Co1 ≃*
      (TauCeti.CFSGIndex.sporadic .Co1).Group) := CFSG.Sporadic.Bridge.Co1.nonempty_mulEquiv
  obtain ⟨b⟩ := hb0
  have hcat : catalogIs ↥GA (sporIs .Co1) :=
    ⟨.sporadic .Co1, rfl, ⟨CFSG.Sporadic.Co1Block.co1MatEquiv.symm.trans b⟩⟩
  have hrk : GLATwoLocalRank 5 ↥GA < 3 := (twoRankLe_five_co1 ↥GA hcat).trans_lt (by norm_num)
  exact i301BRow_of_M (p := 5) (r := 3) (k := 4) rfl rfl rfl (by decide) (by norm_num)
    (fun j hj0 hj4 => by interval_cases j <;> decide) h hrk
    (fun F hF hFc v hv =>
      let ⟨j, hj, hj0⟩ := H1016M5.co1FiveCubeFacts_holds.2 F hF hFc
      hj0 v (hv j hj))
    (fun F H hF hFc hHF hHc => card_fixed_le_of_five_sq (hF.mono hHF)
      (Nat.eq_of_mul_eq_mul_right (by norm_num : 0 < 5) (hHc.trans (hFc.trans (by norm_num)))))

end RowFive

end CFSG.LocalAnalysis.GLTheoremA.H301B

end
