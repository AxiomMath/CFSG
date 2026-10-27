module

public import CFSG.LocalAnalysis.GLTheoremA.CatB.H1016M3AssemblyInv
public import CFSG.LocalAnalysis.GLTheoremA.CatB.H1016M3TwoB
public import CFSG.Milestones.CL_LIT_Monster_existence_Griess_Conway
public import CFSG.Sporadic.Bridge.MonsterModelsGriess

public section

attribute [-instance] instCommGroupOfIsSimpleGroupOfIsNilpotent
  instAddCommGroupOfIsSimpleAddGroupOfIsNilpotent

namespace CFSG.LocalAnalysis.GLTheoremA.H1017.H1016M3

open CFSG.Open CFSG.Monster.Existence CFSG.HardMathSupport.Timmesfeld.SporadicBalance
  CFSG.LocalAnalysis.GLTheoremA.H1017.H1016M5


theorem i1016M3Fact_of_parts (ha : TwoLocalRankCriterion) (hco1 : Co1ThreeRankFact)
    (hfix : Co1ThreeSixFixFact) (hbaby : BabyThreeRankFact) : I1016M3Fact := by
  have hE : MonsterExistenceStatement MGriess :=
    CFSG.Milestones.cl_lit_monster_existence_griess_conway
  haveI : Finite MGriess := hE.1.1
  have hM : GLATwoLocalRank 3 MGriess ≤ 6 :=
    ha MGriess 3 6 2 Nat.prime_three (by norm_num)
      (fun j hj0 hj2 => by interval_cases j; decide) (card_le_of_involution_three hE hco1 hbaby)
      (false_of_four_three hE card_nativeB hfix)
  obtain ⟨e₀⟩ := CFSG.Blueprint.NativeSporadic.MonsterModel.iso_griess_y443Derived
  obtain ⟨e₁⟩ := CFSG.Blueprint.NativeSporadic.MonsterModel.iso_y443Derived_tauCeti
  intro K _ _ hK
  obtain ⟨i, hi, ⟨φ⟩⟩ := hK
  simp only [S8.sporIs] at hi
  subst hi
  have ψ : K ≃* MGriess := φ.trans (e₀.trans e₁).symm
  have h := CFSG.HardMathSupport.Timmesfeld.Tables.Census.glaTwoLocalRank_congr (p := 3)
    (by norm_num) ψ
  omega

end CFSG.LocalAnalysis.GLTheoremA.H1017.H1016M3
