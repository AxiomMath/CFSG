module

public import CFSG.LocalAnalysis.AGL81I.Section3.ThreeNineSporGenTh
public import CFSG.HardMathSupport.Dickson.I271.SporGenAux.M13Gmat

public section

namespace CFSG.LocalAnalysis.AGL81I.Section3.SporGen.MThirteen

open CFSG.Open CFSG.Monster.Generated

section Gmat


theorem sporadicCentGen_M_thirteen_gmat : SporadicCentGen 13 .M := by
  intro L _ _ ⟨e⟩ A hA hAc
  obtain ⟨b⟩ := CFSG.Sporadic.Bridge.Y443.nonempty_mulEquiv
  have hM := CFSG.Milestones.fam_m_finiteness
  have : Finite MonsterY443Derived :=
    Nat.finite_of_card_ne_zero (by rw [hM]; norm_num [monsterOrder])
  have hbij : Function.Bijective CFSG.YGroups.Y443.fM :=
    CFSG.RankThree.PartOne.SPOR.fM_surjective.bijective_of_nat_card_le
      (by rw [hM, CFSG.YGroups.Y443.natCard_Gmat_eq_monsterOrder])
  have hG : (Nat.card Gmat).factorization 13 = 3 := by
    have h : monsterOrder = 13 ^ 3 * 367782168773105542051187940355808264454144000000000 := by
      norm_num [monsterOrder]
    rw [CFSG.YGroups.Y443.natCard_Gmat_eq_monsterOrder, h,
      Nat.factorization_mul (by norm_num) (by norm_num), Finsupp.add_apply,
      Nat.Prime.factorization_pow (by norm_num), Finsupp.single_eq_same,
      Nat.factorization_eq_zero_of_not_dvd (by norm_num)]
  have hCG : CFSG.HardMathSupport.Dickson.I271.CentGen 13 L :=
    (CFSG.HardMathSupport.Dickson.I271.M13.centGen_Gmat_thirteen hG
      CFSG.AGLEmbedding.Norton.GenD13.closure_genD13_eq_top
      CFSG.AGLEmbedding.Norton.Gen13.closure_gen13_eq_top).of_mulEquiv
      (e.trans (b.symm.trans (CFSG.Sporadic.Bridge.Y443.commutatorMulEquiv.trans
        (MulEquiv.ofBijective CFSG.YGroups.Y443.fM hbij)))).symm
  rw [eq_top_iff, ← hCG A hA hAc, Subgroup.closure_le]
  rintro σ ⟨a, ha, ha1, hσ⟩
  exact centralizer_le_centGen ha ha1 (Subgroup.mem_centralizer_singleton_iff.2 hσ)

section Five


theorem sporadicGen24_12Five_holds
    : CFSG.LocalAnalysis.AGL81I.Section3.SporadicGen24_12Five :=
  SporGen.ThFive.sporadicGen24_12Five_of_M13 sporadicCentGen_M_thirteen_gmat

end Five

end Gmat

end CFSG.LocalAnalysis.AGL81I.Section3.SporGen.MThirteen
