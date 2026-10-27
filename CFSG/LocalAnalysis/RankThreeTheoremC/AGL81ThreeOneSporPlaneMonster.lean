module

public import CFSG.LocalAnalysis.RankThreeTheoremC.AGL81ThreeOneSporPlaneOf
public import CFSG.HardMathSupport.Dickson.I271.SporGenAux.M13Gmat
public import CFSG.Milestones.FAM_M_finiteness
public import CFSG.RankThree.PartOne.SPOR.OuterM
public import CFSG.Sporadic.Bridge.Y443Relabel

public section

namespace CFSG.LocalAnalysis.RankThreeTheoremC.Hyp111.ThreeOne

open CFSG.Open CFSG.Monster.Generated

theorem glbCore_one_eq_top_Gmat
    (K : Type*) [Group K] [Finite K] (hK : Nonempty (K ≃* Gmat)) (A : Subgroup K)
    (hA : IsElemAbelian 13 A) (hc : Nat.card A = 13 ^ 2) : GLBCore 13 1 A = ⊤ := by
  obtain ⟨φ⟩ := hK
  have hG : (Nat.card Gmat).factorization 13 = 3 := by
    have h : monsterOrder = 13 ^ 3 * 367782168773105542051187940355808264454144000000000 := by
      norm_num [monsterOrder]
    rw [CFSG.YGroups.Y443.natCard_Gmat_eq_monsterOrder, h,
      Nat.factorization_mul (by norm_num) (by norm_num), Finsupp.add_apply,
      Nat.Prime.factorization_pow (by norm_num), Finsupp.single_eq_same,
      Nat.factorization_eq_zero_of_not_dvd (by norm_num)]
  have hCG : CFSG.HardMathSupport.Dickson.I271.CentGen 13 K :=
    (CFSG.HardMathSupport.Dickson.I271.M13.centGen_Gmat_thirteen hG
      CFSG.AGLEmbedding.Norton.GenD13.closure_genD13_eq_top
      CFSG.AGLEmbedding.Norton.Gen13.closure_gen13_eq_top).of_mulEquiv φ.symm
  refine glbCore_one_eq_top_of_gens (by norm_num) (hCG A hA hc) ?_
  rintro g ⟨y, hyA, hy1, hgy⟩
  exact ⟨y, hyA, hy1, hA.2 y hyA, 1, by rw [pow_one]; exact hgy⟩

theorem sporPlaneAt_M :
    SporPlaneAt .M 13 := by
  intro K _ _ hK A hA hc
  obtain ⟨e⟩ := hK
  obtain ⟨b⟩ := CFSG.Sporadic.Bridge.Y443.nonempty_mulEquiv
  have hM := CFSG.Milestones.fam_m_finiteness
  haveI : Finite MonsterY443Derived :=
    Nat.finite_of_card_ne_zero (by rw [hM]; norm_num [monsterOrder])
  have hbij : Function.Bijective CFSG.YGroups.Y443.fM :=
    CFSG.RankThree.PartOne.SPOR.fM_surjective.bijective_of_nat_card_le
      (by rw [hM, CFSG.YGroups.Y443.natCard_Gmat_eq_monsterOrder])
  exact glbCore_one_eq_top_Gmat K ⟨e.trans (b.symm.trans
    (CFSG.Sporadic.Bridge.Y443.commutatorMulEquiv.trans
      (MulEquiv.ofBijective CFSG.YGroups.Y443.fM hbij)))⟩ A hA hc

end CFSG.LocalAnalysis.RankThreeTheoremC.Hyp111.ThreeOne
