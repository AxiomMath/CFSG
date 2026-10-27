module

public import CFSG.LocalAnalysis.SeitzReduction.F4PilotQ2RowCat

public section

namespace CFSG.SeitzReduction.F4Pilot

open Subgroup CFSG.Blueprint CFSG.Blueprint.Chevalley CFSG.LieType.Chevalley CFSG.EvenSmallLie
open CFSG.LieType.Ree (ReeTag)

section Graph

variable {K : Type} [Field K] [Finite K] [CharP K ReeTag.F4.prime]

theorem graphAutF4_mul_self_of_card_eq_two (hK : Nat.card K = 2) :
    graphAutF4 K * graphAutF4 K = 1 := by
  have hK' : Nat.card K = ReeTag.F4.prime ^ 1 := by rw [hK]; rfl
  have h1 := finiteFrobeniusAut_pow_card (K := K) ReeTag.F4 hK'
  rw [pow_one] at h1
  exact (finiteExceptionalAut_mul_self (K := K) ReeTag.F4).trans h1

theorem graphAutF4_graphAutF4_of_card_eq_two (hK : Nat.card K = 2) (x : adjointGroup .F4 K) :
    graphAutF4 K (graphAutF4 K x) = x := by
  have h := congrArg (fun α : MulAut (adjointGroup .F4 K) => α x)
    (graphAutF4_mul_self_of_card_eq_two hK)
  simpa only [MulAut.mul_apply, MulAut.one_apply] using h

theorem graphAutF4_symm_apply_of_card_eq_two (hK : Nat.card K = 2) (x : adjointGroup .F4 K) :
    (graphAutF4 K).symm x = graphAutF4 K x := by
  conv_lhs => rw [← graphAutF4_graphAutF4_of_card_eq_two hK x]
  exact (graphAutF4 K).symm_apply_apply _

theorem trans_graphAutF4_symm_trans_graphAutF4_symm {G : Type} [Group G] {L : Subgroup G}
    (hK : Nat.card K = 2) (e : L ≃* adjointGroup .F4 K) :
    (e.trans (graphAutF4 K).symm).trans (graphAutF4 K).symm = e := by
  ext x
  rw [MulEquiv.trans_apply, MulEquiv.trans_apply, graphAutF4_symm_apply_of_card_eq_two hK,
    graphAutF4_symm_apply_of_card_eq_two hK, graphAutF4_graphAutF4_of_card_eq_two hK]

end Graph

section Pairs

theorem twoKindPairInput_swap {κ κ' : Sp6Kind} (h : TwoKindPairInput κ κ') :
    TwoKindPairInput κ' κ := by
  intro G _ _ L K _ _ _ e t hw X₀ hXJ hcyc hX₀ hκ' hκ
  have hK : Nat.card K = 2 := by rw [hw.card_eq, pow_one]
  refine h G L K (e.trans (graphAutF4 K).symm) t hw X₀ hXJ hcyc hX₀ hκ ?_
  rw [trans_graphAutF4_symm_trans_graphAutF4_symm hK]
  exact hκ'

theorem twoE6PairInput_of_linear6 (h : TwoKindPairInput .linear6 .omegaMinus8) :
    TwoE6PairInput :=
  ⟨h, twoKindPairInput_swap h⟩

end Pairs

end CFSG.SeitzReduction.F4Pilot
