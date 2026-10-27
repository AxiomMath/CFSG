module

public import CFSG.HardMathSupport.Timmesfeld.SporadicBalance.MonsterEleven
public import CFSG.HardMathSupport.Timmesfeld.SporadicBalance.MonsterTwoBGmat
public import CFSG.HardMathSupport.Timmesfeld.SporadicBalance.BMPairs
public import CFSG.LocalAnalysis.AGLEmbeddingD2.Ambient
public import CFSG.LocalAnalysis.RankTwoShapes.UnitaryFour.Bridge

public section

attribute [-instance] instCommGroupOfIsSimpleGroupOfIsNilpotent
  instAddCommGroupOfIsSimpleAddGroupOfIsNilpotent


namespace CFSG.HardMathSupport.Timmesfeld.SporadicBalance.MonsterElevenFinal

open CFSG.Open CFSG.Monster CFSG.Monster.Generated CFSG.Monster.Existence CFSG.Monster.Griess
  CFSG.HardMathSupport.Timmesfeld.SporadicBalance
  CFSG.HardMathSupport.Timmesfeld.SporadicBalance.MonsterEleven
  CFSG.HardMathSupport.Timmesfeld.SporadicBalance.MonsterTwoBGmat

theorem factorization_Gmat_eleven : (Nat.card Gmat).factorization 11 = 2 := by
  have h : monsterOrder = 11 ^ 2 * 6677829956979445255259999214559593033105408000000000 := by
    norm_num [monsterOrder]
  rw [CFSG.YGroups.Y443.natCard_Gmat_eq_monsterOrder, h,
    Nat.factorization_mul (by norm_num) (by norm_num), Finsupp.add_apply,
    Nat.Prime.factorization_pow (by norm_num), Finsupp.single_eq_same,
    Nat.factorization_eq_zero_of_not_dvd (by norm_num)]

theorem factorization_twoB_eleven : twoBCentralizerOrder.factorization 11 = 1 := by
  have h : twoBCentralizerOrder = 11 * 12682894466030575288320000 := by
    norm_num [twoBCentralizerOrder]
  rw [h, Nat.factorization_mul (by norm_num) (by norm_num), Finsupp.add_apply,
    Nat.Prime.factorization_self (by norm_num), Nat.factorization_eq_zero_of_not_dvd (by norm_num)]

theorem factorization_twoA_eleven : (2 * monsterBabyOrder).factorization 11 = 1 := by
  have h : 2 * monsterBabyOrder = 11 * 755414814768441125668651008000000 := by
    norm_num [monsterBabyOrder]
  rw [h, Nat.factorization_mul (by norm_num) (by norm_num), Finsupp.add_apply,
    Nat.Prime.factorization_self (by norm_num), Nat.factorization_eq_zero_of_not_dvd (by norm_num)]

theorem factorization_centralizer_involution (u : Gmat) (hu : orderOf u = 2) :
    (Nat.card (Subgroup.centralizer ({u} : Set Gmat))).factorization 11 ≤ 1 := by
  rcases CFSG.Monster.Existence.Census.generated_group_two_involution_classes u hu with h | h
  · obtain ⟨c, rfl⟩ := isConj_iff.1 h
    rw [card_centralizer_conj_eq, MonsterElevenLocal.natCard_cent_xGmat, factorization_twoB_eleven]
  · obtain ⟨c, rfl⟩ := isConj_iff.1 h
    rw [card_centralizer_conj_eq, MonsterFiveGmat.natCard_centralizer_tGmat,
      factorization_twoA_eleven]

theorem oPrimeCoreTrivialAt_eleven_Gmat : OPrimeCoreTrivialAt 11 Gmat :=
  oPrimeCoreTrivialAt_eleven_Gmat_of factorization_Gmat_eleven factorization_centralizer_involution
    exists_twoB_Gmat

end CFSG.HardMathSupport.Timmesfeld.SporadicBalance.MonsterElevenFinal

namespace CFSG.HardMathSupport.Timmesfeld.SporadicBalance

theorem sporadicOPrimeHolds_M_eleven : SporadicOPrimeHolds .M 11 :=
  sporadicOPrimeHolds_M_of_gmat MonsterElevenFinal.oPrimeCoreTrivialAt_eleven_Gmat

end CFSG.HardMathSupport.Timmesfeld.SporadicBalance
