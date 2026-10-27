module

public import CFSG.HardMathSupport.Timmesfeld.SporadicBalance.MonsterThreeBCQ
public import CFSG.HardMathSupport.MathTwE6.ExtraspecialComponents
public import CFSG.Assembly.RankThreeEvenDefs
public import CFSG.Fischer.Classification.Recognition.PSU6
public import CFSG.HardMathSupport.Solomon.LocalBalance.Lemma53
public import CFSG.HardMathSupport.Solomon.LocalBalance.Lemma54
public import CFSG.LocalAnalysis.ComponentClassification.ClassicalModelStatedBridge
public import CFSG.LocalAnalysis.RankTwoShapes.UnitaryFour.Bridge
public import CFSG.Quasithin.Vol2.Ch10SecKGA318

public section

set_option linter.unusedSectionVars false

attribute [-instance] instCommGroupOfIsSimpleGroupOfIsNilpotent
  instAddCommGroupOfIsSimpleAddGroupOfIsNilpotent

namespace CFSG.HardMathSupport.Dickson.I271

open CFSG.Open CFSG.AGLEmbedding.Norton.MON5_7 CFSG.Monster.Generated CFSG.Monster.B.Pinned
open CFSG.HardMathSupport.Timmesfeld.SporadicBalance
open CFSG.HardMathSupport.Timmesfeld.SporadicBalance.ThreeBNF (QQ tbL tbL_conj QQ_le_tbL card_QQ
  not_three_pow_21_dvd factorization_tbL le_zpowers_of_le_CQ)
open CFSG.HardMathSupport.Timmesfeld.SporadicBalance.ThreeBNF (SylFact)

section Step0

theorem step0_QQ (hsyl : SylFact) :
    ∀ P : Subgroup Gmat, P ≤ Subgroup.centralizer (QQ : Set Gmat) → IsPGroup 3 P →
      Nat.card P ≤ 3 := by
  have hcardG : Nat.card Gmat = CFSG.Open.monsterOrder :=
    CFSG.YGroups.Y443.natCard_Gmat_eq_monsterOrder
  have hLQ : tbL ≤ Subgroup.normalizer (QQ : Set Gmat) := by
    intro b hb
    rw [Subgroup.mem_normalizer_iff]
    intro x
    constructor
    · intro hx
      have := tbL_conj b⁻¹ (tbL.inv_mem hb) x hx
      simpa using this
    · intro hx
      have := tbL_conj b hb _ hx
      convert this using 1
      group
  have hL3 : (Nat.card Gmat).factorization 3 ≤ (Nat.card tbL).factorization 3 := by
    rw [factorization_tbL hsyl]
    by_contra h
    exact not_three_pow_21_dvd (hcardG ▸ (Nat.Prime.pow_dvd_iff_le_factorization Nat.prime_three
      Nat.card_pos.ne').2 (by omega))
  exact CFSG.HardMathSupport.MathTwE6.card_le_three_of_le_centralizer tbw tbw_pow_three QQ tbL
    hLQ hL3 (le_zpowers_of_le_CQ hsyl)

end Step0

end CFSG.HardMathSupport.Dickson.I271
