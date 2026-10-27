module

public import CFSG.HardMathSupport.Timmesfeld.SporadicBalance.BThirteenCore
public import CFSG.HardMathSupport.Timmesfeld.SporadicBalance.BThirteenCap
public import CFSG.HardMathSupport.Timmesfeld.SporadicBalance.BThirteenFacts
public import CFSG.RankThree.OddKernel.SporadicKernelRestrictionB

public section

set_option linter.unusedSectionVars false

attribute [-instance] instCommGroupOfIsSimpleGroupOfIsNilpotent
  instAddCommGroupOfIsSimpleAddGroupOfIsNilpotent

namespace CFSG.HardMathSupport.Timmesfeld.SporadicBalance

open Subgroup CFSG.Blueprint CFSG.Monster.GMS CFSG.Monster.Existence
  CFSG.EvenSporadicStandard.HypOne.BabyHyp.B68


theorem babyInv_zero_of_rank_1860 {X : NativeSporadic.B} (hX : orderOf X = 2)
    (hr : Matrix.rank (X.val.val - 1) = 1860) : BabyInv 0 X := by
  have hfin : Finite NativeSporadic.B := CFSG.Monster.B.Pinned.finite_B
  obtain ⟨-, -, -, -, -, -, -, -, -, hB, -, b1, b0, b5, b3⟩ :=
    CFSG.Monster.B.CTIB.native_four_involution_classes
  obtain ⟨i, ⟨hi, hc⟩, -⟩ := hB X hX
  have hrk := rank_sub_one_of_isConj hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hi
  rcases hi with rfl | rfl | rfl | rfl
  · have hconv : CFSG.Monster.B.CTIB.iotaEquiv.symm (CFSG.Monster.B.CTIB.rs 1) = babyRep 1 := by
      unfold babyRep
      rfl
    rw [hconv] at hc
    exact Inv.of_isConj babyInv_zero_babyRep_one hc.symm
  · rw [hr, b0] at hrk
    exact absurd hrk (by norm_num)
  · rw [hr, b5] at hrk
    exact absurd hrk (by norm_num)
  · rw [hr, b3] at hrk
    exact absurd hrk (by norm_num)

theorem bThirteenOddCore_holds : BThirteenOddCore := by
  intro x hx K hKx hKn hodd h13
  have hfin : Finite NativeSporadic.B := CFSG.Monster.B.Pinned.finite_B
  have hp2 : ¬ 13 ^ 2 ∣ Nat.card NativeSporadic.B := by
    rw [CFSG.RankThree.OddKernel.card_B_eq]
    norm_num
  have P := b13_parts
  have inv : ∀ {t : NativeSporadic.B}, t * t = 1 → t ≠ 1 →
      Matrix.rank (CFSG.Monster.B.bMat t - 1) = 1860 → BabyInv 0 t := by
    intro t h1 h2 h3
    have h2' : orderOf t = 2 := by
      have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
      exact orderOf_eq_prime (by rw [pow_two]; exact h1) h2
    exact babyInv_zero_of_rank_1860 h2' h3
  refine BThirteen.eq_bot_of_conj hp2 P.order_x hx ?_ hKx hKn hodd h13
  intro K hKx hKn hodd h13
  exact BThirteen.eq_bot_of_data (N := babyCentOrder) (sz := babyOrbitSize)
    BThirteen.arith13_baby babyTableIV BThirteen.cap13_baby P.order_x
    (inv P.mul_self_t1 P.ne_one_t1 P.rank_t1) (inv P.mul_self_t2 P.ne_one_t2 P.rank_t2)
    (inv P.mul_self_t4 P.ne_one_t4 P.rank_t4) (inv P.mul_self_t5 P.ne_one_t5 P.rank_t5)
    P.comm_t1 P.comm_t2 P.comm_t4 P.comm_t5 P.comm_t1_t5 P.ne_t5_t1 P.order_t1_t2 P.conj_g
    P.comm_g_t1 P.comm_g_t2 P.comm_g_t5 P.w12 P.w14 P.w15 P.w24 P.w25 P.w45 hKx hKn hodd h13

end CFSG.HardMathSupport.Timmesfeld.SporadicBalance
