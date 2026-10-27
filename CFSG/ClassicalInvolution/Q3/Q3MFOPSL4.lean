module

public import CFSG.ClassicalInvolution.Q3.Q3MFO4Top
public import CFSG.ClassicalInvolution.Q3.Q3PPWireAll

public section

set_option linter.unusedSectionVars false

namespace CFSG.ClassicalInvolution.Q3.Q3PP

open CFSG.Assembly.LowTwoRank CFSG.ClassicalInvolution CFSG.ClassicalInvolution.Generic
  CFSG.ClassicalInvolution.Models CFSG.ClassicalInvolution.Q3 CFSG.ClassicalInvolution.Q3.Q3NM
  CFSG.ClassicalInvolution.Balance
open scoped MatrixGroups


theorem fixedOddFreeFund_psl4 : FixedOddFreeFund (CompData.model .PSL 4) := by
  have hF : Nat.card (GaloisField 3 1) = 3 := natCard_gf3
  have hadmL : StatedLieAdmissible .PSL 4 3 1 :=
    ⟨Nat.prime_three, le_rfl, by norm_num, by decide, by decide⟩
  have hadmS : StatedLieAdmissible .PSp 2 3 1 :=
    ⟨Nat.prime_three, le_rfl, by norm_num, by decide⟩
  have hSL : CFSG.Open.IsQuasisimple SL(4, GaloisField 3 1) :=
    (ModelFacts.modelClauseZero .PSL 4 3 1 Nat.prime_three trivial hadmL).1
  have hSLZ : IsPGroup 2 (Subgroup.center SL(4, GaloisField 3 1)) :=
    (modelFiniteCenterTwoGroup3 .PSL 4 Nat.prime_three trivial hadmL).2
  have hSp : CFSG.Open.IsQuasisimple (StatedSp 2 (GaloisField 3 1)) :=
    (ModelFacts.modelClauseZero .PSp 2 3 1 Nat.prime_three trivial hadmS).1
  have hSpZ : IsPGroup 2 (Subgroup.center (StatedSp 2 (GaloisField 3 1))) :=
    (modelFiniteCenterTwoGroup3 .PSp 2 Nat.prime_three trivial hadmS).2
  intro ρ hρ2 ⟨R, hR, hρR⟩
  have hRl : R ∈ longRootSet (K := GaloisField 3 1) (by norm_num : 2 ≤ 4) :=
    RouteD.fundamentalSubgroups_psl_subset (m := 3) (F := GaloisField 3 1) (by norm_num) hR
  obtain ⟨g₀, rfl⟩ := (mem_longRootSet_iff (K := GaloisField 3 1) (n := 4) (by norm_num)).mp hRl
  exact Q3MFO4.oddCoreIn_fixed_eq_bot_sl4 hF hSL hSLZ hSp hSpZ ρ hρ2 g₀ hρR

theorem mfComp_psl4 : MFComp (CompData.model .PSL 4) := Or.inr fixedOddFreeFund_psl4

end CFSG.ClassicalInvolution.Q3.Q3PP
