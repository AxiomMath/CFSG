module

public import CFSG.HardMathSupport.Dickson.I271.SporGenR3Aux.TabMThreeADefs
public import CFSG.HardMathSupport.Dickson.I271.SporGenR3Aux.TabMThreeACover
public import CFSG.HardMathSupport.Dickson.I271.SporGenR3Aux.TabMThreeAFi24

public section

attribute [-instance] instCommGroupOfIsSimpleGroupOfIsNilpotent
  instAddCommGroupOfIsSimpleAddGroupOfIsNilpotent

namespace CFSG.HardMathSupport.Dickson.I271.TabMThreeA

open CFSG.Monster CFSG.Monster.Generated CFSG.Monster.Griess CFSG.Monster.GMS
  CFSG.Monster.Existence CFSG.YGroups CFSG.YGroups.Y443 CFSG.Open
open CFSG.Certificates.CosetEnumeration (evalWord evalWord_nil evalWord_cons evalWord_append)

theorem tGriess_mul_refT_three_mem_range
    (hG : Gmat = AutO) : tGriess * refT hG 3 ∈ (yMc hG).range := by
  refine ⟨yWordC (yF0 ++ [3]) (by decide) (by decide), ?_⟩
  rw [yMc_yWordC, evalWord_append, map_mul, yM_yF0 hG, evalWord_cons, evalWord_nil, mul_one,
    yM_yGen hG (by norm_num)]

theorem ker_yMc_le
    (hG : Gmat = AutO) : (yMc hG).ker ≤ yJ.ker := by
  haveI := CFSG.Sporadic.Fi24.isSimpleGroup_J
  haveI := card_ker_yJ_le.1
  have hmem := tGriess_mul_refT_three_mem_range hG
  have hne : tGriess * refT hG 3 ≠ 1 := by
    intro h
    have hc := (isConj_tGriess_refT_three hG).2
    rw [h, isConj_one_left] at hc
    have h2 := orderOf_tGriess
    rw [hc, orderOf_one] at h2
    omega
  have hΦ : (yMc hG).range ≠ ⊥ := by
    intro h
    rw [h, Subgroup.mem_bot] at hmem
    exact hne hmem
  exact ker_le_ker_of_isSimpleGroup
    (commutator_eq_top_of_commutator_eq y442_commutator_commutator) (yMc hG) yJ yJ_surjective
    card_ker_yJ_le.2 hΦ

end CFSG.HardMathSupport.Dickson.I271.TabMThreeA
