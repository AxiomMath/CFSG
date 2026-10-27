module

public import CFSG.LocalAnalysis.EvenSporadicStandard.TwoCo1.PerfAbstract
public import CFSG.LocalAnalysis.EvenSporadicStandard.TwoCo1.PerfData
public import CFSG.Monster.Existence.Compat.Co0Iso
public import CFSG.Monster.VisQuot.Simple

public section

attribute [-instance] instCommGroupOfIsSimpleGroupOfIsNilpotent
  instAddCommGroupOfIsSimpleAddGroupOfIsNilpotent

namespace CFSG.EvenSporadicStandard.TwoCo1

open CFSG.Monster CFSG.Monster.ScalarKernel CFSG.Monster.Visible CFSG.Monster.VisQuot
  CFSG.Monster.Existence.Compat

theorem latticeO_isPerfect :
    Group.IsPerfect latticeO := by
  have : IsSimpleGroup OLq := isSimpleGroup_OLq
  refine isPerfect_of_sq_eq_central (QuotientGroup.mk' (Subgroup.zpowers negOneO))
    (QuotientGroup.mk'_surjective _)
    (Subgroup.mem_center_iff.2 fun g => (negOneO_mul_comm g).symm) negOneO_mul_self
    (QuotientGroup.ker_mk' _) perfJ_mul_self ?_
  rw [show Nat.card (latticeO ⧸ Subgroup.zpowers negOneO) = 4157776806543360000 from natCard_OLq]
  intro hp
  have := hp.eq_one_or_self_of_dvd 2 (by norm_num)
  omega

theorem monsterCo0_isPerfect :
    Group.IsPerfect CFSG.Open.monsterCo0 :=
  haveI := latticeO_isPerfect
  Group.IsPerfect.ofSurjective (f := co0Equiv.toMonoidHom) co0Equiv.surjective

end CFSG.EvenSporadicStandard.TwoCo1
