module

public import CFSG.LieType.Chevalley.BorelQuotientAbelian
public import CFSG.LieType.Chevalley.BorelSelfNormalizer
public import CFSG.ThirdParty.QiuzhenCFSG.GorensteinWalter.NormalizerSubgroupCyclic

public noncomputable section

namespace CFSG.ClassicalGroups.Orthogonal

open CFSG.Blueprint.Chevalley CFSG.LieType.Chevalley

variable {τ : Tag} {K : Type} [Field K] [Finite K] [CharP K 2]

theorem normalizer_posUnipotentSub_eq_borelSub :
    Subgroup.normalizer (posUnipotentSub τ K : Set (adjointGroup τ K)) = borelSub τ K := by
  change Subgroup.normalizer ((posUnipotent τ K).subgroupOf (adjointGroup τ K) :
    Set (adjointGroup τ K)) = borelSub τ K
  rw [CFSG.GorensteinWalter.normalizer_subgroupOf_eq_subgroupOf_inf_normalizer
    (adjointGroup τ K) (posUnipotent τ K) posUnipotent_le_adjointGroup]
  rw [(CFSG.LieType.Chevalley.borel_self_normalizers τ K).1]

theorem isMulCommutative_normalizer_posUnipotent_quotient_pCore :
    IsMulCommutative
      (↥(Subgroup.normalizer (posUnipotentSub τ K : Set (adjointGroup τ K))) ⧸
        CFSG.pCore 2
          ↥(Subgroup.normalizer (posUnipotentSub τ K : Set (adjointGroup τ K)))) := by
  rw [normalizer_posUnipotentSub_eq_borelSub]
  exact CFSG.LieType.Chevalley.isMulCommutative_borelSub_quotient_pCore

end CFSG.ClassicalGroups.Orthogonal
