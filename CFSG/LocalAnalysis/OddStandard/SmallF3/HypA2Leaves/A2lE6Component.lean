module

public import CFSG.LocalAnalysis.OddStandard.SmallF3.HypA2Leaves.A2lLeviToral
public import CFSG.LocalAnalysis.ComponentClassification.CatLeafProofE6ToralA5

public section

namespace CFSG.OddStandard.SmallF3.HypA2Leaves

open Subgroup CFSG CFSG.Blueprint CFSG.Blueprint.Chevalley CFSG.LieType CFSG.LieType.Chevalley
  CFSG.LieType.Steinberg CFSG.LieType.Steinberg.Adjoint CFSG.LieType.CurtisTits
  CFSG.Assembly.LowTwoRank CFSG.ComponentClassification CFSG.ComponentClassification.CatLeafProof
  CFSG.LocalAnalysis.ComponentInitial CFSG.LocalAnalysis.ComponentInitial.FourGroupChevalley
open CFSG.ClassicalInvolution.Generic (Commutes)


theorem a2lE6_commutes_levi_hiE6 {K : Type} [Field K] :
    Commutes (subsystemGroup .E6 K e6LeviA5)
      (rootSubgroup .E6 K hiE6 ⊔ rootSubgroup .E6 K (-hiE6)) := by
  have hQmap : (rootGroup (rootOperatorFamily .E6) K hiE6 ⊔
      rootGroup (rootOperatorFamily .E6) K (-hiE6)).map (adjointGroup .E6 K).subtype =
        rootSubgroup .E6 K hiE6 ⊔ rootSubgroup .E6 K (-hiE6) := by
    rw [Subgroup.map_sup, map_subtype_rootGroup _ isRoot_hiE6,
      map_subtype_rootGroup _ (IsRoot.neg isRoot_hiE6)]
  have hcomm' : Commutes (⨆ k, rankOne (adjDatum (rootOperatorFamily .E6) K).rootGroup
      (e6A5Node k)) (rootGroup (rootOperatorFamily .E6) K hiE6 ⊔
        rootGroup (rootOperatorFamily .E6) K (-hiE6)) :=
    ClassicalInvolution.RouteD.commutes_iSup_left.2 fun k =>
      commutes_rootPair_of_noG2 noG2_E6 (isRoot_single _ _) isRoot_hiE6
        (e6A5Node_ne_hiE6 k).1 (e6A5Node_ne_hiE6 k).2 (iform_e6A5Node_hiE6 k)
        (not_isRoot_e6A5Node_hiE6 k).1 (not_isRoot_e6A5Node_hiE6 k).2
  rw [show e6LeviA5 = Set.range e6A5Node from rfl, ← map_subtype_iSup_rankOne e6A5Node, ← hQmap]
  rintro _ ⟨x, hx, rfl⟩ _ ⟨y, hy, rfl⟩
  rw [← map_mul, ← map_mul, hcomm' x hx y hy]

theorem a2lE6_component_toral {K : Type} [Field K] [Finite K] (hK : Nat.card K = 9) :
    CFSG.Assembly.IsComponentOf (subsystemGroup .E6 K e6LeviA5)
      (adjointGroup .E6 K ⊓
        centralizer ({rootDiagUnit .E6 (bitsTuple (K := K) e6BitsA5)} : Set (ModGL .E6 K))) := by
  have hK' : Nat.card K = 3 ^ 2 := by rw [hK]; norm_num
  haveI : CharP K 3 :=
    finite_field_prime_power_characteristic Nat.prime_three (by norm_num) hK'
  have hK2 : ringChar K ≠ 2 := by rw [ringChar.eq K 3]; norm_num
  have hS : rootSpan .E6 K (rootCharKernel (bitsTuple (K := K) e6BitsA5)) =
      subsystemGroup .E6 K e6LeviA5 ⊔ (rootSubgroup .E6 K hiE6 ⊔ rootSubgroup .E6 K (-hiE6)) := by
    rw [rootCharKernel_e6BitsA5 hK2, rootSpan_union_pair, ← subsystemGroup_eq_rootSpan]
  exact a2l_levi_component_toral hK2 (bitsTuple_mem _) hS a2lE6_commutes_levi_hiE6
    (e6_levi_A5_recognition (K := K) (p := 3) (f := 2) Nat.prime_three (by norm_num) hK').1

end CFSG.OddStandard.SmallF3.HypA2Leaves
