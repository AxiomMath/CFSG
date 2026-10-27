module

public import CFSG.ThirdParty.QiuzhenCFSG.GorensteinWalter.Section2.Bender1970_18

public section

namespace CFSG.GorensteinWalter

universe u

lemma qCoreOf_fittingSubgroupOf_le_qCoreOf
    {G : Type u} [Group G] [Finite G]
    (A : Subgroup G) (q : ℕ) (hq : q.Prime) :
    qCoreOf (_root_.CFSG.fittingSubgroupOf A) q ≤ qCoreOf A q := by
  let F : Subgroup G := _root_.CFSG.fittingSubgroupOf A
  have hQFnormA : IsNormalIn (qCoreOf F q) A := by
    have h := map_characteristic_isNormalIn_of_isNormalIn (H := F) (N := A)
      (pCore q (↥F)) (pCore_characteristic (p := q)) (fittingSubgroupOf_isNormalIn A)
    simpa [qCoreOf] using h
  exact le_qCoreOf_of_normal_isPGroup A (qCoreOf F q) q hQFnormA.1 (by
    rw [Subgroup.normal_subgroupOf_iff_le_normalizer hQFnormA.1]
    exact le_normalizer_of_isNormalIn hQFnormA) (qCoreOf_isPGroup F q)

end CFSG.GorensteinWalter
