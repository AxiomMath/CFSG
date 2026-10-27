module

public import CFSG.LocalAnalysis.RankThreeEvenClassification.CharacteristicLocal
public import CFSG.Assembly.Subnormal

public section

open CFSG.Open
open CFSG.Open

namespace CFSG.RankThreeEvenClassification.Helpers

universe u

theorem pCoreOf_isPGroup {G : Type u} [Group G] (prime : ℕ) (subgroup : Subgroup G) :
    IsPGroup prime (pCoreOf prime subgroup) := by
  exact (pCore_isPGroup subgroup prime).of_equiv
    ((pCore prime subgroup).equivMapOfInjective subgroup.subtype subgroup.subtype_injective)

theorem pCoreOf_normal_of_normal {G : Type u} [Group G] (prime : ℕ)
    (subgroup : Subgroup G) (hnormal : subgroup.Normal) : (pCoreOf prime subgroup).Normal := by
  have : subgroup.Normal := hnormal
  have : (pCore prime subgroup).Characteristic := pCore_characteristic subgroup prime
  exact ConjAct.normal_of_characteristic_of_normal

theorem pCoreOf_subgroupOf {G : Type u} [Group G] (prime : ℕ)
    (smaller larger : Subgroup G) (hle : smaller ≤ larger) :
    (pCoreOf prime smaller).subgroupOf larger = pCoreOf prime (smaller.subgroupOf larger) := by
  apply Subgroup.map_injective larger.subtype_injective
  rw [Subgroup.map_subgroupOf_eq_of_le ((pCoreOf_le prime smaller).trans hle)]
  unfold pCoreOf
  rw [Subgroup.map_map]
  have hcomposition : larger.subtype.comp (smaller.subgroupOf larger).subtype =
      smaller.subtype.comp (Subgroup.subgroupOfEquivOfLe hle).toMonoidHom := by
    ext element
    rfl
  rw [hcomposition, ← Subgroup.map_map, pCore_map_equiv]

theorem pCoreOf_normal_subgroupOf {G : Type u} [Group G] (prime : ℕ)
    (smaller larger : Subgroup G) (hle : smaller ≤ larger)
    (hnormal : (smaller.subgroupOf larger).Normal) :
    ((pCoreOf prime smaller).subgroupOf larger).Normal := by
  rw [pCoreOf_subgroupOf prime smaller larger hle]
  exact pCoreOf_normal_of_normal prime (smaller.subgroupOf larger) hnormal

theorem pCoreOf_le_pCoreOf_of_normal {G : Type u} [Group G] (prime : ℕ)
    (smaller larger : Subgroup G) (hle : smaller ≤ larger)
    (hnormal : (smaller.subgroupOf larger).Normal) :
    pCoreOf prime smaller ≤ pCoreOf prime larger := by
  exact normal_pSubgroup_le_pCoreOf prime (pCoreOf prime smaller) larger
    ((pCoreOf_le prime smaller).trans hle)
    (pCoreOf_normal_subgroupOf prime smaller larger hle hnormal)
    (pCoreOf_isPGroup prime smaller)

theorem subnormal_le {G : Type u} [Group G] {smaller larger : Subgroup G}
    (hsubnormal : IsSubnormal smaller larger) : smaller ≤ larger :=
  hsubnormal.le

theorem pCoreOf_le_pCoreOf_of_subnormal {G : Type u} [Group G] (prime : ℕ)
    {smaller larger : Subgroup G} (hsubnormal : IsSubnormal smaller larger) :
    pCoreOf prime smaller ≤ pCoreOf prime larger := by
  induction hsubnormal with
  | refl => exact le_rfl
  | step hle hnormal _ ih =>
    exact (pCoreOf_le_pCoreOf_of_normal prime _ _ hle hnormal).trans ih

theorem subnormal_pSubgroup_le_pCoreOf {G : Type u} [Group G] (prime : ℕ)
    {smaller larger : Subgroup G} (hsubnormal : IsSubnormal smaller larger)
    (hpgroup : IsPGroup prime smaller) : smaller ≤ pCoreOf prime larger := by
  have hself : (smaller.subgroupOf smaller).Normal := by
    rw [Subgroup.subgroupOf_self]
    infer_instance
  exact (normal_pSubgroup_le_pCoreOf prime smaller smaller le_rfl hself hpgroup).trans
    (pCoreOf_le_pCoreOf_of_subnormal prime hsubnormal)

theorem charTwoType_subnormal_local_odd_subgroup_eq_bot {G : Type u} [Group G]
    (hchar : IsCharTwoType G) (localSubgroup : Subgroup G) (hlocal : IsTwoLocal localSubgroup)
    (prime : ℕ) (hprime : prime.Prime) (hodd : prime ≠ 2) (subgroup : Subgroup G)
    (hsubnormal : IsSubnormal subgroup localSubgroup) (hpgroup : IsPGroup prime subgroup) :
    subgroup = ⊥ := by
  have hcore := subnormal_pSubgroup_le_pCoreOf prime hsubnormal hpgroup
  rw [charTwoType_local_odd_coreOf_eq_bot hchar localSubgroup hlocal prime hprime hodd] at hcore
  exact le_antisymm hcore bot_le

end CFSG.RankThreeEvenClassification.Helpers
