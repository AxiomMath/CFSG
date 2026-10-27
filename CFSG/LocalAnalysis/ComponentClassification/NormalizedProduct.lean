module

public import CFSG.Assembly.Defs

public section

namespace CFSG.ComponentClassification.NormalizedProduct

theorem coordinates {G : Type*} [Group G] (normal acting : Subgroup G)
    (hnormalizes : acting ≤ Subgroup.normalizer (normal : Set G))
    (member : G) (hmember : member ∈ normal ⊔ acting) :
    ∃ left ∈ normal, ∃ right ∈ acting, left * right = member := by
  let product := normal ⊔ acting
  let localNormal := normal.subgroupOf product
  let localActing := acting.subgroupOf product
  let : localNormal.Normal := Subgroup.normal_subgroupOf_of_le_normalizer
    (sup_le Subgroup.le_normalizer hnormalizes)
  have hlocal : (⟨member, hmember⟩ : product) ∈ localNormal ⊔ localActing := by
    rw [← Subgroup.subgroupOf_sup (le_sup_left : normal ≤ product) (le_sup_right : acting ≤ product)]
    exact hmember
  obtain ⟨left, hleft, right, hright, heq⟩ := Subgroup.mem_sup_of_normal_left.mp hlocal
  exact ⟨left.val, hleft, right.val, hright, congrArg Subtype.val heq⟩

theorem inf_eq {G : Type*} [Group G] (normal acting ambient : Subgroup G)
    (hnormalizes : acting ≤ Subgroup.normalizer (normal : Set G))
    (hnormal : normal ≤ ambient) (hdisjoint : Disjoint ambient acting) :
    (normal ⊔ acting) ⊓ ambient = normal := by
  apply le_antisymm _ (le_inf le_sup_left hnormal)
  intro member hmember
  obtain ⟨left, hleft, right, hright, heq⟩ := coordinates normal acting hnormalizes member hmember.1
  have hrightAmbient : right ∈ ambient := by
    have hproduct := ambient.mul_mem (ambient.inv_mem (hnormal hleft)) hmember.2
    rw [← heq, inv_mul_cancel_left] at hproduct
    exact hproduct
  have hrightOne : right = 1 := Subgroup.mem_bot.mp (hdisjoint.eq_bot ▸
    (show right ∈ ambient ⊓ acting from ⟨hrightAmbient, hright⟩))
  rw [hrightOne, mul_one] at heq
  exact heq ▸ hleft

end CFSG.ComponentClassification.NormalizedProduct
