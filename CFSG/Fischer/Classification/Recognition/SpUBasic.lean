module

public import CFSG.Fischer.Classification.Recognition.Basic

public section

namespace CFSG.Fischer.Classification.Recognition.SpU

open CFSG.Open
open scoped commutatorElement

variable {X : Type*} [Group X]

theorem le_of_isSubnormal {A B : Subgroup X} (h : IsSubnormal A B) : A ≤ B :=
  h.le

theorem isSubnormal_subgroupOf {A B : Subgroup X} (h : IsSubnormal A B) :
    (A.subgroupOf B).IsSubnormal :=
  h.subgroupOf

theorem commute_of_isComponentOf [Finite X] {K C N : Subgroup X} (hK : IsComponentOf K C)
    (hNC : N ≤ C) (hNn : ∀ c ∈ C, ∀ x ∈ N, c * x * c⁻¹ ∈ N) (hN : Group.IsSolvable N) :
    ∀ k ∈ K, ∀ x ∈ N, k * x = x * k := by
  have hK' : CFSG.IsComponent (K.subgroupOf C) :=
    ⟨CFSG.LocalCores.isQuasisimple_of_mulEquiv (Subgroup.subgroupOfEquivOfLe hK.1).symm
      (localCores_isQuasisimple hK.2.2), isSubnormal_subgroupOf hK.2.1⟩
  have hN'n : (N.subgroupOf C).Normal := by
    rw [Subgroup.normal_subgroupOf_iff hNC]
    exact fun x c hx hc => hNn c hc x hx
  have hN's : Group.IsSolvable (N.subgroupOf C) :=
    Group.isSolvable_of_isSolvable_injective
      (f := (Subgroup.subgroupOfEquivOfLe hNC).toMonoidHom)
      (Subgroup.subgroupOfEquivOfLe hNC).injective
  have h := (CFSG.LocalCores.component_solvable_centralizer hN's hN'n.isSubnormal).1 _ hK'
  intro k hk x hx
  have hc : ⁅(⟨k, hK.1 hk⟩ : C), (⟨x, hNC hx⟩ : C)⁆ ∈ ⁅K.subgroupOf C, N.subgroupOf C⁆ :=
    Subgroup.commutator_mem_commutator hk hx
  rw [h, Subgroup.mem_bot, commutatorElement_eq_one_iff_mul_comm] at hc
  exact congrArg Subtype.val hc

theorem isPGroup_of_pow_four {H : Subgroup X} (h : ∀ x ∈ H, x ^ 4 = 1) : IsPGroup 2 H :=
  fun x => ⟨2, Subtype.ext (by simpa using h x x.2)⟩

theorem not_isComponentOf [Finite X] {K C N : Subgroup X} (hK : IsComponentOf K C)
    (hNC : N ≤ C) (hNn : ∀ c ∈ C, ∀ x ∈ N, c * x * c⁻¹ ∈ N) (hN : ∀ x ∈ N, x ^ 4 = 1)
    (hcent : ∀ c ∈ C, (∀ x ∈ N, c * x = x * c) → c ^ 4 = 1) : False := by
  have : Group.IsNilpotent N := (isPGroup_of_pow_four hN).isNilpotent
  have hcomm := commute_of_isComponentOf hK hNC hNn inferInstance
  have hK4 : ∀ k ∈ K, k ^ 4 = 1 := fun k hk => hcent k (hK.1 hk) (hcomm k hk)
  have : Group.IsNilpotent K := (isPGroup_of_pow_four hK4).isNilpotent
  have : Nontrivial K :=
    CFSG.LocalCores.isQuasisimple_nontrivial (localCores_isQuasisimple hK.2.2)
  have : Group.IsPerfect K := ⟨hK.2.2.1⟩
  exact Group.IsPerfect.not_isNilpotent K inferInstance

end CFSG.Fischer.Classification.Recognition.SpU
