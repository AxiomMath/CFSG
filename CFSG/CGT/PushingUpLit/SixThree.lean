module

public import CFSG.CGT.PushingUpLit.Transport
public import CFSG.CGT.PushingUpLit.SixThreeBasic
public import CFSG.GroupTheory.ConjugatePairSubnormality
public import CFSG.RankThree.PartTwo.Sec6.Item612Basic

public section

namespace CFSG.CGT.PushingUpLit

open CFSG CFSG.RankThree.PartOne CFSG.CGT.PushingUp CFSG.Assembly
open scoped commutatorElement Pointwise

namespace SixThree

variable {G : Type} [Group G]

theorem isSylowOf_of_le {R K L : Subgroup G} (hR : IsSylowOf 2 R K) (hRL : R ≤ L) (hLK : L ≤ K) :
    IsSylowOf 2 R L :=
  ⟨hRL, hR.2.1, fun hd => hR.2.2
    (hd.trans ⟨L.relIndex K, (Subgroup.relIndex_mul_relIndex R L K hRL hLK).symm⟩)⟩

theorem le_normalizer_sup_of_isSylowOf [Finite G] {R X : Subgroup G} (hR : IsSylowOf 2 R X)
    {g : G} (hg : g ∈ Subgroup.normalizer (X : Set G)) :
    g ∈ Subgroup.normalizer (R : Set G) ⊔ X := by
  obtain ⟨T, hT⟩ := sylow_of_isSylowOf hR
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  obtain ⟨x, hx, hxg⟩ := CFSG.RankThree.PartTwo.Sec6.exists_inv_mul_mem_normalizer_sylow T hg
  rw [hT, Subgroup.map_subgroupOf_eq_of_le hR.1] at hxg
  have hg' : g = x * (x⁻¹ * g) := by group
  rw [hg']
  exact mul_mem (Subgroup.mem_sup_right hx) (Subgroup.mem_sup_left hxg)

theorem isSubnormal_normalizer_sup {Y R C : Subgroup G} [C.Normal]
    (hYR : Y ≤ Subgroup.normalizer (R : Set G))
    (hsub : (Y.subgroupOf (Subgroup.normalizer (R : Set G))).IsSubnormal)
    (hCY : C ≤ Subgroup.normalizer (Y : Set G)) :
    (Y.subgroupOf (Subgroup.normalizer (R : Set G) ⊔ C)).IsSubnormal := by
  have h1 := isSubnormal_subgroupOf_sup_of_normal (C := C) hYR hsub
  have h2 : (Y.subgroupOf (Y ⊔ C)).IsSubnormal :=
    isSubnormal_subgroupOf_of_le_normalizer le_sup_left (sup_le Subgroup.le_normalizer hCY)
  exact CFSG.GroupTheory.isSubnormal_subgroupOf_trans le_sup_left
    (sup_le_sup_right hYR C) h2 h1

end SixThree

open SixThree

end CFSG.CGT.PushingUpLit
