module

public import CFSG.Mathlib.GroupTheory.Basic
public import CFSG.Foundations.MaxOrderThompsonDefs
import CFSG.Foundations.MaxOrderThompson
public import CFSG.Assembly.Defs

public section

namespace CFSG.RankThreeEvenClassification.Helpers

universe u

@[expose, reducible] noncomputable def maximumAbelianOrder (G : Type u) [Group G] : ℕ :=
  CFSG.maxAbelianOrder G

@[expose, reducible] def MaximumOrderAbelian {G : Type u} [Group G] (subgroup : Subgroup G) : Prop :=
  subgroup ∈ CFSG.maxOrderAbelianFamily G

@[expose, reducible] noncomputable def thompsonOrderSubgroup (G : Type u) [Group G] : Subgroup G :=
  CFSG.orderThompson G

@[expose, reducible] noncomputable def thompsonOrderCenter (G : Type u) [Group G] : Subgroup G :=
  CFSG.orderZJ G

private theorem thompsonOrderSubgroup_eq_canonical (G : Type u) [Group G] :
    thompsonOrderSubgroup G = CFSG.orderThompson G :=
  rfl

private theorem thompsonOrderCenter_eq_canonical (G : Type u) [Group G] :
    thompsonOrderCenter G = CFSG.orderZJ G :=
  rfl

theorem maximumAbelianOrder_bddAbove (G : Type u) [Group G] [Finite G] :
    BddAbove {order : ℕ | ∃ subgroup : Subgroup G, IsMulCommutative subgroup ∧ Nat.card subgroup = order} :=
  CFSG.maxAbelianOrder_bddAbove

theorem exists_maximumOrderAbelian (G : Type u) [Group G] [Finite G] :
    ∃ subgroup : Subgroup G, MaximumOrderAbelian subgroup :=
  CFSG.maxOrderAbelianFamily_nonempty

theorem commutative_card_le_maximumAbelianOrder {G : Type u} [Group G] [Finite G]
    (subgroup : Subgroup G) (hcomm : IsMulCommutative subgroup) :
    Nat.card subgroup ≤ maximumAbelianOrder G :=
  CFSG.card_le_maxAbelianOrder_of_isMulCommutative hcomm

theorem MaximumOrderAbelian.eq_of_le_commutative {G : Type u} [Group G] [Finite G]
    (first second : Subgroup G) (hfirst : MaximumOrderAbelian first)
    (hsecond : IsMulCommutative second) (hle : first ≤ second) : first = second :=
  CFSG.eq_of_mem_maxOrderAbelianFamily_of_le hfirst hsecond hle

theorem commutative_sup_of_centralizes {G : Type u} [Group G]
    (first second : Subgroup G) (hfirst : IsMulCommutative first) (hsecond : IsMulCommutative second)
    (hcentralizes : first ≤ Subgroup.centralizer (second : Set G)) :
    IsMulCommutative (first ⊔ second : Subgroup G) := by
  rw [Subgroup.sup_eq_closure]
  apply CFSG.subgroup_isMulCommutative_closure
  intro firstElement hfirstElement secondElement hsecondElement
  rcases hfirstElement with hfirstElement | hfirstElement <;>
    rcases hsecondElement with hsecondElement | hsecondElement
  · exact congrArg (fun element : first => (element : G))
      (isMulCommutative_iff.mp hfirst ⟨firstElement, hfirstElement⟩ ⟨secondElement, hsecondElement⟩)
  · exact (Subgroup.mem_centralizer_iff.mp (hcentralizes hfirstElement) secondElement hsecondElement).symm
  · exact Subgroup.mem_centralizer_iff.mp (hcentralizes hsecondElement) firstElement hfirstElement
  · exact congrArg (fun element : second => (element : G))
      (isMulCommutative_iff.mp hsecond ⟨firstElement, hfirstElement⟩ ⟨secondElement, hsecondElement⟩)

theorem MaximumOrderAbelian.mem_of_centralizes {G : Type u} [Group G] [Finite G]
    (subgroup : Subgroup G) (hmaximum : MaximumOrderAbelian subgroup)
    (element : G) (hcentral : element ∈ Subgroup.centralizer (subgroup : Set G)) : element ∈ subgroup :=
  CFSG.mem_of_mem_centralizer_of_mem_maxOrderAbelianFamily hmaximum hcentral

theorem maximumOrderAbelian_le_thompson {G : Type u} [Group G]
    (subgroup : Subgroup G) (hmaximum : MaximumOrderAbelian subgroup) : subgroup ≤ thompsonOrderSubgroup G :=
  thompsonOrderSubgroup_eq_canonical G ▸ CFSG.le_orderThompson hmaximum

theorem thompsonOrderCenter_eq_intersection (G : Type u) [Group G] [Finite G] :
    thompsonOrderCenter G =
      ⨅ subgroup : {candidate : Subgroup G // MaximumOrderAbelian candidate}, subgroup.val :=
  (thompsonOrderCenter_eq_canonical G).trans CFSG.orderZJ_eq_iInf_subtype

theorem group_center_le_thompsonOrderCenter (G : Type u) [Group G] [Finite G] :
    Subgroup.center G ≤ thompsonOrderCenter G :=
  thompsonOrderCenter_eq_canonical G ▸ CFSG.center_le_orderZJ_of_finite

theorem thompsonOrderCenter_ne_bot_of_pGroup (G : Type u) [Group G] [Finite G] [Nontrivial G]
    (prime : ℕ) (hprime : prime.Prime) (hpgroup : IsPGroup prime G) : thompsonOrderCenter G ≠ ⊥ :=
  thompsonOrderCenter_eq_canonical G ▸ CFSG.orderZJ_ne_bot_of_isPGroup hprime hpgroup

end CFSG.RankThreeEvenClassification.Helpers
