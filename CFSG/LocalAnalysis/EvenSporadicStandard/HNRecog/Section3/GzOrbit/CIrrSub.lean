module

public import CFSG.LocalAnalysis.EvenSporadicStandard.HNRecog.Section3.GzOrbit.CIrrDef
public import CFSG.LocalAnalysis.EvenSporadicStandard.HNRecog.TwoHSData.ShapeCongr

public section

attribute [-instance] instAddCommGroupOfIsSimpleAddGroupOfIsNilpotent
  instCommGroupOfIsSimpleGroupOfIsNilpotent

namespace CFSG.EvenSporadicStandard.HNRecog.Section3

open CFSG.EvenSporadicStandard.HNRecog

private theorem isElemAbelian_subgroupOf_CIrrSub {G : Type} [Group G] {p : ℕ} {E : Subgroup G}
    (h : CFSG.Open.IsElemAbelian p E) (K : Subgroup G) :
    CFSG.Open.IsElemAbelian p (E.subgroupOf K) := by
  have := h.1
  refine ⟨⟨⟨fun x y => ?_⟩⟩, fun x hx => ?_⟩
  · have hc := congrArg Subtype.val (mul_comm' (⟨((x : K) : G), x.2⟩ : E) ⟨((y : K) : G), y.2⟩)
    apply Subtype.ext
    apply Subtype.ext
    simpa using hc
  · apply Subtype.ext
    rw [Subgroup.coe_pow, Subgroup.coe_one]
    exact h.2 _ hx

theorem isPlusExtraspecial_subgroupOf_baseSub {C : Type} [Group C] {Q : Subgroup C} [Q.Normal]
    (hQ : IsExtraspecialPlusByA5WrTwoWith C Q) (e : C ⧸ Q ≃* A5WrTwo) :
    IsPlusExtraspecial 4 (Q.subgroupOf (baseSub Q e)) := by
  obtain ⟨hext, hcard, E, hEQ, hEab, hEcard⟩ := hQ.plus
  have hEL : E ≤ baseSub Q e := hEQ.trans (le_baseSub e)
  have hι : Q.subgroupOf (baseSub Q e) ≃* Q := Subgroup.subgroupOfEquivOfLe (le_baseSub e)
  refine ⟨?_, ?_, E.subgroupOf (baseSub Q e), ?_, ?_, ?_⟩
  · exact TwoHSData.isExtraspecial_of_mulEquiv hι.symm hext
  · exact (Nat.card_congr hι.toEquiv).trans hcard
  · intro x hx
    exact Subgroup.mem_subgroupOf.mpr (hEQ (Subgroup.mem_subgroupOf.mp hx))
  · exact isElemAbelian_subgroupOf_CIrrSub hEab (baseSub Q e)
  · exact (Nat.card_congr (Subgroup.subgroupOfEquivOfLe hEL).toEquiv).trans hEcard

theorem centralizer_subgroupOf_baseSub_le {C : Type} [Group C] {Q : Subgroup C} [Q.Normal]
    (hQ : IsExtraspecialPlusByA5WrTwoWith C Q) (e : C ⧸ Q ≃* A5WrTwo) :
    Subgroup.centralizer ((Q.subgroupOf (baseSub Q e) : Subgroup ↥(baseSub Q e)) :
      Set ↥(baseSub Q e)) ≤ Q.subgroupOf (baseSub Q e) := by
  intro x hx
  rw [Subgroup.mem_subgroupOf]
  refine hQ.centralizer_le ?_
  rw [Subgroup.mem_centralizer_iff] at hx ⊢
  intro y hy
  have hcomm := hx (⟨y, le_baseSub e hy⟩ : ↥(baseSub Q e)) (Subgroup.mem_subgroupOf.mpr hy)
  exact congrArg Subtype.val hcomm

end CFSG.EvenSporadicStandard.HNRecog.Section3
