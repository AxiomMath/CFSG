module

public import CFSG.ClassicalInvolution.Q3.TL4OddKey
public import CFSG.ClassicalInvolution.Q3.Q3CHHyp51

public section

namespace CFSG.ClassicalInvolution.Q3.TL4

open CFSG CFSG.Open CFSG.ClassicalInvolution CFSG.ClassicalInvolution.Generic
open CFSG.ClassicalInvolution.Asc77 CFSG.ClassicalInvolution.Disconnected.AschTight
open CFSG.ClassicalInvolution.Balance CFSG.ClassicalInvolution.Balance.Bootstrap
open CFSG.ClassicalInvolution.Q3.Q3NL (IsSectionMember3)
open CFSG.ClassicalInvolution.Q3.Q3CH

section Member

variable {Y : Type} [Group Y] [Finite Y]

omit [Finite Y] in
theorem isSectionMember3_map {C : Subgroup Y} {L : Subgroup ↥C} {z : ↥C}
    (h : IsClassicalMember3 L z) : IsSectionMember3 C (L.map C.subtype) (z : Y) where
  le := Subgroup.map_subtype_le L
  orderOf_eq_two := by rw [Subgroup.orderOf_coe]; exact h.orderOf_eq_two
  mem := Subgroup.mem_map_of_mem _ h.mem
  subnormal := by
    have h1 : IsSubnormal (L.map C.subtype)
        ((Subgroup.centralizer ({z} : Set ↥C)).map C.subtype) :=
      CFSG.ComponentClassification.Components.chain_map C.subtype h.subnormal
    have h2 : (Subgroup.centralizer ({z} : Set ↥C)).map C.subtype =
        Subgroup.centralizer ({(z : Y)} : Set Y) ⊓ C := by
      have := subgroupOf_centralizer_inf (z := (z : Y)) z.2
      rw [Subtype.coe_eta] at this
      rw [← this, Subgroup.map_subgroupOf_eq_of_le inf_le_right]
    rwa [h2] at h1
  nonempty_equiv := by
    obtain ⟨e'⟩ := h.nonempty_equiv
    let e : L ≃* L.map C.subtype := L.equivMapOfInjective C.subtype C.subtype_injective
    have hO : (classicalInvolutionOddCore L).map e.toMonoidHom =
        classicalInvolutionOddCore (L.map C.subtype) :=
      CFSG.ComponentClassification.OddCore.equiv_invariant e
    exact ⟨(QuotientGroup.congr _ _ e hO).symm.trans e'⟩

end Member

section Good

variable {Y : Type} [Group Y] [Finite Y]


theorem movedOddFree_oddQuot_of_member (hBelow : CIT3Below (Nat.card Y))
    (hZ : Subgroup.center Y = ⊥) {u t : Y} (hu1 : u ≠ 1)
    (htu : t ∈ Subgroup.centralizer ({u} : Set Y)) {K : Subgroup Y}
    (hK : IsSectionMember3 (Subgroup.centralizer ({u} : Set Y)) K t) :
    ∀ L : Subgroup (OddQuot u), CFSG.IsComponent L →
      oddQuotMk u ⟨t, htu⟩ ∈ Subgroup.normalizer (L : Set (OddQuot u)) →
      (∃ y ∈ L, oddQuotMk u ⟨t, htu⟩ * y ≠ y * oddQuotMk u ⟨t, htu⟩) →
      Q3NM.AutOddFreeOn ↥L (IsInducedAut L (oddQuotMk u ⟨t, htu⟩)) := by
  intro L hL _ hmv
  have hsnc : ¬ ({u} : Set Y) ⊆ Subgroup.center Y := fun h => hu1 (by
    have h1 : u ∈ Subgroup.center Y := h (Set.mem_singleton u)
    rwa [hZ, Subgroup.mem_bot] at h1)
  have hΦ := secData3_sFamily3 hK hK hK
  obtain ⟨ι, -, ⟨D⟩⟩ := lieSystemMod3_of_secData3 hΦ hBelow hsnc
  obtain ⟨j, hj⟩ := exists_modOdd_le_secComp hΦ D (mem_sFamily3_one u K K K)
  have htj : oddQuotMk u ⟨t, htu⟩ ∈ secComp hΦ D j := hj (oddQuotMk_mem_modOdd hK.mem htu)
  have hLj := eq_secComp_of_not_commute hΦ D htj hL hmv
  have hle : modOdd u K ≤ L := hLj ▸ hj
  obtain ⟨htL, K', hK'⟩ := exists_classical_center hK htu hle hmv
  have hrow : Q3NM.AutOddFreeOn ↥L (ClassicalInner ↥L) := by
    have hk := kind_of_isComponent_secComp hΦ D (hLj ▸ hL)
    subst hLj
    exact autOddFreeOn_range m11OddAutInner3 hk _
      (Q3CH.ker_comp_le_center D _ (sectionQuotientHom_injective _) j)
      (Q3CH.exists_comp_ne_one D _ (sectionQuotientHom_injective _) j)
  refine hrow.mono fun σ hσ => ⟨⟨oddQuotMk u ⟨t, htu⟩, htL⟩, ?_, K', hK'⟩
  refine MulEquiv.ext fun y => Subtype.ext ?_
  exact (hσ y).symm

theorem secMovedOddFree_of_good {n : ℕ} {R : Subgroup Y} {S : Sylow 2 R} {t : Y}
    (hL : TightLargeHypR 3 n Y R S t) {u : Y} (hu1 : u ≠ 1)
    (htu : t ∈ Subgroup.centralizer ({u} : Set Y))
    (hRu : R ≤ Subgroup.centralizer ({u} : Set Y))
    (ht : (⟨t, htu⟩ : Subgroup.centralizer ({u} : Set Y)) ∈ secH R u)
    (hgood : GoodThreeElement (secR R u)
      (QuotientGroup.mk' (classicalInvolutionOddCore ↥(secH R u)) ⟨⟨t, htu⟩, ht⟩)) :
    SecMovedOddFree R u
      (QuotientGroup.mk' (classicalInvolutionOddCore ↥(secH R u)) ⟨⟨t, htu⟩, ht⟩) := by
  have hd := hL.datum
  have hSu : (S : Subgroup R).map R.subtype ≤ Subgroup.centralizer ({u} : Set Y) :=
    (Subgroup.map_subtype_le _).trans hRu
  obtain ⟨S₁, hd₁, ⟨e₁⟩⟩ := hd.restrict hSu
  have hq8 : Nonempty (↥(S₁ : Subgroup (R.subgroupOf (Subgroup.centralizer ({u} : Set Y)))) ≃*
      QuaternionGroup 2) := ⟨e₁.trans (tightClsR_three_iff.mp hL.cls).1.some⟩
  obtain ⟨ht', S', hd', -, -⟩ := hd₁.exists_cls_subnormalClosure hq8
  have hgC := hd₁.good_of_subnormalClosure hd' hgood
  obtain ⟨L, -, hLC⟩ := tightHasLift_of_good hd₁ hgC
  have hK := isSectionMember3_map hLC
  have hBelow : CIT3Below (Nat.card Y) := by
    rw [hL.card]
    exact hL.below
  exact movedOddFree_sub_of_quot (isSubnormal_subnormalClosure _) ht
    (movedOddFree_oddQuot_of_member hBelow hL.center hu1 htu hK)

end Good

end CFSG.ClassicalInvolution.Q3.TL4
