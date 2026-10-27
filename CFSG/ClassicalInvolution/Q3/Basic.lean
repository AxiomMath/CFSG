module

public import CFSG.ClassicalInvolution.Generic.StepOdd
public import CFSG.ClassicalInvolution.SolvableCase.SL2Three
public import CFSG.ClassicalInvolution.Generic.InductionLocal

public section

namespace CFSG.ClassicalInvolution.Q3

open CFSG.Open CFSG.ClassicalInvolution CFSG.ClassicalInvolution.Generic
open scoped MatrixGroups

variable {Y : Type} [Group Y]

structure IsClassicalMember3 (L : Subgroup Y) (z : Y) : Prop where
  orderOf_eq_two : orderOf z = 2
  mem : z ∈ L
  subnormal : IsSubnormal L (Subgroup.centralizer ({z} : Set Y))
  nonempty_equiv : Nonempty (L ⧸ classicalInvolutionOddCore L ≃* SL(2, ZMod 3))

structure InClass3 (Λ : Set (Subgroup Y)) : Prop where
  nonempty : Λ.Nonempty
  conjInvariant : ConjInvariant Λ
  generated : ⨆ L ∈ Λ, L = ⊤
  classical : ∀ L ∈ Λ, ∃ z : Y, IsClassicalMember3 L z

@[expose] def ExactMembers3 (Λ : Set (Subgroup Y)) : Prop :=
  ∀ L ∈ Λ, classicalInvolutionOddCore L = ⊥

theorem IsClassicalMember3.nonempty_equiv_sl2 {L : Subgroup Y} {z : Y}
    (h : IsClassicalMember3 L z) (hL : classicalInvolutionOddCore L = ⊥) :
    Nonempty (L ≃* SL(2, ZMod 3)) := by
  obtain ⟨e⟩ := h.nonempty_equiv
  exact ⟨((QuotientGroup.quotientMulEquivOfEq hL).trans QuotientGroup.quotientBot).symm.trans e⟩

theorem sl2Three_not_comm (h : ∀ a b : SL(2, ZMod 3), a * b = b * a) : False := by
  have : ¬ ∀ a b : SL(2, ZMod 3), a * b = b * a := by decide +kernel
  exact this h

section Basic

variable {L : Subgroup Y} {z : Y}

theorem IsClassicalMember3.ne_one (h : IsClassicalMember3 L z) : z ≠ 1 := by
  intro hz
  have h2 := h.orderOf_eq_two
  rw [hz, orderOf_one] at h2
  exact absurd h2 (by norm_num)

theorem IsClassicalMember3.not_le_center (h : IsClassicalMember3 L z) :
    ¬ L ≤ Subgroup.center Y := by
  intro hle
  have hcomm : ∀ a b : L, a * b = b * a := fun a b =>
    Subtype.ext (Subgroup.mem_center_iff.mp (hle a.2) b.1).symm
  obtain ⟨e⟩ := h.nonempty_equiv
  have hab : ∀ a b : SL(2, ZMod 3), a * b = b * a := by
    intro a b
    obtain ⟨a', ha'⟩ := QuotientGroup.mk'_surjective (classicalInvolutionOddCore L) (e.symm a)
    obtain ⟨b', hb'⟩ := QuotientGroup.mk'_surjective (classicalInvolutionOddCore L) (e.symm b)
    apply e.symm.injective
    rw [map_mul, map_mul, ← ha', ← hb', ← map_mul, ← map_mul, hcomm a' b']
  exact sl2Three_not_comm hab

theorem IsClassicalMember3.conj (h : IsClassicalMember3 L z) (g : Y) :
    IsClassicalMember3 (conjSub g L) (g * z * g⁻¹) where
  orderOf_eq_two := by rw [orderOf_conj_eq]; exact h.orderOf_eq_two
  mem := conj_mem_conjSub h.mem
  subnormal := isSubnormal_map_conj_centralizer h.subnormal g
  nonempty_equiv := by
    obtain ⟨e'⟩ := h.nonempty_equiv
    let e : L ≃* conjSub g L := L.equivMapOfInjective (MulAut.conj g).toMonoidHom
      (MulAut.conj g).injective
    have hO : (classicalInvolutionOddCore L).map e.toMonoidHom =
        classicalInvolutionOddCore (conjSub g L) :=
      CFSG.ComponentClassification.OddCore.equiv_invariant e
    exact ⟨(QuotientGroup.congr _ _ e hO).symm.trans e'⟩

theorem IsClassicalMember3.card_ge [Finite Y] (h : IsClassicalMember3 L z) :
    24 ≤ Nat.card L := by
  obtain ⟨e⟩ := h.nonempty_equiv
  have h1 : Nat.card SL(2, ZMod 3) ≤ Nat.card L := by
    rw [← Nat.card_congr e.toEquiv]
    exact Nat.card_le_card_of_surjective _ (QuotientGroup.mk'_surjective _)
  rwa [natCard_sl2Three] at h1

theorem IsClassicalMember3.subgroupOf (h : IsClassicalMember3 L z) {H : Subgroup Y}
    (hLH : L ≤ H) : IsClassicalMember3 (L.subgroupOf H) (⟨z, hLH h.mem⟩ : H) := by
  have e : L.subgroupOf H ≃* L := Subgroup.subgroupOfEquivOfLe hLH
  refine ⟨?_, Subgroup.mem_subgroupOf.mpr h.mem, ?_, ?_⟩
  · rw [Subgroup.orderOf_mk]; exact h.orderOf_eq_two
  · have h1 : IsSubnormal L (Subgroup.centralizer ({z} : Set Y) ⊓ H) := by
      have := isSubnormal_inf h.subnormal H
      rwa [inf_eq_left.mpr hLH] at this
    have h2 : (Subgroup.centralizer ({z} : Set Y) ⊓ H).subgroupOf H =
        Subgroup.centralizer ({(⟨z, hLH h.mem⟩ : H)} : Set H) := by
      ext x
      simp only [Subgroup.mem_subgroupOf, Subgroup.mem_inf, Subgroup.mem_centralizer_iff,
        Set.mem_singleton_iff, forall_eq]
      exact ⟨fun hx => Subtype.ext hx.1, fun hx => ⟨congrArg Subtype.val hx, x.2⟩⟩
    rw [← h2]
    exact isSubnormal_subgroupOf h1 H
  · obtain ⟨e'⟩ := h.nonempty_equiv
    have hO : (classicalInvolutionOddCore (L.subgroupOf H)).map e.toMonoidHom =
        classicalInvolutionOddCore L :=
      CFSG.ComponentClassification.OddCore.equiv_invariant e
    exact ⟨(QuotientGroup.congr _ _ e hO).trans e'⟩

end Basic

section OddQuotient

variable [Finite Y]

theorem IsClassicalMember3.map_oddQuotient {L : Subgroup Y} {z : Y}
    (h : IsClassicalMember3 L z) :
    IsClassicalMember3 (L.map (QuotientGroup.mk' (classicalInvolutionOddCore Y)))
      (QuotientGroup.mk' (classicalInvolutionOddCore Y) z) where
  orderOf_eq_two := orderOf_mk_oddCore_eq_two h.orderOf_eq_two
  mem := Subgroup.mem_map_of_mem _ h.mem
  subnormal := by
    rw [← centralizer_map_oddCore h.orderOf_eq_two]
    exact CFSG.ComponentClassification.Components.chain_map _ h.subnormal
  nonempty_equiv := by
    obtain ⟨e⟩ := h.nonempty_equiv
    exact ⟨(CFSG.ComponentClassification.OddKernel.coreQuotientEquiv
      ((QuotientGroup.mk' (classicalInvolutionOddCore Y)).subgroupMap L)
      (MonoidHom.subgroupMap_surjective _ L) (oddCore_restriction_ker_odd L)).symm.trans e⟩

theorem inClass3_oddQuotient {Λ : Set (Subgroup Y)} (hΛ : InClass3 Λ) :
    InClass3 (oddQuotientFamily Λ) where
  nonempty := hΛ.nonempty.image _
  conjInvariant := conjInvariant_oddQuotientFamily hΛ.conjInvariant
  generated := by
    set π := QuotientGroup.mk' (classicalInvolutionOddCore Y)
    have h : ⨆ M ∈ oddQuotientFamily Λ, M = (⨆ L ∈ Λ, L).map π := by
      refine le_antisymm (iSup₂_le fun M hM => ?_) ?_
      · obtain ⟨L, hL, rfl⟩ := hM
        exact Subgroup.map_mono (le_iSup₂ (f := fun (L : Subgroup Y) (_ : L ∈ Λ) => L) L hL)
      · rw [Subgroup.map_le_iff_le_comap]
        refine iSup₂_le fun L hL => ?_
        exact Subgroup.map_le_iff_le_comap.mp (le_iSup₂
          (f := fun (M : Subgroup (Y ⧸ classicalInvolutionOddCore Y))
            (_ : M ∈ oddQuotientFamily Λ) => M) (L.map π) ⟨L, hL, rfl⟩)
    rw [h, hΛ.generated, Subgroup.map_top_of_surjective _ (QuotientGroup.mk'_surjective _)]
  classical := by
    rintro _ ⟨L, hL, rfl⟩
    obtain ⟨z, hz⟩ := hΛ.classical L hL
    exact ⟨_, hz.map_oddQuotient⟩

end OddQuotient

section Local

theorem inClass3_local {Λ : Set (Subgroup Y)} (hΛ : InClass3 Λ) (A : Set Y)
    (hA : (centralizingMembers Λ A).Nonempty) :
    InClass3 (restrictFamily (centralizingMembers Λ A) (centralizingLayer Λ A)) where
  nonempty := by
    obtain ⟨L, hL⟩ := hA
    exact ⟨L.subgroupOf (centralizingLayer Λ A), L, hL, le_centralizingLayer hL, rfl⟩
  conjInvariant := by
    rintro n _ ⟨L, hL, hLH, rfl⟩
    have hn : (n : Y) ∈ Subgroup.centralizer A := centralizingLayer_le_centralizer Λ A n.2
    have hmem : conjSub (n : Y) L ∈ centralizingMembers Λ A := by
      refine ⟨hΛ.conjInvariant _ L hL.1, fun x hx => ?_⟩
      rw [mem_conjSub_iff] at hx
      have hx' := hL.2 hx
      have : x = (n : Y) * ((n : Y)⁻¹ * x * (n : Y)) * (n : Y)⁻¹ := by group
      rw [this]
      exact Subgroup.mul_mem _ (Subgroup.mul_mem _ hn hx') ((Subgroup.inv_mem _) hn)
    exact ⟨conjSub (n : Y) L, hmem, le_centralizingLayer hmem, (conjSub_subgroupOf _ n L)⟩
  generated := by
    set S := centralizingMembers Λ A with hS
    have key := iSup_subgroupOf_self (G := Y) (fun i : S => (i : Subgroup Y))
    have hsup : (⨆ i : S, (i : Subgroup Y)) = centralizingLayer Λ A := by
      rw [centralizingLayer, iSup_subtype']
    rw [hsup] at key
    refine eq_top_iff.mpr (key.symm.le.trans ?_)
    refine iSup_le fun i => ?_
    exact le_iSup₂ (f := fun (L' : Subgroup (centralizingLayer Λ A))
      (_ : L' ∈ restrictFamily S (centralizingLayer Λ A)) => L')
      ((i : Subgroup Y).subgroupOf (centralizingLayer Λ A))
      ⟨i, i.2, le_centralizingLayer i.2, rfl⟩
  classical := by
    rintro _ ⟨L, hL, hLH, rfl⟩
    obtain ⟨z, hz⟩ := hΛ.classical L hL.1
    exact ⟨_, hz.subgroupOf hLH⟩

end Local


section Witness

theorem IsClassicalMember3.of_witness [Finite Y] {z : Y} {J : Subgroup Y} (hz : orderOf z = 2)
    (hzJ : z ∈ J) (hJ : IsSubnormal J (Subgroup.centralizer ({z} : Set Y)))
    (hsol : Group.IsSolvable J) (hw : classicalInvolutionWitness J) :
    IsClassicalMember3 J z := by
  refine ⟨hz, hzJ, hJ, ?_⟩
  have hqs : Group.IsSolvable (J ⧸ classicalInvolutionOddCore J) := inferInstance
  rcases hw with ⟨p, n, hp, hp2, hn, ⟨e⟩⟩ | ⟨hqsimple, -, -⟩
  · have hs : Group.IsSolvable SL(2, GaloisField p n) :=
      Group.isSolvable_of_isSolvable_injective (f := e.symm.toMonoidHom) e.symm.injective
    have hodd : Odd (Nat.card (GaloisField p n)) := by
      rw [GaloisField.card p n hn.ne']
      exact (hp.out.odd_of_ne_two hp2).pow
    have h3 := natCard_eq_three_of_isSolvable_sl2 hodd hs
    obtain ⟨e'⟩ := nonempty_mulEquiv_sl2Three_of_natCard_eq_three h3
    exact ⟨e.trans e'⟩
  · exfalso
    obtain ⟨hperf, hsimple⟩ := hqsimple
    have hnt : Nontrivial (J ⧸ classicalInvolutionOddCore J) := by
      by_contra hcon
      rw [not_nontrivial_iff_subsingleton] at hcon
      have : Subsingleton ((J ⧸ classicalInvolutionOddCore J) ⧸
          Subgroup.center (J ⧸ classicalInvolutionOddCore J)) := inferInstance
      exact (not_nontrivial_iff_subsingleton.mpr this) hsimple.toNontrivial
    exact (Group.IsSolvable.commutator_lt_top_of_nontrivial _).ne hperf

end Witness

end CFSG.ClassicalInvolution.Q3
