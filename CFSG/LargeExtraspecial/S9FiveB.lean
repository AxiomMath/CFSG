module

public import CFSG.LargeExtraspecial.S9Five
public import CFSG.LargeExtraspecial.S9OneMain

public section

attribute [-instance] instAddCommGroupOfIsSimpleAddGroupOfIsNilpotent
  instCommGroupOfIsSimpleGroupOfIsNilpotent

namespace CFSG.LargeExtraspecial.S9

open Subgroup Module QuadraticMap CFSG.RankThree.OrthogonalInvolutions
open CFSG.LargeExtraspecial.S4 CFSG.LargeExtraspecial.S6 CFSG.LargeExtraspecial.OrthoF2
open scoped commutatorElement

universe u

theorem isExtraspecialPGroup_of_center {P : Type*} [Group P] [Finite P] (hP : IsPGroup 2 P)
    {Z : Subgroup P} (hZ : Nat.card Z = 2) (hZc : Z ≤ Subgroup.center P)
    (hcomm : ∀ x y : P, ⁅x, y⁆ ∈ Z) (hsq : ∀ x : P, x ^ 2 ∈ Z)
    (hcent : ∀ x : P, (∀ y : P, x * y = y * x) → x ∈ Z) (hnab : ∃ x : P, x ∉ Z) :
    IsExtraspecialPGroup 2 P := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have : Fact (IsPGroup 2 P) := ⟨hP⟩
  have hcenter : Subgroup.center P = Z := by
    refine le_antisymm (fun x hx => hcent x fun y => ?_) hZc
    exact (Subgroup.mem_center_iff.mp hx y).symm
  have hcom_le : commutator P ≤ Z := by
    rw [_root_.commutator_def]
    exact Subgroup.commutator_le.mpr fun x _ y _ => hcomm x y
  have hcom : commutator P = Z := by
    refine le_antisymm hcom_le ?_
    obtain ⟨x, hx⟩ := hnab
    have hnc : ¬ ∀ y : P, x * y = y * x := fun h => hx (hcent x h)
    push Not at hnc
    obtain ⟨y, hy⟩ := hnc
    have hg1 : ⁅x, y⁆ ≠ 1 := fun h => hy (commutatorElement_eq_one_iff_mul_comm.mp h)
    have hgZ : ⁅x, y⁆ ∈ Z := hcomm x y
    have hgc : ⁅x, y⁆ ∈ commutator P := by
      rw [_root_.commutator_def]
      exact Subgroup.commutator_mem_commutator (Subgroup.mem_top x) (Subgroup.mem_top y)
    have hzp : Subgroup.zpowers ⁅x, y⁆ = Z := by
      refine Subgroup.eq_of_le_of_card_ge (Subgroup.zpowers_le.mpr hgZ) ?_
      rw [hZ, Nat.card_zpowers]
      have h2 : orderOf ⁅x, y⁆ ∣ 2 := by
        have := orderOf_dvd_natCard (⟨_, hgZ⟩ : Z)
        rwa [hZ, Subgroup.orderOf_mk] at this
      rcases (Nat.dvd_prime Nat.prime_two).mp h2 with h | h
      · exact absurd (orderOf_eq_one_iff.mp h) hg1
      · exact h.ge
    rw [← hzp]
    exact (Subgroup.zpowers_le).mpr hgc
  have hfr : frattini P = Z := by
    refine le_antisymm ?_ (hcom ▸ CFSG.commutator_le_frattini_of_isPGroup (R := P) (p := 2))
    rw [CFSG.frattini_eq_closure_commutator_union_powers (p := 2)]
    refine (Subgroup.closure_le _).mpr ?_
    rintro _ (hx | ⟨y, rfl⟩)
    · exact hcom_le hx
    · exact hsq y
  refine ⟨hP, ?_, ?_, ?_⟩
  · rw [hcom, hcenter]
  · rw [hfr, hcenter]
  · rw [hcenter]
    exact hZ

variable {G : Type u} [Group G] [Finite G] {S : Setting G} {g : G}

theorem mem_zpowers_subtype_iff {t : S.O} (htN : t ∈ Nbar S g t) (x : Nbar S g t) :
    x ∈ zpowers (⟨t, htN⟩ : Nbar S g t) ↔ (x : S.O) ∈ zpowers t := by
  constructor
  · rintro ⟨k, rfl⟩
    exact ⟨k, by simp⟩
  · rintro ⟨k, hk⟩
    exact ⟨k, Subtype.ext (by simpa using hk)⟩

theorem timmesfeld_9_5 (hCE : CentralExtInput.{u}) (H : Hyp4 S g) (hNo : NoA2 S g)
    (C : Cons311 S g) {t : S.O} (ht : t ∈ S.Lbar g) (ht1 : t ≠ 1) (hVQ : ¬ V S g t ≤ S.Qa g)
    (hSp : SpCase H C ht ht1 hVQ) (hA : S.Lbar g ⊓ Nbar S g t ≠ zpowers t) :
    IsExtraspecialPGroup 2 (Nbar S g t) := by
  have haQ := H.conj_mem
  obtain ⟨h, hh, hb⟩ := exists_pair H C ht ht1 hVQ
  have hNQ : NQHyp S g t := timmesfeld_6_5_nqHyp H C ht ht1 hVQ
    (pairGen_of_spCase H C ht ht1 hVQ hSp) (Nbar_eq_N0bar_of_spCase hCE H hNo C ht ht1 hVQ hSp)
    hh hb
  have htN := self_mem_Nbar H ht
  have htt := mul_self_of_mem_Lbar S haQ ht
  have hto : orderOf t = 2 := orderOf_eq_prime (by rw [pow_two]; exact htt) ht1
  refine isExtraspecialPGroup_of_center (isPGroup_Nbar_of_spCase hCE H hNo C ht ht1 hVQ hSp)
    (Z := zpowers (⟨t, htN⟩ : Nbar S g t)) ?_ ?_ ?_ ?_ ?_ ?_
  · rw [Nat.card_zpowers, Subgroup.orderOf_mk, hto]
  · rw [zpowers_le, mem_center_iff]
    intro y
    exact Subtype.ext (commute_of_mem_Rbar haQ (Nbar_le_Rbar y.2))
  · intro x y
    rw [mem_zpowers_subtype_iff, commutatorElement_def]
    exact hNQ.comm x x.2 y y.2
  · intro x
    rw [mem_zpowers_subtype_iff, Subgroup.coe_pow, pow_two]
    exact hNQ.sq x x.2
  · intro x hx
    rw [mem_zpowers_subtype_iff]
    exact mem_zpowers_of_mem_center hCE H hNo C ht ht1 hVQ hSp hh hb x.2 fun y hy =>
      congrArg Subtype.val (hx ⟨y, hy⟩)
  · by_contra hcon
    push Not at hcon
    apply hA
    refine le_antisymm (fun α hα => (mem_zpowers_subtype_iff htN ⟨α, hα.2⟩).mp
      (hcon ⟨α, hα.2⟩)) ?_
    rw [zpowers_le]
    exact ⟨ht, htN⟩

end CFSG.LargeExtraspecial.S9
