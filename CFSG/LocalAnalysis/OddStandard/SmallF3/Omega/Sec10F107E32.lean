module

public import CFSG.LocalAnalysis.OddStandard.SmallF3.Omega.Sec10F107Frame2
public import CFSG.LocalAnalysis.OddStandard.SmallF3.Omega.Sec10FrameB0
public import CFSG.LocalAnalysis.OddStandard.SmallF3.Omega.Sec10AutAbP
public import CFSG.GroupTheory.ElemAbelianClosure

public section

namespace CFSG.OddStandard.SmallF3.Omega

open Subgroup CFSG.Blueprint CFSG.GH74.KGroups CFSG.ComponentClassification.CatFactsSmall.PSp43
  CFSG.ComponentClassification.GSThmB

local notation "P45" => Equiv.Perm (Fin 45)

namespace PspFrame

variable {G : Type} [Group G] [Finite G] {L : Subgroup G} {F : PspFrame L} {t : G}
  {S : Subgroup G} (h : Setup107 L t S)

namespace Setup107

include h

theorem imgS_mono {X Y : Subgroup G} (hXY : X ≤ Y) : F.imgS S X ≤ F.imgS S Y := by
  intro p hp
  obtain ⟨x, hx, hxS, rfl⟩ := (F.mem_imgS h.S_le_N).1 hp
  exact (F.mem_imgS h.S_le_N).2 ⟨x, hXY hx, hxS, rfl⟩

section Certs

variable
  (hFP : F.img (S ⊓ L) = QT0.originalSubgroup)

include hFP

theorem T0_le_imgS : QT0.originalSubgroup ≤ F.imgS S S := by
  rw [← hFP, ← h.imgS_eq_img (F := F) (X := S ⊓ L) inf_le_right inf_le_left]
  exact h.imgS_mono inf_le_left

theorem B0_le_imgS : B0 ≤ F.imgS S S := B0_le_T0.trans (h.T0_le_imgS hFP)

theorem secA_eq_pre : secA t S L = F.pre B0 ⊔ zpowers t := by
  show JElem (S ⊓ L) ⊔ zpowers t = _
  rw [F.jElem_eq hFP inf_le_right]

theorem secA_eq : secA t S L = F.preS S B0 := by
  rw [h.secA_eq_pre hFP, ← h.preS_eq_sup (by rw [hFP]; exact B0_le_T0)]

theorem secA_le : secA t S L ≤ S := by
  rw [h.secA_eq hFP]
  exact h.preS_le B0

theorem card_secA : Nat.card (secA t S L) = 2 ^ 5 := by
  rw [h.secA_eq hFP, h.card_preS (h.B0_le_imgS hFP), card_B0]
  norm_num

theorem isElemAbelian_secA : CFSG.Open.IsElemAbelian 2 (secA t S L) := by
  rw [h.secA_eq_pre hFP]
  refine CFSG.Open.IsElemAbelian.sup_of_commute F.isElemAbelian_pre_B0
    (CFSG.Open.isElemAbelian_zpowers (by rw [pow_two]; exact h.t_sq)) ?_
  intro a ha b hb
  have hL : a ∈ L := F.pre_le B0 ha
  rcases (mem_zpowers_of_sq h.t_sq).1 hb with hb1 | hb1
  · rw [hb1, mul_one, one_mul]
  · rw [hb1]
    exact Subgroup.mem_centralizer_iff.1 h.t_cent a hL

theorem isElemAb2_secA : IsElemAb2 (secA t S L) 5 :=
  ⟨h.isElemAbelian_secA hFP, h.card_secA hFP⟩

omit hFP in
theorem card_imgS_le {X : Subgroup G} (hXS : X ≤ S) (hcomm : ∀ a ∈ X, ∀ b ∈ X, a * b = b * a) :
    Nat.card (F.imgS S X) ≤ 16 :=
  card_abelian_two_le_16_A0 (h.imgS_le_A X) (h.isPGroup_imgS hXS)
    (isMulCommutative_iff_of_setLike.2 (h.comm_imgS hcomm))

omit hFP in
theorem card_le_32 (F : PspFrame L) {X : Subgroup G} (hXS : X ≤ S)
    (hXe : CFSG.Open.IsElemAbelian 2 X) : Nat.card X ≤ 32 := by
  have h16 := h.card_imgS_le (F := F) hXS fun a ha b hb => hXe.comm ha hb
  by_cases ht : t ∈ X
  · rw [h.card_of_t_mem (F := F) hXS ht]
    omega
  · rw [h.card_of_t_not_mem (F := F) hXS ht]
    omega

omit hFP in
theorem e32_data {X : Subgroup G} (hXS : X ≤ S) (hX : IsElemAb2 X 5) :
    t ∈ X ∧ Nat.card (F.imgS S X) = 16 ∧ F.preS S (F.imgS S X) = X ∧
      (∀ a ∈ F.imgS S X, ∀ b ∈ F.imgS S X, a * b = b * a) ∧ ∀ a ∈ F.imgS S X, a * a = 1 := by
  have hcomm : ∀ a ∈ X, ∀ b ∈ X, a * b = b * a := fun a ha b hb => hX.1.comm ha hb
  have hsq : ∀ a ∈ X, a * a = 1 := fun a ha => hX.1.mul_self_eq_one ha
  have h16 := h.card_imgS_le (F := F) hXS hcomm
  have hcard : Nat.card X = 32 := by
    rw [hX.2]
    norm_num
  have ht : t ∈ X := by
    by_contra ht
    rw [h.card_of_t_not_mem (F := F) hXS ht] at hcard
    omega
  rw [h.card_of_t_mem (F := F) hXS ht] at hcard
  exact ⟨ht, by omega, h.preS_imgS (F := F) hXS ht, h.comm_imgS (F := F) hcomm,
    h.sq_imgS (F := F) hsq⟩

theorem jElem_eq_secA (hD : ∀ X : Subgroup G, X ≤ S → IsElemAb2 X 5 → X = secA t S L) :
    secA t S L = JElem S := by
  have hmaxA : IsMaxElemAbelianIn S (secA t S L) := by
    refine ⟨h.secA_le hFP, h.isElemAbelian_secA hFP, fun B hBS hB => ?_⟩
    rw [h.card_secA hFP]
    have := h.card_le_32 F hBS hB
    norm_num
    omega
  apply le_antisymm
  · intro x hx
    exact Subgroup.subset_closure ⟨_, hmaxA, hx⟩
  · refine (Subgroup.closure_le _).2 ?_
    rintro x ⟨X, ⟨hXS, hXe, hmax⟩, hx⟩
    have hge := hmax (secA t S L) (h.secA_le hFP) (h.isElemAbelian_secA hFP)
    rw [h.card_secA hFP] at hge
    have hle := h.card_le_32 F hXS hXe
    have hX2 : IsElemAb2 X 5 := ⟨hXe, by norm_num at hge ⊢; omega⟩
    rw [hD X hXS hX2] at hx
    exact hx

end Certs

end Setup107

end PspFrame

end CFSG.OddStandard.SmallF3.Omega
