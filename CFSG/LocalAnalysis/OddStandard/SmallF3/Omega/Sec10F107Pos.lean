module

public import CFSG.LocalAnalysis.OddStandard.SmallF3.Omega.Sec10F107E32
public import CFSG.LocalAnalysis.OddStandard.SmallF3.Omega.Sec10F107Model
public import CFSG.LocalAnalysis.OddStandard.SmallF3.Omega.Sec10Notation
public import CFSG.Sporadic.Th.KernelOrder
public import CFSG.Sporadic.Th.KernelOrderBase
public import CFSG.Sporadic.ThSchreier.LocalData

public section

namespace CFSG.OddStandard.SmallF3.Omega

open Subgroup CFSG.Blueprint CFSG.GH74.KGroups CFSG.ComponentClassification.CatFactsSmall.PSp43
  CFSG.ComponentClassification.GSThmB

local notation "P45" => Equiv.Perm (Fin 45)

namespace PspFrame

variable {G : Type} [Group G] [Finite G] {L : Subgroup G} {F : PspFrame L} {t : G}
  {S : Subgroup G} {K1 K2 : Subgroup G} (h : Setup107 L t S)

namespace Setup107

section Pos

variable
  (hFP : F.img (S ⊓ L) = QT0.originalSubgroup)
  (hQL : secQ K1 K2 ≤ L) (hQ : F.img (secQ K1 K2) = Q32)

include h hFP hQL hQ in
theorem secQ_le_S : secQ K1 K2 ≤ S := by
  have h1 : F.img (secQ K1 K2) ≤ F.img (S ⊓ L) := by
    rw [hQ, hFP]
    exact Mo107.Q32_le_T0
  exact ((PspFrame.img_le_img_iff (F := F) hQL inf_le_right).1 h1).trans inf_le_left

include h hQ in
theorem exists_psi {c : P45} (hc : c ∈ Q32) : ∃ l : ↥L, (l : G) ∈ secQ K1 K2 ∧ F.ψ l = c := by
  rw [← hQ] at hc
  exact PspFrame.mem_img.1 hc

include h hQ in
theorem psi_mem_Q32 {l : ↥L} (hl : (l : G) ∈ secQ K1 K2) : F.ψ l ∈ Q32 := by
  rw [← hQ]
  exact PspFrame.psi_mem_img.2 hl

variable {B2 : Subgroup P45} {y2 : P45}

include h in
theorem comm_lift {r : G} (hrS : r ∈ S) (hr : F.phiG r = y2) (l : ↥L) :
    (l : G) * r = r * (l : G) ↔ F.ψ l * y2 = y2 * F.ψ l := by
  have hc := F.phiG_comm_psi (h.S_le_N hrS) l
  rw [hr] at hc
  exact ⟨fun e => (hc.2 e.symm).symm, fun e => (hc.1 e.symm).symm⟩

include h hQ in
theorem psi_mem_B2 (hM : Mo107.Model107 (F.imgS S S) B2 y2) {r : G} (hrS : r ∈ S)
    (hr : F.phiG r = y2) {l : ↥L} (hlQ : (l : G) ∈ secQ K1 K2) (hlr : (l : G) * r = r * (l : G)) :
    F.ψ l ∈ B2 :=
  (hM.mem_B2 _).2 (Or.inl ⟨h.psi_mem_Q32 hQ hlQ, (h.comm_lift hrS hr l).1 hlr⟩)

include h hFP hQL hQ in
theorem secA2_eq (hM : Mo107.Model107 (F.imgS S S) B2 y2) {r : G} (hrS : r ∈ S)
    (hr : F.phiG r = y2) : secA2 t r K1 K2 = F.preS S B2 := by
  have hN := h.S_le_N
  have hQS : secQ K1 K2 ≤ S := h.secQ_le_S hFP hQL hQ
  apply le_antisymm
  · refine sup_le (sup_le ?_ ?_) ?_
    · intro q hq
      obtain ⟨hqQ, hqC⟩ := Subgroup.mem_inf.1 hq
      have hqL : q ∈ L := hQL hqQ
      refine (F.mem_preS hN).2 ⟨hQS hqQ, ?_⟩
      have e : F.phiG q = F.ψ ⟨q, hqL⟩ := F.phiG_psi ⟨q, hqL⟩
      rw [e]
      exact h.psi_mem_B2 hQ hM hrS hr (l := ⟨q, hqL⟩) hqQ
        (Subgroup.mem_centralizer_singleton_iff.1 hqC)
    · rw [Subgroup.zpowers_le]
      exact (F.mem_preS hN).2 ⟨hrS, by rw [hr]; exact hM.y2_mem⟩
    · rw [Subgroup.zpowers_le]
      exact h.t_mem_preS B2
  · intro x hx
    obtain ⟨hxS, hxB⟩ := (F.mem_preS hN).1 hx
    have hEmem : ∀ q ∈ secQ K1 K2 ⊓ centralizer ({r} : Set G), q ∈ secA2 t r K1 K2 := fun q hq =>
      Subgroup.mem_sup_left (Subgroup.mem_sup_left hq)
    have hrmem : r ∈ secA2 t r K1 K2 :=
      Subgroup.mem_sup_left (Subgroup.mem_sup_right (Subgroup.mem_zpowers r))
    have htmem : t ∈ secA2 t r K1 K2 := Subgroup.mem_sup_right (Subgroup.mem_zpowers t)
    rcases (hM.mem_B2 _).1 hxB with ⟨hcQ, hcomm⟩ | ⟨c, hcQ, hcy, hcx⟩
    · obtain ⟨l, hlQ, hl⟩ := h.exists_psi hQ hcQ
      have hlE : (l : G) ∈ secQ K1 K2 ⊓ centralizer ({r} : Set G) :=
        Subgroup.mem_inf.2 ⟨hlQ, Subgroup.mem_centralizer_singleton_iff.2
          ((h.comm_lift hrS hr l).2 (by rw [hl]; exact hcomm))⟩
      have hφ : F.phiG (l : G) = F.phiG x := by rw [F.phiG_psi, hl]
      rcases (h.phiG_eq_iff (hQS hlQ) hxS).1 hφ with e | e
      · rw [e]
        exact hEmem _ hlE
      · rw [e]
        exact (secA2 t r K1 K2).mul_mem (hEmem _ hlE) htmem
    · obtain ⟨l, hlQ, hl⟩ := h.exists_psi hQ hcQ
      have hlE : (l : G) ∈ secQ K1 K2 ⊓ centralizer ({r} : Set G) :=
        Subgroup.mem_inf.2 ⟨hlQ, Subgroup.mem_centralizer_singleton_iff.2
          ((h.comm_lift hrS hr l).2 (by rw [hl]; exact hcy))⟩
      have hφ : F.phiG ((l : G) * r) = F.phiG x := by
        rw [F.phiG_mul (hN (hQS hlQ)) (hN hrS), F.phiG_psi, hl, hr, hcx]
      rcases (h.phiG_eq_iff (S.mul_mem (hQS hlQ) hrS) hxS).1 hφ with e | e
      · rw [e]
        exact (secA2 t r K1 K2).mul_mem (hEmem _ hlE) hrmem
      · rw [e]
        exact (secA2 t r K1 K2).mul_mem ((secA2 t r K1 K2).mul_mem (hEmem _ hlE) hrmem) htmem

include h hFP hQL hQ in
theorem isElemAbelian_secA2 (hM : Mo107.Model107 (F.imgS S S) B2 y2) {r : G} (hrS : r ∈ S)
    (hr : F.phiG r = y2) (hr2 : r * r = 1) : CFSG.Open.IsElemAbelian 2 (secA2 t r K1 K2) := by
  have hQS : secQ K1 K2 ≤ S := h.secQ_le_S hFP hQL hQ
  show CFSG.Open.IsElemAbelian 2 ((secQ K1 K2 ⊓ centralizer ({r} : Set G)) ⊔ zpowers r ⊔
    zpowers t)
  have hEL : secQ K1 K2 ⊓ centralizer ({r} : Set G) ≤ L := inf_le_left.trans hQL
  have hEe : CFSG.Open.IsElemAbelian 2 (secQ K1 K2 ⊓ centralizer ({r} : Set G)) := by
    rw [← F.isElemAbelian_img_iff hEL]
    have hmem : ∀ p ∈ F.img (secQ K1 K2 ⊓ centralizer ({r} : Set G)), p ∈ B2 := by
      intro p hp
      obtain ⟨l, hl, rfl⟩ := PspFrame.mem_img.1 hp
      obtain ⟨hlQ, hlC⟩ := Subgroup.mem_inf.1 hl
      exact h.psi_mem_B2 hQ hM hrS hr hlQ (Subgroup.mem_centralizer_singleton_iff.1 hlC)
    exact ⟨isMulCommutative_iff_of_setLike.2 fun p hp q hq =>
      hM.comm p (hmem p hp) q (hmem q hq), fun p hp => by rw [pow_two]; exact hM.sq p (hmem p hp)⟩
  have hrE : CFSG.Open.IsElemAbelian 2 (zpowers r) :=
    CFSG.Open.isElemAbelian_zpowers (by rw [pow_two]; exact hr2)
  have hE1 : CFSG.Open.IsElemAbelian 2 ((secQ K1 K2 ⊓ centralizer ({r} : Set G)) ⊔ zpowers r) := by
    refine CFSG.Open.IsElemAbelian.sup_of_commute hEe hrE ?_
    intro a ha b hb
    rcases (mem_zpowers_of_sq hr2).1 hb with hb1 | hb1
    · rw [hb1, mul_one, one_mul]
    · rw [hb1]
      exact Subgroup.mem_centralizer_singleton_iff.1 (Subgroup.mem_inf.1 ha).2
  have htE : CFSG.Open.IsElemAbelian 2 (zpowers t) :=
    CFSG.Open.isElemAbelian_zpowers (by rw [pow_two]; exact h.t_sq)
  refine CFSG.Open.IsElemAbelian.sup_of_commute hE1 htE ?_
  intro a ha b hb
  have haS : a ∈ S :=
    (sup_le (inf_le_left.trans hQS) (Subgroup.zpowers_le.2 hrS)) ha
  rcases (mem_zpowers_of_sq h.t_sq).1 hb with hb1 | hb1
  · rw [hb1, mul_one, one_mul]
  · rw [hb1]
    exact h.t_comm a haS

include h hFP hQL hQ in
theorem isElemAb2_secA2 (hM : Mo107.Model107 (F.imgS S S) B2 y2) {r : G} (hrS : r ∈ S)
    (hr : F.phiG r = y2) (hr2 : r * r = 1) : IsElemAb2 (secA2 t r K1 K2) 5 := by
  refine ⟨h.isElemAbelian_secA2 hFP hQL hQ hM hrS hr hr2, ?_⟩
  rw [h.secA2_eq hFP hQL hQ hM hrS hr, h.card_preS hM.le, hM.card]
  norm_num

include h hFP hQL hQ in
theorem secA2_ne (hM : Mo107.Model107 (F.imgS S S) B2 y2) {r : G} (hrS : r ∈ S)
    (hr : F.phiG r = y2) : secA2 t r K1 K2 ≠ secA t S L := by
  rw [h.secA2_eq hFP hQL hQ hM hrS hr, h.secA_eq hFP]
  intro he
  have h1 := congrArg (F.imgS S) he
  rw [h.imgS_preS hM.le, h.imgS_preS (h.B0_le_imgS hFP)] at h1
  exact hM.y2_out (B0_le_T0 (h1 ▸ hM.y2_mem))

include h hFP in
theorem normal_secA (hM : Mo107.Model107 (F.imgS S S) B2 y2) :
    ((secA t S L).subgroupOf S).Normal := by
  rw [h.secA_eq hFP]
  exact h.normal_preS hM.normB0

include h hFP hQL hQ in
theorem normal_secA2 (hM : Mo107.Model107 (F.imgS S S) B2 y2) {r : G} (hrS : r ∈ S)
    (hr : F.phiG r = y2) : ((secA2 t r K1 K2).subgroupOf S).Normal := by
  rw [h.secA2_eq hFP hQL hQ hM hrS hr]
  exact h.normal_preS hM.normal

end Pos

end Setup107

end PspFrame

end CFSG.OddStandard.SmallF3.Omega
