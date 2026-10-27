module

public import CFSG.LocalAnalysis.OddStandard.SmallF3.Omega.Sec8S87a
public import CFSG.LocalAnalysis.OddStandard.SmallF3.Omega.Sec6Facts2
import CFSG.LocalAnalysis.OddStandard.SmallF3.Omega.Sec6L68b
import CFSG.LocalAnalysis.OddStandard.SmallF3.Omega.Sec10Sylow
import CFSG.GroupTheory.ElemAbelianClosure

public section

namespace CFSG.OddStandard.SmallF3.Omega

open Subgroup CFSG.Blueprint

private theorem sec8a_mem_normalizer_of_conjugate_eq {G : Type} [Group G] {H : Subgroup G} {c : G}
    (h : CFSG.conjugate H c = H) : c ∈ normalizer (H : Set G) := by
  rw [Subgroup.mem_normalizer_iff]
  intro x
  rw [← mem_conjugate_iff' (H := H) (g := c) (x := x), h]

private theorem sec8a_cent_le_normalizer {G : Type} [Group G] [Finite G]
    (h36 : Asc82Lemma36) {t : G}
    {L : Subgroup G} (hS : Sec3SettingLB G t L) {B : Subgroup G} :
    centralizer (Asub8 t B : Set G) ≤ normalizer (L : Set G) := by
  intro c hc
  have hct : c ∈ centralizer ({t} : Set G) :=
    Subgroup.mem_centralizer_singleton_iff.mpr
      ((Subgroup.mem_centralizer_iff.mp hc t
        (Subgroup.mem_sup_left (Subgroup.mem_zpowers t))).symm)
  exact sec8a_mem_normalizer_of_conjugate_eq (conjugate_eq_self_of_lemma36 h36 hS c hct)

private theorem sec8a_A_elem {G : Type} [Group G] [Finite G] {t : G} {L S : Subgroup G}
    {z g : G} {B : Subgroup G}
    (hctx : Sec8Ctx G t L S z g B) : CFSG.Open.IsElemAbelian 2 (Asub8 t B) := by
  have hS : Sec3SettingLB G t L := hctx.toSec3SettingLB
  have ht2 : t ^ 2 = 1 := by rw [← hS.involution]; exact pow_orderOf_eq_one t
  have hzt : CFSG.Open.IsElemAbelian 2 (Subgroup.zpowers t) :=
    CFSG.Open.isElemAbelian_zpowers (p := 2) ht2
  have hB' : CFSG.Open.IsElemAbelian 2 B := hctx.B_e16.1
  have hcomm : ∀ a ∈ Subgroup.zpowers t, ∀ b ∈ B, a * b = b * a := by
    intro a ha b hb
    obtain ⟨k, rfl⟩ := Subgroup.mem_zpowers_iff.mp ha
    have htb : t * b = b * t :=
      (Subgroup.mem_centralizer_singleton_iff.mp (hS.component.le (hctx.B_le hb).1)).symm
    exact ((show Commute t b from htb).zpow_left k).eq
  exact CFSG.Open.IsElemAbelian.sup_of_commute hzt hB' hcomm

private theorem sec8a_A_le_cent {G : Type} [Group G] {t : G} {B : Subgroup G}
    (hAel : CFSG.Open.IsElemAbelian 2 (Asub8 t B)) :
    Asub8 t B ≤ centralizer (Asub8 t B : Set G) := by
  haveI : IsMulCommutative (Asub8 t B) := hAel.1
  intro a ha
  exact Subgroup.mem_centralizer_iff.mpr fun a' ha' => setLike_mul_comm ha' ha

private theorem sec8a_A_sylow {G : Type} [Group G] [Finite G]
    (h36 : Asc82Lemma36) (h68 : Asc82Lemma68)
    (h85 : Asc82Lemma85) (h87 : Asc82Lemma87) (hB : Asc82Sec8B) (hM : Asc82Tab6M)
    {t : G} {L S : Subgroup G} {z g : G} {B : Subgroup G} (hctx : Sec8Ctx G t L S z g B) :
    IsSylow2Of (Asub8 t B) (centralizer (Asub8 t B : Set G)) := by
  have hS : Sec3SettingLB G t L := hctx.toSec3SettingLB
  have hLM : IsOm6M L := ⟨hS.component.isQuasisimple, hctx.omega6m⟩
  have hAel : CFSG.Open.IsElemAbelian 2 (Asub8 t B) := sec8a_A_elem hctx
  have hA2 : IsPGroup 2 (Asub8 t B) := hAel.isPGroup
  have hAC : Asub8 t B ≤ centralizer (Asub8 t B : Set G) := sec8a_A_le_cent hAel
  have hCL : centralizer (Asub8 t B : Set G) ≤ normalizer (L : Set G) :=
    sec8a_cent_le_normalizer h36 hS
  obtain ⟨P, hPsyl, hAP⟩ :=
    sec68_exists_sylow_ge (H := centralizer (Asub8 t B : Set G)) hA2 hAC
  have hPA : P ≤ Asub8 t B := by
    intro x hxP
    have hxC : x ∈ centralizer (Asub8 t B : Set G) := hPsyl.1 hxP
    have hxN : x ∈ normalizer (L : Set G) := hCL hxC
    have hxB : ∀ b ∈ B, x * b = b * x := fun b hb =>
      (Subgroup.mem_centralizer_iff.mp hxC b (Subgroup.mem_sup_right hb)).symm
    have hB2 : IsPGroup 2 B := hctx.B_e16.1.isPGroup
    have hBL : B ≤ L := fun b hb => (hctx.B_le hb).1
    obtain ⟨P0, hP0, hBP0⟩ := sec68_exists_sylow_ge (H := L) hB2 hBL
    rcases hM.cent_B G L hLM P0 hP0 B hBP0 hctx.B_e16 x hxN hxB with
      ⟨b, hbB, hbc⟩ | ⟨α, hα⟩ | ⟨α, hα⟩
    · have hbA : b ∈ Asub8 t B := Subgroup.mem_sup_right hbB
      have hbP : b ∈ P := hAP hbA
      have hcP : x * b⁻¹ ∈ P := P.mul_mem hxP (P.inv_mem hbP)
      have hQ2 : IsPGroup 2 ↥(P ⊓ centralizer (L : Set G)) :=
        hPsyl.2.1.to_le inf_le_left
      have htP : t ∈ P := hAP (Subgroup.mem_sup_left (Subgroup.mem_zpowers t))
      have htC : t ∈ centralizer (L : Set G) := sec68_t_mem_centralizer hS
      have hle : zpowers t ≤ P ⊓ centralizer (L : Set G) :=
        le_inf (zpowers_le.mpr htP) (zpowers_le.mpr htC)
      have hQeq : P ⊓ centralizer (L : Set G) = zpowers t :=
        IsSylow2Of.eq_of_le (sec8s_sylow_t h68 h85 hB hctx) inf_le_right hQ2 hle
      have hcQ : x * b⁻¹ ∈ P ⊓ centralizer (L : Set G) := ⟨hcP, hbc⟩
      rw [hQeq] at hcQ
      rw [show x = (x * b⁻¹) * b by group]
      exact Subgroup.mul_mem_sup hcQ hbB
    · exact absurd hα (h87 G t L S z g B hctx x α).1
    · exact absurd hα (h87 G t L S z g B hctx x α).2
  exact le_antisymm hPA hAP ▸ hPsyl

private theorem sec8a_oddCore_le {G : Type} [Group G] [Finite G] {t : G} {B : Subgroup G} :
    oddCoreIn (centralizer (Asub8 t B : Set G)) ≤ oddCoreIn (Nsub8 t B) :=
  oddCoreIn_le_of_normal (Subgroup.centralizer_le_normalizer (Asub8 t B : Set G))
    (Subgroup.normal_subgroupOf_centralizer_normalizer (Asub8 t B : Set G))

private theorem sec8a_oddCore_M_le_cent {G : Type} [Group G] [Finite G] {t : G} {B : Subgroup G}
    (hA2 : IsPGroup 2 (Asub8 t B)) :
    oddCoreIn (Nsub8 t B) ≤ centralizer (Asub8 t B : Set G) := by
  have hAN : Asub8 t B ≤ Nsub8 t B := Subgroup.le_normalizer
  have hAn : ((Asub8 t B).subgroupOf (Nsub8 t B)).Normal := by
    change ((Asub8 t B).subgroupOf
      (Subgroup.normalizer (Asub8 t B : Set G))).Normal
    infer_instance
  have hOn : ((oddCoreIn (Nsub8 t B)).subgroupOf (Nsub8 t B)).Normal :=
    (oddCoreIn_normal (Nsub8 t B)).2
  have hOodd : Odd (Nat.card (oddCoreIn (Nsub8 t B))) := odd_card_oddCoreIn (Nsub8 t B)
  have hcomm := commute_of_normal_two_odd hAN (oddCoreIn_normal (Nsub8 t B)).1 hAn hOn hA2 hOodd
  intro o ho
  exact Subgroup.mem_centralizer_iff.mpr fun a ha => hcomm a ha o ho

theorem asc82Lemma8A_of (h36 : Asc82Lemma36) (h68 : Asc82Lemma68) (h85 : Asc82Lemma85)
    (h87 : Asc82Lemma87) (hB : Asc82Sec8B) (hM : Asc82Tab6M) : Asc82Lemma8A := by
  intro G _ _ t L S z g B hctx
  have hS : Sec3SettingLB G t L := hctx.toSec3SettingLB
  have hCL : centralizer (Asub8 t B : Set G) ≤ normalizer (L : Set G) :=
    sec8a_cent_le_normalizer h36 hS
  have hAel : CFSG.Open.IsElemAbelian 2 (Asub8 t B) := sec8a_A_elem hctx
  have hAsyl : IsSylow2Of (Asub8 t B) (centralizer (Asub8 t B : Set G)) :=
    sec8a_A_sylow h36 h68 h85 h87 hB hM hctx
  have hAd : Asub8 t B ⊔ oddCoreIn (centralizer (Asub8 t B : Set G)) =
      centralizer (Asub8 t B : Set G) :=
    sup_oddCoreIn_of_central_sylow hAsyl
      (fun k hk z hz => Subgroup.mem_centralizer_iff.mp hk z hz)
  have hOCN : oddCoreIn (centralizer (Asub8 t B : Set G)) ≤ oddCoreIn (Nsub8 t B) :=
    sec8a_oddCore_le
  have hONC : oddCoreIn (Nsub8 t B) ≤ centralizer (Asub8 t B : Set G) :=
    sec8a_oddCore_M_le_cent hAel.isPGroup
  have hAC : Asub8 t B ≤ centralizer (Asub8 t B : Set G) := sec8a_A_le_cent hAel
  have hgoal : Asub8 t B ⊔ oddCoreIn (Nsub8 t B) = centralizer (Asub8 t B : Set G) := by
    apply le_antisymm
    · exact sup_le hAC hONC
    · rw [← hAd]
      exact sup_le le_sup_left (hOCN.trans le_sup_right)
  have hinf : normalizer (L : Set G) ⊓ centralizer (Asub8 t B : Set G) =
      centralizer (Asub8 t B : Set G) := inf_eq_right.mpr hCL
  refine ⟨?_, hinf⟩
  rw [hinf]
  exact hgoal

end CFSG.OddStandard.SmallF3.Omega
