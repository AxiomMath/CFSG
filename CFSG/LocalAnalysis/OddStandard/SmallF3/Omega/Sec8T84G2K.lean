module

public import CFSG.LocalAnalysis.OddStandard.SmallF3.Omega.Sec8T84Defs
import CFSG.LocalAnalysis.OddStandard.SmallF3.Omega.Sec6L67a
import CFSG.LocalAnalysis.OddStandard.SmallF3.Omega.Sec9SD2
public import CFSG.LocalAnalysis.OddStandard.SmallF3.Omega.Basic

public section

namespace CFSG.OddStandard.SmallF3.Omega

open Subgroup CFSG.Blueprint

theorem sec8t84g_K0_comp (F : Sec8T84Base) {G : Type} [Group G] [Finite G] {t : G}
    {L S : Subgroup G} {z g : G} {B : Subgroup G} (hctx : Sec8Ctx G t L S z g B) {δ : G}
    (hδS : δ ∈ S) (hδ2 : orderOf δ = 2) (hout : InducesOutsideGStar L 6 (-1) δ) :
    IsL29 (layerCent L δ) ∧ IsQuasisimple (layerCent L δ) ∧
      layerCent L δ ≤ L ⊓ centralizer ({δ} : Set G) ∧
      IsComponentIn (layerCent L δ) (centralizer ({δ} : Set G) ⊓ centralizer ({t} : Set G)) ∧
      ((layerCent L δ).subgroupOf
        (centralizer ({δ} : Set G) ⊓ centralizer ({t} : Set G))).Normal := by
  have hS : Sec3SettingLB G t L := hctx.toSec3SettingLB
  have hLM : IsOm6M L := ⟨hS.component.isQuasisimple, hctx.omega6m⟩
  have hLt : L ≤ centralizer ({t} : Set G) := hS.component.le
  have hnormL : ∀ c ∈ centralizer ({t} : Set G), CFSG.conjugate L c = L :=
    conjugate_eq_self_of_lemma36 F.h36 hS
  have hδt : δ ∈ centralizer ({t} : Set G) := hctx.sylow.1 hδS
  have hδN : δ ∈ normalizer (L : Set G) := mem_normalizer_of_conjugate_eq (hnormL δ hδt)
  have hL29 : IsL29 (layerCent L δ) := F.hM.layer_gamma G L hLM δ hδ2 hδN hout
  have hcomp : IsComponentIn (layerCent L δ) (L ⊓ centralizer ({δ} : Set G)) :=
    isComponentIn_layerCent (Or.inr (Or.inl hL29))
  have hcomp2 : IsComponentIn (layerCent L δ)
      (centralizer ({t} : Set G) ⊓ centralizer ({δ} : Set G)) :=
    IsComponentIn.of_normal_inf_centralizer hLt hnormL hcomp
  rw [inf_comm] at hcomp2
  refine ⟨hL29, hcomp.isQuasisimple, hcomp.1, hcomp2, ?_⟩
  rw [Subgroup.normal_subgroupOf_iff_le_normalizer hcomp2.1]
  intro c hc
  apply mem_normalizer_of_conjugate_eq
  have h1 := sec9d_layerCent_conj L δ c
  rw [hnormL c hc.2] at h1
  have h2 : c⁻¹ * δ * c = δ := by
    have h3 : c * δ = δ * c := Subgroup.mem_centralizer_singleton_iff.mp hc.1
    rw [mul_assoc, ← h3, ← mul_assoc, inv_mul_cancel, one_mul]
  rw [h2] at h1
  exact h1.symm

theorem sec8t84g_K_exists (F : Sec8T84Base) {G : Type} [Group G] [Finite G] {t : G}
    {L S : Subgroup G} {z g : G} {B : Subgroup G} (hctx : Sec8Ctx G t L S z g B) {δ : G}
    (hδS : δ ∈ S) (hδ2 : orderOf δ = 2) (hout : InducesOutsideGStar L 6 (-1) δ) :
    ∃ K : Subgroup G, IsComponentIn K (centralizer ({δ} : Set G)) ∧ InFStar K ∧
      layerCent L δ ≤ K ∧ (K.subgroupOf (centralizer ({δ} : Set G))).Normal := by
  obtain ⟨hL29, hq, -, hcomp, -⟩ := sec8t84g_K0_comp F hctx hδS hδ2 hout
  have hS : Sec3SettingLB G t L := hctx.toSec3SettingLB
  have hδt : δ ∈ centralizer ({t} : Set G) := hctx.sylow.1 hδS
  have htδ : t * δ = δ * t := (Subgroup.mem_centralizer_singleton_iff.mp hδt).symm
  have hK2 : IsComponentIn (layerCent L δ) (centralizer ({t, δ} : Set G)) := by
    rw [centralizer_pair_eq_inf, inf_comm]
    exact hcomp
  obtain ⟨K, hK, hle⟩ := hS.lBalance t δ hS.involution hδ2 htδ (layerCent L δ) hK2
  have hK0F : InFStar (layerCent L δ) := Or.inr ⟨hq, Or.inl hL29⟩
  have hKF : InFStar K :=
    hS.a2 t δ hS.involution hδ2 htδ (layerCent L δ) K hK2 hK hle hK0F
  have hCN : centralizer ({δ} : Set G) ≤ normalizer (K : Set G) :=
    sec67_cent_le_normalizer F.h63 hS (F.hH62 G t L hS) hδ2 hK hKF
  have htC : t ∈ centralizer ({δ} : Set G) :=
    Subgroup.mem_centralizer_singleton_iff.mpr htδ
  have hKt : CFSG.conjugate K t = K := by
    unfold CFSG.conjugate
    exact Subgroup.mem_normalizer_iff_map_conj_eq.mp (inv_mem (hCN htC))
  refine ⟨K, hK, hKF, ?_, (Subgroup.normal_subgroupOf_iff_le_normalizer hK.1).mpr hCN⟩
  calc layerCent L δ ≤ K ⊔ CFSG.conjugate K t := hle
    _ = K := by rw [hKt, sup_idem]

end CFSG.OddStandard.SmallF3.Omega
