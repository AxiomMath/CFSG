module

public import CFSG.LocalAnalysis.OddStandard.SmallF3.Omega.Sec8Statements
public import CFSG.LocalAnalysis.OddStandard.SmallF3.Omega.Sec6Facts2
import CFSG.LocalAnalysis.OddStandard.SmallF3.Omega.Sec6L66In
public import CFSG.LocalAnalysis.OddStandard.SmallF3.Omega.Basic

public section

namespace CFSG.OddStandard.SmallF3.Omega

open Subgroup CFSG.Blueprint

private theorem asc82_84z_t_mem_centralizer {G : Type} [Group G] [Finite G] {t : G}
    {L : Subgroup G} (hS : Sec3SettingLB G t L) : t ∈ centralizer (L : Set G) := by
  rw [Subgroup.mem_centralizer_iff]
  intro x hx
  exact Subgroup.mem_centralizer_singleton_iff.mp (hS.component.le hx)

private theorem asc82_84z_type {G : Type} [Group G] [Finite G] {t : G} {L S : Subgroup G}
    {z g : G} {B : Subgroup G} (h36 : Asc82Lemma36) (h37 : Asc82Lemma37) (hM : Asc82Tab6M)
    (hctx : Sec8Ctx G t L S z g B) {u : G} (huC : u ∈ centralizer ({t} : Set G))
    (huconj : IsConj z u) : InducesTypeSome L u 6 (-1) 4 1 := by
  have hS : Sec3SettingLB G t L := hctx.toSec3SettingLB
  have hLM : IsOm6M L := ⟨hS.component.isQuasisimple, hctx.omega6m⟩
  have hz2 : orderOf z = 2 := hctx.pocket.1
  obtain ⟨c, hc⟩ := isConj_iff_inv_mul.mp huconj
  have hu2 : orderOf u = 2 := by rw [← hc, orderOf_conjugate_eq, hz2]
  have huN : u ∈ normalizer (L : Set G) :=
    mem_normalizer_of_conjugate_eq (conjugate_eq_self_of_lemma36 h36 hS u huC)
  have hlayer : layerCent L u = ⊥ := by
    have h := h37 G t L hS z c hctx.pocket (by rw [hc]; exact huC)
    rw [hc] at h
    simpa [layerCent] using h
  rcases (hM.layer_trivial G L hLM u hu2 huN).mp hlayer with h4 | ⟨α, h3⟩
  · exact h4
  · exact (hctx.no_i3 u huC hu2 α h3).elim

theorem sec8s_not_isConj_z_t {G : Type} [Group G] [Finite G] {t : G} {L S : Subgroup G}
    {z g : G} {B : Subgroup G} (h36 : Asc82Lemma36) (h37 : Asc82Lemma37) (hM : Asc82Tab6M)
    (hctx : Sec8Ctx G t L S z g B) : ¬ IsConj z t := by
  intro hzt
  have hS : Sec3SettingLB G t L := hctx.toSec3SettingLB
  have hLM : IsOm6M L := ⟨hS.component.isQuasisimple, hctx.omega6m⟩
  have htCL : t ∈ centralizer (L : Set G) := asc82_84z_t_mem_centralizer hS
  have htC : t ∈ centralizer ({t} : Set G) := Subgroup.mem_centralizer_singleton_iff.mpr rfl
  have htype : InducesTypeSome L t 6 (-1) 4 1 := asc82_84z_type h36 h37 hM hctx htC hzt
  have htN : t ∈ normalizer (L : Set G) := (Subgroup.centralizer_le_normalizer (L : Set G)) htCL
  exact ((hM.inner_iff G L hLM t hS.involution htN).mpr htype).2 htCL

theorem asc82Lemma84Z_of (h36 : Asc82Lemma36) (h37 : Asc82Lemma37) (h82 : Asc82Lemma82)
    (h83 : Asc82Lemma83) (hM : Asc82Tab6M) : Asc82Lemma84Z := by
  intro G _ _ t L S z g B hctx
  have hS : Sec3SettingLB G t L := hctx.toSec3SettingLB
  have hLM : IsOm6M L := ⟨hS.component.isQuasisimple, hctx.omega6m⟩
  have hz2 : orderOf z = 2 := hctx.pocket.1
  have hzL : z ∈ L := hctx.pocket.mem
  have htCL : t ∈ centralizer (L : Set G) := asc82_84z_t_mem_centralizer hS
  have hzt_comm : z * t = t * z :=
    Subgroup.mem_centralizer_singleton_iff.mp (hS.component.le hzL)
  have hnotConj : ¬ IsConj z t := sec8s_not_isConj_z_t h36 h37 hM hctx
  ext w
  constructor
  · rintro ⟨hwconj, hwC⟩
    obtain ⟨c, hc⟩ := isConj_iff_inv_mul.mp hwconj
    have hw2 : orderOf w = 2 := by rw [← hc, orderOf_conjugate_eq, hz2]
    have hwN : w ∈ normalizer (L : Set G) :=
      mem_normalizer_of_conjugate_eq (conjugate_eq_self_of_lemma36 h36 hS w hwC)
    have htype : InducesTypeSome L w 6 (-1) 4 1 := asc82_84z_type h36 h37 hM hctx hwC hwconj
    have hin := (hM.inner_iff G L hLM w hw2 hwN).mpr htype
    have hwt : w ≠ t := by
      intro hwt
      apply hin.2
      rw [hwt]
      exact htCL
    obtain ⟨v, hvL, hv2, hcase⟩ :=
      sec66_inner_decomp h82 hS hctx.omega6m hw2 hwC hwt hin.1
    rcases hcase with hwv | hwvt
    · rw [hwv]
      exact hM.inv_one_class G L hLM z v hzL hvL hz2 hv2
    · obtain ⟨l, hlL, hlv⟩ := hM.inv_one_class G L hLM z v hzL hvL hz2 hv2
      have hlt : l * t = t * l :=
        Subgroup.mem_centralizer_singleton_iff.mp (hS.component.le hlL)
      have hvt : v * t = l * (z * t) * l⁻¹ := by
        rw [hlv]
        rw [show (l * z * l⁻¹) * t = l * z * (l⁻¹ * t) by group]
        rw [show l⁻¹ * t = t * l⁻¹ by
          have h := congrArg (fun x => l⁻¹ * x * l⁻¹) hlt
          simpa [mul_assoc] using h.symm]
        group
      have hconj_zt_vt : IsConj (z * t) (v * t) := isConj_iff.mpr ⟨l, hvt.symm⟩
      have hz_vt : IsConj z (v * t) := by rw [← hwvt]; exact hwconj
      have hz_zt : IsConj z (z * t) := IsConj.trans hz_vt (IsConj.symm hconj_zt_vt)
      have h83res : IsConj t (z * t) := by
        have h := h83 G t L hS hctx.omega6m z hz2 hzL
        rwa [← hzt_comm] at h
      exact (hnotConj (IsConj.trans hz_zt (IsConj.symm h83res))).elim
  · rintro ⟨l, hl, rfl⟩
    refine ⟨isConj_iff.mpr ⟨l, rfl⟩, ?_⟩
    exact hS.component.le (L.mul_mem (L.mul_mem hl hzL) (L.inv_mem hl))

end CFSG.OddStandard.SmallF3.Omega
