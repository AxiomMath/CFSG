module

public import CFSG.LocalAnalysis.ComponentClassification.AS81Sec3Step38F
public import CFSG.Sporadic.Schreier.J4SSylowBase

public section

attribute [-instance] instAddCommGroupOfIsSimpleAddGroupOfIsNilpotent
  instCommGroupOfIsSimpleGroupOfIsNilpotent CFSG.Sporadic.Schreier.Tits.titsZMod2CharP

namespace CFSG.ComponentClassification.AS81

open Subgroup Module QuadraticMap CFSG.RankThree.OrthogonalInvolutions CFSG.Open
open CFSG.LargeExtraspecial.S2 (perp mem_perp)
open CFSG.LargeExtraspecial.OrthoF2 (isRefl_polarBilin zmod2_eq_zero_or_eq_one)

namespace Sec38Hyp

variable {G : Type} [Group G] [Finite G] {A A₁ R : Subgroup G} {g : G} {E F : Subgroup G}
  {x : G} {Zs P T Q B₀ : Subgroup G} {z y : G} {D J U V₀ V Q₀ : Subgroup G}
  (H : Sec38Hyp G A A₁ R g E F x Zs P T Q B₀ z y D J U V₀ V Q₀)
include H

theorem Zs_le_E : Zs ≤ E := by
  intro s hs
  have hSz := H.q0.dData.suz
  have h := hs
  rw [hSz.Zs_eq] at h
  have h2 : s ∈ centerIn (E ⊔ F) := h.2
  rw [← hSz.setting.frame.inf_eq_center] at h2
  exact h2.1

theorem sq_eq_one_of_mem_Zs {s : G} (hs : s ∈ Zs) : s ^ 2 = 1 :=
  H.q0.dData.suz.setting.frame.elemE.2 s (H.Zs_le_E hs)

theorem z_mem_Zs : z ∈ Zs := H.q0.dData.suz.z_mem

theorem comm_of_mem_Zs {s t : G} (hs : s ∈ Zs) (ht : t ∈ Zs) : s * t = t * s :=
  congrArg Subtype.val
    (H.q0.dData.suz.setting.frame.elemE.1.is_comm.comm ⟨s, H.Zs_le_E hs⟩ ⟨t, H.Zs_le_E ht⟩)

theorem exists_z₂ : ∃ z₂ ∈ Zs, z₂ ∉ zpowers z := by
  by_contra hcon
  push Not at hcon
  have h1 := Subgroup.card_le_of_le (show Zs ≤ zpowers z from hcon)
  rw [H.q0.dData.suz.Zs_card, Nat.card_zpowers, show orderOf z = 2 from H.xsub.orderOf_z] at h1
  omega

variable {z₂ : G}

theorem cl_ne_zero (hZQ : Zs ≤ Q) (hz₂ : z₂ ∈ Zs) (hz₂z : z₂ ∉ zpowers z) :
    H.xsub.cl z₂ ≠ 0 := fun h =>
  hz₂z ((H.xsub.cl_eq_zero_iff (H.Q_le (hZQ hz₂))).mp h)

theorem q_cl_eq_zero (hZQ : Zs ≤ Q) (hz₂ : z₂ ∈ Zs) : H.xsub.q (H.xsub.cl z₂) = 0 :=
  (H.xsub.q_cl_eq_zero_iff (H.Q_le (hZQ hz₂))).mpr (H.sq_eq_one_of_mem_Zs hz₂)

theorem clSub_Zs (hZQ : Zs ≤ Q) (hz₂ : z₂ ∈ Zs) (hz₂z : z₂ ∉ zpowers z) :
    H.xsub.clSub Zs = (ZMod 2) ∙ H.xsub.cl z₂ := by
  have hZQ₁ : Zs ≤ H.xsub.Q₁ := hZQ.trans H.Q_le
  have h1 : finrank (ZMod 2) (H.xsub.clSub Zs) = 1 :=
    H.xsub.finrank_clSub hZQ₁ H.z_mem_Zs (n := 1) (by rw [H.q0.dData.suz.Zs_card]; norm_num)
  have hle : (ZMod 2) ∙ H.xsub.cl z₂ ≤ H.xsub.clSub Zs :=
    (Submodule.span_singleton_le_iff_mem _ _).mpr (H.xsub.cl_mem_clSub hz₂ (hZQ₁ hz₂))
  have h2 : finrank (ZMod 2) ((ZMod 2) ∙ H.xsub.cl z₂) = 1 :=
    finrank_span_singleton (H.cl_ne_zero hZQ hz₂ hz₂z)
  exact (Submodule.eq_of_le_of_finrank_eq hle (by rw [h1, h2])).symm

theorem Zs_eq_clPre (hZQ : Zs ≤ Q) (hz₂ : z₂ ∈ Zs) (hz₂z : z₂ ∉ zpowers z) :
    Zs = H.xsub.clPre ((ZMod 2) ∙ H.xsub.cl z₂) := by
  rw [← H.clSub_Zs hZQ hz₂ hz₂z, H.xsub.clPre_clSub (hZQ.trans H.Q_le) H.z_mem_Zs]

theorem centralizer_Zs_eq_clPre (hZQ : Zs ≤ Q) (hz₂ : z₂ ∈ Zs) (hz₂z : z₂ ∉ zpowers z) :
    (Q₀ ⊔ Q) ⊓ centralizer (Zs : Set G) =
      H.xsub.clPre (perp H.xsub.q ((ZMod 2) ∙ H.xsub.cl z₂)) := by
  have hZQ₁ : Zs ≤ H.xsub.Q₁ := hZQ.trans H.Q_le
  ext u
  rw [mem_inf, H.xsub.mem_clPre]
  constructor
  · rintro ⟨hu, huc⟩
    refine ⟨hu, mem_perp.mpr fun w hw => ?_⟩
    obtain ⟨c, rfl⟩ := Submodule.mem_span_singleton.mp hw
    rw [polar_smul_left, (H.xsub.polar_cl_eq_zero_iff (hZQ₁ hz₂) hu).mpr
      (mem_centralizer_iff.mp huc z₂ hz₂), smul_zero]
  · rintro ⟨hu, hup⟩
    refine ⟨hu, mem_centralizer_iff.mpr fun s hs => ?_⟩
    have hs' := hs
    rw [H.Zs_eq_clPre hZQ hz₂ hz₂z] at hs'
    exact (H.xsub.polar_cl_eq_zero_iff hs'.1 hu).mp ((mem_perp.mp hup) _ hs'.2)

theorem card_U (hZQ : Zs ≤ Q) (hz₂ : z₂ ∈ Zs) (hz₂z : z₂ ∉ zpowers z) :
    Nat.card ↥((Q₀ ⊔ Q) ⊓ centralizer (Zs : Set G)) = 2 ^ 8 := by
  rw [H.centralizer_Zs_eq_clPre hZQ hz₂ hz₂z, H.xsub.card_clPre, H.xsub.card_submodule]
  have h1 := LinearMap.BilinForm.finrank_orthogonal H.xsub.q_nondegenerate
    ((ZMod 2) ∙ H.xsub.cl z₂)
  rw [finrank_span_singleton (H.cl_ne_zero hZQ hz₂ hz₂z), H.finrank_Qt] at h1
  change finrank (ZMod 2) ↥(LinearMap.BilinForm.orthogonal (polarBilin H.xsub.q)
    ((ZMod 2) ∙ H.xsub.cl z₂)) = _ at h1
  rw [show finrank (ZMod 2) ↥(perp H.xsub.q ((ZMod 2) ∙ H.xsub.cl z₂)) = 7 from h1]
  norm_num

theorem centerIn_U (hZQ : Zs ≤ Q) (hz₂ : z₂ ∈ Zs) (hz₂z : z₂ ∉ zpowers z) :
    centerIn ((Q₀ ⊔ Q) ⊓ centralizer (Zs : Set G)) = Zs := by
  have hZQ₁ : Zs ≤ H.xsub.Q₁ := hZQ.trans H.Q_le
  have hZU : Zs ≤ (Q₀ ⊔ Q) ⊓ centralizer (Zs : Set G) := fun s hs =>
    mem_inf.mpr ⟨hZQ₁ hs, mem_centralizer_iff.mpr fun t ht => H.comm_of_mem_Zs ht hs⟩
  apply le_antisymm
  · rintro u ⟨hu, huc⟩
    rw [H.centralizer_Zs_eq_clPre hZQ hz₂ hz₂z] at hu huc
    rw [H.Zs_eq_clPre hZQ hz₂ hz₂z]
    refine ⟨hu.1, ?_⟩
    have h1 : H.xsub.cl u ∈ perp H.xsub.q (perp H.xsub.q ((ZMod 2) ∙ H.xsub.cl z₂)) := by
      refine mem_perp.mpr fun w hw => ?_
      obtain ⟨b, hb, rfl⟩ := H.xsub.exists_cl w
      exact (H.xsub.polar_cl_eq_zero_iff hb hu.1).mpr
        (mem_centralizer_iff.mp huc b ⟨hb, hw⟩)
    have h2 : H.xsub.cl u ∈ LinearMap.BilinForm.orthogonal (polarBilin H.xsub.q)
        (LinearMap.BilinForm.orthogonal (polarBilin H.xsub.q) ((ZMod 2) ∙ H.xsub.cl z₂)) := h1
    rwa [LinearMap.BilinForm.orthogonal_orthogonal H.xsub.q_nondegenerate
      (isRefl_polarBilin H.xsub.q)] at h2
  · intro s hs
    refine ⟨hZU hs, mem_centralizer_iff.mpr fun u hu => ?_⟩
    exact (mem_centralizer_iff.mp (mem_inf.mp hu).2 s hs).symm

theorem ρG_cl_z₂ (hZQ : Zs ≤ Q) (hz₂ : z₂ ∈ Zs) {n : H.xsub.N}
    (hn : (n : G) ∈ centralizer (Zs : Set G)) : H.ρG n (H.xsub.cl z₂) = H.xsub.cl z₂ := by
  rw [H.ρG_cl n (H.Q_le (hZQ hz₂))]
  congr 1
  rw [(mem_centralizer_iff.mp hn z₂ hz₂).symm, mul_inv_cancel_right]

theorem exists_mem_centralizer_of_apply (hQF : Q₀ ⊔ Q ≤ sec3F (Q₀ ⊔ Q)) (hZQ : Zs ≤ Q)
    (hz₂ : z₂ ∈ Zs) (hz₂z : z₂ ∉ zpowers z) (f : ↥(sec3F (Q₀ ⊔ Q)))
    (hf : H.ρF f (H.xsub.cl z₂) = H.xsub.cl z₂) :
    ∃ f' : ↥(sec3F (Q₀ ⊔ Q)), (f' : G) ∈ centralizer (Zs : Set G) ∧ H.ρF f' = H.ρF f := by
  have hZQ₁ : Zs ≤ H.xsub.Q₁ := hZQ.trans H.Q_le
  have hfN := H.F_le_N f.2
  have hz₂Q := hZQ₁ hz₂
  have hcl : H.xsub.cl ((f : G) * z₂ * (f : G)⁻¹) = H.xsub.cl z₂ := by
    have h1 := H.ρG_cl ⟨f, hfN⟩ hz₂Q
    rw [← h1]
    exact hf
  have hfz₂ := (H.xsub.cl_eq_cl_iff hz₂Q (H.xsub.conj_mem hfN hz₂Q)).mp hcl.symm
  have hcen : ∀ f' : G, f' ∈ H.xsub.N → f' * z₂ * f'⁻¹ = z₂ →
      f' ∈ centralizer (Zs : Set G) := by
    intro f' hf'N hf'z₂
    have hf'z : f' * z * f'⁻¹ = z := by
      have h1 := (mem_normalizer_iff.mp (Sec3.mem_normalizer_centerIn (H := Q₀ ⊔ Q) hf'N) z).mp
        (by rw [H.center_sup]; exact mem_zpowers z)
      rw [H.center_sup] at h1
      rcases H.xsub.mem_zpowers_z_iff.mp h1 with h2 | h2
      · exfalso
        apply H.z_ne_one
        calc z = f'⁻¹ * (f' * z * f'⁻¹) * f' := by group
          _ = 1 := by rw [h2]; group
      · exact h2
    refine mem_centralizer_iff.mpr fun s hs => ?_
    have hs' := hs
    rw [H.Zs_eq_clPre hZQ hz₂ hz₂z] at hs'
    obtain ⟨c, hc⟩ := Submodule.mem_span_singleton.mp hs'.2
    have hfs : f' * s * f'⁻¹ = s := by
      rcases zmod2_eq_zero_or_eq_one c with rfl | rfl
      · rw [zero_smul, eq_comm, H.xsub.cl_eq_zero_iff hs'.1] at hc
        rcases H.xsub.mem_zpowers_z_iff.mp hc with h | h
        · rw [h]; group
        · rw [show s = z from h]; exact hf'z
      · rw [one_smul] at hc
        have h1 := (H.xsub.cl_eq_cl_iff hz₂Q hs'.1).mp hc
        rcases H.xsub.mem_zpowers_z_iff.mp h1 with h | h
        · have hs2 : s = z₂ := by
            calc s = z₂ * (z₂⁻¹ * s) := by group
              _ = z₂ := by rw [h, mul_one]
          rw [hs2]; exact hf'z₂
        · have hs2 : s = z₂ * z := by
            calc s = z₂ * (z₂⁻¹ * s) := by group
              _ = z₂ * z := by rw [show z₂⁻¹ * s = z from h]
          rw [hs2, show f' * (z₂ * z) * f'⁻¹ = (f' * z₂ * f'⁻¹) * (f' * z * f'⁻¹) by group,
            hf'z₂, hf'z]
    calc s * f' = f' * (f'⁻¹ * s * f') := by group
      _ = f' * s := by
        rw [show f'⁻¹ * s * f' = s by
          calc f'⁻¹ * s * f' = f'⁻¹ * (f' * s * f'⁻¹) * f' := by rw [hfs]
            _ = s := by group]
  rcases H.xsub.mem_zpowers_z_iff.mp hfz₂ with h | h
  ·
    have h1 : (f : G) * z₂ * (f : G)⁻¹ = z₂ := by
      calc (f : G) * z₂ * (f : G)⁻¹ = z₂ * (z₂⁻¹ * ((f : G) * z₂ * (f : G)⁻¹)) := by group
        _ = z₂ := by rw [h, mul_one]
    exact ⟨f, hcen f hfN h1, rfl⟩
  ·
    have h1 : (f : G) * z₂ * (f : G)⁻¹ = z₂ * z := by
      calc (f : G) * z₂ * (f : G)⁻¹ = z₂ * (z₂⁻¹ * ((f : G) * z₂ * (f : G)⁻¹)) := by group
        _ = z₂ * z := by rw [show z₂⁻¹ * ((f : G) * z₂ * (f : G)⁻¹) = z from h]
    obtain ⟨w, hw⟩ := CFSG.ClassicalGroups.Orthogonal.exists_polar_ne_zero H.xsub.q_nondegenerate
      (H.cl_ne_zero hZQ hz₂ hz₂z)
    obtain ⟨j, hj, rfl⟩ := H.xsub.exists_cl w
    have hjz₂ : ¬ (z₂ * j = j * z₂) := fun hc =>
      hw ((H.xsub.polar_cl_eq_zero_iff hz₂Q hj).mpr hc)
    have hjc : j * z₂ * j⁻¹ * z₂⁻¹ ∈ zpowers z :=
      commutator_mem_of_extraspecial H.ext H.center_sup hj hz₂Q
    have hjz : j * z₂ * j⁻¹ = z * z₂ := by
      rcases H.xsub.mem_zpowers_z_iff.mp hjc with h2 | h2
      · exfalso
        apply hjz₂
        have h3 : j * z₂ * j⁻¹ = z₂ := by
          calc j * z₂ * j⁻¹ = j * z₂ * j⁻¹ * z₂⁻¹ * z₂ := by group
            _ = z₂ := by rw [h2, one_mul]
        calc z₂ * j = j * (j⁻¹ * z₂ * j) := by group
          _ = j * z₂ := by
            rw [show j⁻¹ * z₂ * j = z₂ by
              calc j⁻¹ * z₂ * j = j⁻¹ * (j * z₂ * j⁻¹) * j := by rw [h3]
                _ = z₂ := by group]
      · calc j * z₂ * j⁻¹ = j * z₂ * j⁻¹ * z₂⁻¹ * z₂ := by group
          _ = z * z₂ := by rw [show j * z₂ * j⁻¹ * z₂⁻¹ = z from h2]
    have hzj : j * z = z * j := H.xsub.z_comm hj
    have hzz : z * z = 1 := H.xsub.z_mul_z
    have hzz₂ : z * z₂ = z₂ * z := (H.xsub.z_comm hz₂Q).symm
    refine ⟨⟨j, hQF hj⟩ * f, hcen _ (mul_mem (H.xsub.le_N hj) hfN) ?_, ?_⟩
    · show j * (f : G) * z₂ * (j * (f : G))⁻¹ = z₂
      calc j * (f : G) * z₂ * (j * (f : G))⁻¹ = j * ((f : G) * z₂ * (f : G)⁻¹) * j⁻¹ := by
            group
        _ = j * (z₂ * z) * j⁻¹ := by rw [h1]
        _ = (j * z₂ * j⁻¹) * (j * z * j⁻¹) := by group
        _ = z * z₂ * z := by
            rw [hjz, show j * z * j⁻¹ = z by rw [hzj, mul_inv_cancel_right]]
        _ = z₂ := by rw [hzz₂, mul_assoc, hzz, mul_one]
    · rw [map_mul]
      have hj1 : H.ρF ⟨j, hQF hj⟩ = 1 :=
        (H.ρG_eq_one_iff _).mpr (H.xsub.ρ_eq_one_of_mem (g := ⟨j, H.xsub.le_N hj⟩) hj)
      rw [hj1, one_mul]

end Sec38Hyp

end CFSG.ComponentClassification.AS81
