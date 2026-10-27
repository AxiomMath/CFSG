module

public import CFSG.LocalAnalysis.OddStandard.HigherRank.YamadaG23.YTdict1
public import CFSG.LocalAnalysis.OddStandard.HigherRank.YamadaG23.YAutFrame

public section

namespace CFSG.OddStandard.HigherRank.YamadaG23

open Subgroup CFSG.Open CFSG.OddStandard.HigherRank.G2Three
  CFSG.OddStandard.HigherRank.G2Three.Sec1

variable {G : Type} [Group G] [Finite G] {L : Subgroup G} (s : Setting3 G L)

theorem s3_not_mem_M (hS : HRSetting G L) {x : G} (hx : x ∈ s.T) (hxR : x ∉ s.R) :
    x ∉ L ⊔ centIn s.H L := by
  intro hxM
  exact hxR (by rw [s3_R_eq s hS]; exact ⟨hx, hxM⟩)

theorem s3_outer_of_not_mem_M (hS : HRSetting G L) {x : G} (hxH : x ∈ s.H)
    (hxM : x ∉ L ⊔ centIn s.H L) {α : MulAut (L ⧸ center L)} (hα : ActsAs L x α) :
    α ∉ innerAut (L ⧸ center L) := by
  intro hαInn
  rw [← jSub_self] at hαInn
  obtain ⟨l, hl, hlα⟩ := (mem_jSub L).mp hαInn
  haveI : Group.IsPerfect ↥L := isPerfect_of_hrSetting (L := L) hS
  have hActs : ActsAs L (l⁻¹ * x) (1 : MulAut (L ⧸ center L)) := by
    simpa using actsAs_mul L (actsAs_inv L hlα) hα
  have hcen : l⁻¹ * x ∈ centralizer (L : Set G) := (actsAs_one_iff L).mp hActs
  have hlH : l⁻¹ ∈ s.H := s3_L_le_H s hS (Subgroup.inv_mem L hl)
  have hxinf : l⁻¹ * x ∈ centIn s.H L :=
    Subgroup.mem_inf.mpr ⟨Subgroup.mul_mem s.H hlH hxH, hcen⟩
  refine hxM ?_
  have hmem : l * (l⁻¹ * x) ∈ L ⊔ centIn s.H L := Subgroup.mul_mem_sup hl hxinf
  rwa [mul_inv_cancel_left] at hmem

theorem s3_jSub_H (hS : HRSetting G L) (hOut : (innerAut (L ⧸ center L)).index = 2)
    (hRT : s.R ≠ s.T) : jSub L s.H = ⊤ := by
  have hnotle : ¬ s.T ≤ s.R := fun h => hRT (le_antisymm h s.R_le_T).symm
  obtain ⟨x, hxT, hxR⟩ := SetLike.not_le_iff_exists.mp hnotle
  have hxH : x ∈ s.H := s.sylow_T.1 hxT
  have hxM : x ∉ L ⊔ centIn s.H L := s3_not_mem_M s hS hxT hxR
  have hxN : x ∈ normalizer (L : Set G) := s3_T_le_N s hS hxT
  let α : MulAut (L ⧸ center L) := jHom L ⟨x, hxN⟩
  have hαacts : ActsAs L x α := jHom_actsAs L ⟨x, hxN⟩
  have hαOut : α ∉ innerAut (L ⧸ center L) :=
    s3_outer_of_not_mem_M s hS hxH hxM hαacts
  have hInn_le : innerAut (L ⧸ center L) ≤ jSub L s.H := by
    rw [← jSub_self]
    exact jSub_mono L (s3_L_le_H s hS)
  have hα_mem : α ∈ jSub L s.H := (mem_jSub L).mpr ⟨x, hxH, hαacts⟩
  apply eq_top_iff.mpr
  intro β _
  by_cases hβ : β ∈ innerAut (L ⧸ center L)
  · exact hInn_le hβ
  · have hαinv : α⁻¹ ∉ innerAut (L ⧸ center L) :=
      fun h => hαOut (by simpa using Subgroup.inv_mem _ h)
    have hβα : β * α⁻¹ ∈ innerAut (L ⧸ center L) := by
      rw [Subgroup.mul_mem_iff_of_index_two hOut]
      exact ⟨fun h => absurd h hβ, fun h => absurd h hαinv⟩
    have hmem := Subgroup.mul_mem (jSub L s.H) (hInn_le hβα) hα_mem
    rwa [show (β * α⁻¹) * α = β from by group] at hmem

private theorem s3_map_jOn_T (hS : HRSetting G L) :
    (s.T.subgroupOf s.H).map (jOn L (s3_H_le_N s hS)) = jSub L s.T := by
  apply le_antisymm
  · intro α hα
    rw [Subgroup.mem_map] at hα
    obtain ⟨x, hx, rfl⟩ := hα
    rw [mem_jSub]
    exact ⟨(x : G), Subgroup.mem_subgroupOf.mp hx, jOn_actsAs L (s3_H_le_N s hS) x⟩
  · intro α hα
    rw [mem_jSub] at hα
    obtain ⟨g, hgT, hgα⟩ := hα
    rw [Subgroup.mem_map]
    refine ⟨⟨g, s.sylow_T.1 hgT⟩, ?_, ?_⟩
    · exact Subgroup.mem_subgroupOf.mpr hgT
    · exact actsAs_unique L (jOn_actsAs L (s3_H_le_N s hS) ⟨g, s.sylow_T.1 hgT⟩) hgα

theorem s3_jSub_T_normalizes (hS : HRSetting G L) :
    jSub L s.T ≤ normalizer (s.fr'.S : Set (MulAut (L ⧸ center L))) := by
  intro α hα
  rw [Subgroup.mem_normalizer_iff]
  have hforward : ∀ {a β : MulAut (L ⧸ center L)}, a ∈ jSub L s.T →
      β ∈ s.fr'.S → a * β * a⁻¹ ∈ s.fr'.S := by
    intro a β ha hβ
    rw [← s3_jSub_R s] at hβ ⊢
    obtain ⟨r, hr, hrβ⟩ := (mem_jSub L).mp hβ
    obtain ⟨x, hx, hxα⟩ := (mem_jSub L).mp ha
    refine (mem_jSub L).mpr ⟨x * r * x⁻¹, ?_, ?_⟩
    · have hN := s3_R_normal_T s hS
      have hmem : (⟨r, s.R_le_T hr⟩ : s.T) ∈ s.R.subgroupOf s.T :=
        Subgroup.mem_subgroupOf.mpr hr
      have h := hN.conj_mem _ hmem ⟨x, hx⟩
      simpa using Subgroup.mem_subgroupOf.mp h
    · have h1 := actsAs_mul L hxα hrβ
      have h2 := actsAs_inv L hxα
      simpa using actsAs_mul L h1 h2
  intro β
  constructor
  · exact fun hβ => hforward hα hβ
  · intro hβ
    have hαinv : α⁻¹ ∈ jSub L s.T := Subgroup.inv_mem _ hα
    have h := hforward hαinv hβ
    rwa [show α⁻¹ * (α * β * α⁻¹) * (α⁻¹)⁻¹ = β from by group] at h

theorem s3_jSub_T_isSylow (hS : HRSetting G L) (hOut : (innerAut (L ⧸ center L)).index = 2)
    (hRT : s.R ≠ s.T) : IsSylowIn 2 ⊤ (jSub L s.T) := by
  have hrange : (jOn L (s3_H_le_N s hS)).range = ⊤ := by
    rw [range_jOn]
    exact s3_jSub_H s hS hOut hRT
  have hsurj : Function.Surjective (jOn L (s3_H_le_N s hS)) :=
    MonoidHom.range_eq_top.mp hrange
  have hmap : (s.T.subgroupOf s.H).map (jOn L (s3_H_le_N s hS)) = jSub L s.T :=
    s3_map_jOn_T s hS
  refine ⟨le_top, isPGroup_jSub L s.sylow_T.2.1, ?_⟩
  rw [Subgroup.relIndex_top_right]
  intro hdiv
  have hidx : 2 ∣ ((s.T.subgroupOf s.H).map (jOn L (s3_H_le_N s hS))).index := by
    rwa [← hmap] at hdiv
  exact s.sylow_T.2.2
    (hidx.trans (Subgroup.index_map_dvd (H := s.T.subgroupOf s.H) hsurj))

theorem s3_jSub_T (hS : HRSetting G L) (hOut : (innerAut (L ⧸ center L)).index = 2)
    (hRT : s.R ≠ s.T) : jSub L s.T = s.fr'.Sσ := by
  refine sylowIn_eq_of_le (V := ⊤) (P := jSub L s.T) (Q := s.fr'.Sσ)
    (s3_jSub_T_isSylow s hS hOut hRT) ?_ le_top ?_
  · exact frame_Sσ_isPGroup s.fr' s.facts.1
  · exact (s3_jSub_T_normalizes s hS).trans (frame_normalizer_S_le s.fr' s.facts hOut)

end CFSG.OddStandard.HigherRank.YamadaG23
