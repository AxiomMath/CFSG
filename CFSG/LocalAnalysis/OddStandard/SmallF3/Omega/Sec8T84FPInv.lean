module

public import CFSG.LocalAnalysis.OddStandard.SmallF3.Omega.Sec8T84Defs
import CFSG.LocalAnalysis.SectionRank.PRank

public section

namespace CFSG.OddStandard.SmallF3.Omega

open Subgroup

private theorem isElemAb2_map {G G' : Type} [Group G] [Group G'] (θ : G ≃* G')
    {K : Subgroup G} {k : ℕ} (h : IsElemAb2 K k) : IsElemAb2 (K.map θ.toMonoidHom) k :=
  ⟨CFSG.SectionRank.isElemAbelian_map h.1 θ.toMonoidHom,
    by rw [Subgroup.card_map_of_injective θ.injective, h.2]⟩

private theorem isElemAb2_comap {G G' : Type} [Group G] [Group G'] (θ : G ≃* G')
    {K' : Subgroup G'} {k : ℕ} (h : IsElemAb2 K' k) : IsElemAb2 (K'.comap θ.toMonoidHom) k := by
  rw [Subgroup.comap_equiv_eq_map_symm' θ K']
  exact isElemAb2_map θ.symm h

private theorem normal_subgroupOf_map {G G' : Type} [Group G] [Group G'] (θ : G ≃* G')
    {H K : Subgroup G} (hHK : H ≤ K) (hN : (H.subgroupOf K).Normal) :
    ((H.map θ.toMonoidHom).subgroupOf (K.map θ.toMonoidHom)).Normal := by
  rw [Subgroup.normal_subgroupOf_iff (Subgroup.map_mono hHK)]
  intro f p hf hp
  obtain ⟨f₀, hf₀, rfl⟩ := Subgroup.mem_map.mp hf
  obtain ⟨p₀, hp₀, rfl⟩ := Subgroup.mem_map.mp hp
  refine ⟨p₀ * f₀ * p₀⁻¹, (Subgroup.normal_subgroupOf_iff hHK).mp hN f₀ p₀ hf₀ hp₀, ?_⟩
  simp only [map_mul, map_inv]

private theorem map_centralizer_eq {G G' : Type} [Group G] [Group G'] (θ : G ≃* G')
    (S : Set G) :
    (Subgroup.centralizer S).map θ.toMonoidHom = Subgroup.centralizer (θ.toMonoidHom '' S) := by
  ext x
  rw [Subgroup.mem_map]
  constructor
  · rintro ⟨y, hy, rfl⟩
    rw [Subgroup.mem_centralizer_iff] at hy ⊢
    intro h hh
    obtain ⟨z, hz, rfl⟩ := hh
    rw [← map_mul, ← map_mul, hy z hz]
  · intro hx
    refine ⟨θ.symm x, ?_, θ.apply_symm_apply x⟩
    rw [Subgroup.mem_centralizer_iff] at hx ⊢
    intro z hz
    apply θ.injective
    rw [map_mul, map_mul, θ.apply_symm_apply]
    exact hx (θ z) ⟨z, hz, rfl⟩

private theorem map_centralizer_eq' {G G' : Type} [Group G] [Group G'] (θ : G ≃* G')
    (K : Subgroup G) : (Subgroup.centralizer (K : Set G)).map θ.toMonoidHom =
      Subgroup.centralizer ((K.map θ.toMonoidHom : Subgroup G') : Set G') := by
  rw [Subgroup.coe_map, map_centralizer_eq]

private theorem map_centralizer_singleton {G G' : Type} [Group G] [Group G'] (θ : G ≃* G')
    (s : G) : (Subgroup.centralizer ({s} : Set G)).map θ.toMonoidHom =
      Subgroup.centralizer ({θ s} : Set G') := by
  rw [map_centralizer_eq, Set.image_singleton, MulEquiv.coe_toMonoidHom]

private theorem pRank_map_eq {G G' : Type} [Group G] [Finite G] [Group G'] [Finite G']
    (θ : G ≃* G') (K : Subgroup G) :
    CFSG.Open.pRank 2 (K.map θ.toMonoidHom) = CFSG.Open.pRank 2 K := by
  refine le_antisymm ?_
    (CFSG.SectionRank.pRank_le_map (p := 2) (by norm_num) θ.toMonoidHom θ.injective K)
  have h2 : (K.map θ.toMonoidHom).map θ.symm.toMonoidHom = K := by
    ext x
    simp only [Subgroup.mem_map_equiv, MulEquiv.symm_symm, MulEquiv.symm_apply_apply]
  have h := CFSG.SectionRank.pRank_le_map (p := 2) (by norm_num) θ.symm.toMonoidHom
    θ.symm.injective (K.map θ.toMonoidHom)
  rwa [h2] at h

private theorem comap_le_of_map_le {G G' : Type} [Group G] [Group G'] (θ : G ≃* G')
    {K' : Subgroup G'} {P : Subgroup G} (h : K' ≤ P.map θ.toMonoidHom) :
    K'.comap θ.toMonoidHom ≤ P := by
  have h' : (K'.comap θ.toMonoidHom).map θ.toMonoidHom ≤ P.map θ.toMonoidHom := by
    rw [Subgroup.map_comap_eq_self_of_surjective θ.surjective K']
    exact h
  rw [Subgroup.map_le_iff_le_comap, Subgroup.comap_map_eq_self_of_injective θ.injective P] at h'
  exact h'

theorem Sec8T84PFacts.map {Y Y' : Type} [Group Y] [Finite Y] [Group Y'] [Finite Y']
    (θ : Y ≃* Y') {E P F : Subgroup Y} (h : Sec8T84PFacts Y E P F) :
    Sec8T84PFacts Y' (E.map θ.toMonoidHom) (P.map θ.toMonoidHom) (F.map θ.toMonoidHom) := by
  refine ⟨Subgroup.map_mono h.E_le, Subgroup.map_mono h.F_le, isElemAb2_map θ h.F_e16, ?_, ?_,
    ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact fun heq => h.F_ne (Subgroup.map_injective θ.injective heq)
  · exact normal_subgroupOf_map θ h.F_le h.F_norm
  · intro F' hFP hE4
    have hKP : F'.comap θ.toMonoidHom ≤ P := comap_le_of_map_le θ hFP
    have hK4 : IsElemAb2 (F'.comap θ.toMonoidHom) 4 := isElemAb2_comap θ hE4
    rcases h.only (F'.comap θ.toMonoidHom) hKP hK4 with hKE | hKF
    · left
      have h1 : (F'.comap θ.toMonoidHom).map θ.toMonoidHom = E.map θ.toMonoidHom := by rw [hKE]
      rw [Subgroup.map_comap_eq_self_of_surjective θ.surjective F'] at h1
      exact h1
    · right
      have h1 : (F'.comap θ.toMonoidHom).map θ.toMonoidHom = F.map θ.toMonoidHom := by rw [hKF]
      rw [Subgroup.map_comap_eq_self_of_surjective θ.surjective F'] at h1
      exact h1
  · intro F' hFP hE5
    exact h.no32 (F'.comap θ.toMonoidHom) (comap_le_of_map_le θ hFP) (isElemAb2_comap θ hE5)
  · rw [← Subgroup.map_sup, Subgroup.card_map_of_injective θ.injective, h.J_card]
  · rw [← Subgroup.map_inf E F θ.toMonoidHom θ.injective,
      Subgroup.card_map_of_injective θ.injective, h.EF_card]
  · intro s hs
    have hs' : orderOf (θ.symm s) = 2 := by rw [MulEquiv.orderOf_eq θ.symm s, hs]
    have hmap : (Subgroup.centralizer ({θ.symm s} : Set Y)).map θ.toMonoidHom =
        Subgroup.centralizer ({s} : Set Y') := by
      rw [map_centralizer_singleton]
      simp
    rw [← hmap, pRank_map_eq θ (Subgroup.centralizer ({θ.symm s} : Set Y)),
      h.rank_cent (θ.symm s) hs']
  · rw [← map_centralizer_eq' θ E,
      ← Subgroup.map_inf P (Subgroup.centralizer (E : Set Y)) θ.toMonoidHom θ.injective, h.cent_E]
  · rw [← map_centralizer_eq' θ F,
      ← Subgroup.map_inf P (Subgroup.centralizer (F : Set Y)) θ.toMonoidHom θ.injective, h.cent_F]
  · obtain ⟨y, hy_ord, hy_norm, hy_cent, s, hsP, hsJ, hs_ord, hs_conj, hsp⟩ := h.y_exists
    refine ⟨θ y, ?_, ?_, ?_, θ s, ?_, ?_, ?_, ?_, ?_⟩
    · rw [MulEquiv.orderOf_eq θ y, hy_ord]
    · have h1 : θ y ∈ (Subgroup.normalizer ((E ⊔ F : Subgroup Y) : Set Y)).map
          θ.toMonoidHom :=
        Subgroup.mem_map_of_mem θ.toMonoidHom hy_norm
      rw [Subgroup.map_equiv_normalizer_eq (E ⊔ F) θ, Subgroup.map_sup] at h1
      exact h1
    · intro u hu hcomm
      rw [← Subgroup.map_sup] at hu
      obtain ⟨v, hv, rfl⟩ := Subgroup.mem_map.mp hu
      have hvu : y * v = v * y := θ.injective (by rw [map_mul, map_mul]; exact hcomm)
      rw [hy_cent v hv hvu, map_one]
    · exact Subgroup.mem_map_of_mem θ.toMonoidHom hsP
    · intro hsJ'
      rw [← Subgroup.map_sup] at hsJ'
      obtain ⟨v, hv, hveq⟩ := Subgroup.mem_map.mp hsJ'
      rw [θ.injective hveq] at hv
      exact hsJ hv
    · rw [MulEquiv.orderOf_eq θ s, hs_ord]
    · calc θ s * θ y * (θ s)⁻¹ = θ (s * y * s⁻¹) := by simp only [map_mul, map_inv]
        _ = θ (y⁻¹) := by rw [hs_conj]
        _ = (θ y)⁻¹ := by rw [map_inv]
    · rw [hsp, Subgroup.map_sup, Subgroup.map_sup, MonoidHom.map_zpowers,
        MulEquiv.coe_toMonoidHom]

end CFSG.OddStandard.SmallF3.Omega
