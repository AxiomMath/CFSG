module

public import CFSG.LocalAnalysis.EvenBN.Tits.N.P21Alpha
public import CFSG.LocalAnalysis.EvenBN.Tits.N.P3Base

public section

namespace CFSG.LocalAnalysis.EvenBN.Tits.N

open Subgroup CFSG.Open CFSG.Sporadic.Schreier.Tits

section NoCerts

variable {G : Type} [Group G] {d : Data G} {z₀ : G}

theorem p21_t_mem_sylT (h09 : Node09 d z₀) : d.t ∈ sylT d := by
  obtain ⟨-, -, -, -, -, -, -, -, -, h10, -⟩ := h09
  have h : d.t ∈ zpowers d.t ⊔ (sylT d ⊓ centralizer ({z₀} : Set G)) :=
    mem_sup_left (mem_zpowers _)
  rwa [← h10] at h

theorem p21_mem_sylT_iff {g : G} :
    g ∈ sylT d ↔ ∃ hg : g ∈ centralizer ({d.t} : Set G),
      (d.ρ ⟨g, hg⟩ : Equiv.Perm (Fin 1755)) ∈ Model.parrottU 1 := by
  unfold sylT
  rw [Subgroup.mem_map]
  constructor
  · rintro ⟨x, hx, rfl⟩
    exact ⟨x.2, by simpa [Subgroup.mem_comap, Subgroup.mem_subgroupOf] using hx⟩
  · rintro ⟨hg, h⟩
    exact ⟨⟨g, hg⟩, by simpa [Subgroup.mem_comap, Subgroup.mem_subgroupOf] using h, rfl⟩

end NoCerts

section Certs4

variable {G : Type} [Group G] {d : Data G} {z₀ : G}

theorem p21_Ks_le_normalizer_Ws (h20 : Node20 d z₀) :
    Ks d ≤ normalizer ((Ws d : Subgroup (MulAut ↥d.s56V)) : Set (MulAut ↥d.s56V)) := by
  intro k hk
  have h1 : maxElemAbelian2 (Ks d) = {Ws d} := h20.1
  have hW : Ws d ∈ maxElemAbelian2 (Ks d) := by rw [h1]; exact rfl
  obtain ⟨hWK, hWab, hWmax⟩ := hW
  have hWab' : IsElemAbelian 2 (Ws d) := hWab
  have hconj : (Ws d).map (MulAut.conj k).toMonoidHom ∈ maxElemAbelian2 (Ks d) := by
    refine ⟨?_, hWab'.map _, fun D hD hDab => ?_⟩
    · rintro _ ⟨w, hw, rfl⟩
      exact mul_mem (mul_mem hk (hWK hw)) (inv_mem hk)
    · rw [Subgroup.card_map_of_injective (MulAut.conj k).injective]
      exact hWmax D hD hDab
  rw [h1] at hconj
  exact mem_normalizer_iff_map_conj_eq.2 (Set.mem_singleton_iff.1 hconj)

theorem p21_Ks_le_Is (h20 : Node20 d z₀) : Ks d ≤ Is d :=
  le_inf (p21_Ks_le_normalizer_Ws h20) inf_le_right

theorem p21_img_Xg_le_Is (h19b : Node19b d z₀) (h20 : Node20 d z₀) : img d (Xg d) ≤ Is d :=
  h19b.trans (p21_Ks_le_Is h20)

theorem p21_t_mem_Ig (h09 : Node09 d z₀) (h20 : Node20 d z₀) : d.t ∈ Ig d :=
  h20.2.2.1 (p21_t_mem_sylT h09)

theorem p21_y1_mem_Ig (h20 : Node20 d z₀) {y₁ : G} (hy : IsV1 d z₀ y₁) : y₁ ∈ Ig d :=
  h20.2.2.1 hy.1

end Certs4

section Medium

variable {G : Type} [Group G] [Finite G] {d : Data G} {z₀ : G}


theorem p21_pv2_mem_sylT (hd : d.Hyp) : d.pv 2 ∈ sylT d := by
  have h2D : Model.parrottV 2 ∈ titsD :=
    (Model.parrottV_mem_titsD_iff (by norm_num)).2 (by decide)
  have hmem : d.pv 2 ∈ centralizer ({d.t} : Set G) := hd.L_le (d.lift_mem _)
  rw [p21_mem_sylT_iff]
  refine ⟨hmem, ?_⟩
  have e : (d.ρ ⟨d.pv 2, hmem⟩ : Equiv.Perm (Fin 1755)) = Model.parrottV 2 := hd.ρ_lift h2D
  rw [e]
  exact Subgroup.subset_closure ⟨2, by simp, rfl⟩

end Medium

section Medium4

variable {G : Type} [Group G] [Finite G] {d : Data G} {z₀ : G}


theorem p21_pv2_mem_Ig (hd : d.Hyp) (h20 : Node20 d z₀) : d.pv 2 ∈ Ig d :=
  h20.2.2.1 (p21_pv2_mem_sylT hd)

end Medium4

section Heavy

variable {G : Type} [Group G] [Finite G] {d : Data G} {z₀ : G}


theorem p21_x5_mem_Ig (h49 : d.Thm49Statement) (hd : d.Hyp) (h19b : Node19b d z₀)
    (h20 : Node20 d z₀) : d.x₅ ∈ Ig d := by
  refine mem_Ig_iff.2 ⟨x5_mem_Hg h49 hd, ?_⟩
  have h1 : star d d.x₅ ∈ img d (Xg d) := actFun_mem_imgIn (mem_zpowers d.x₅) (x5_mem_Hg h49 hd)
  exact p21_img_Xg_le_Is h19b h20 h1

theorem p21_star_z (h49 : d.Thm49Statement) (hd : d.Hyp) : star d d.z = 1 := by
  have hzV : d.z ∈ d.s56V := hd.s56_E_le_V h49 hd.s56_z_mem_E
  refine (actFun_eq_one_iff d.s56V (le_normalizer hzV)).2 (mem_centralizer_iff.2 fun v hv => ?_)
  exact Data.s56_V_comm_E hv hd.s56_z_mem_E

theorem p21_z_mem_Ig (h49 : d.Thm49Statement) (hd : d.Hyp) : d.z ∈ Ig d := by
  refine mem_Ig_iff.2 ⟨le_normalizer (hd.s56_E_le_V h49 hd.s56_z_mem_E), ?_⟩
  rw [p21_star_z h49 hd]
  exact one_mem _

theorem p21_alpha_z (h49 : d.Thm49Statement) (hd : d.Hyp) : alpha d d.z = 1 := by
  unfold alpha
  rw [p21_star_z h49 hd, actFun_one]

end Heavy

end CFSG.LocalAnalysis.EvenBN.Tits.N
