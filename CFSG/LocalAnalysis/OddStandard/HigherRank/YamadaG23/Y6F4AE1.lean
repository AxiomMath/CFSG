module

public import CFSG.LocalAnalysis.OddStandard.HigherRank.YamadaG23.Y6F4AC
public import CFSG.LocalAnalysis.OddStandard.HigherRank.YamadaG23.Y6F4AC2
public import CFSG.LocalAnalysis.OddStandard.HigherRank.YamadaG23.Y6B4A

public section

namespace CFSG.OddStandard.HigherRank.YamadaG23

open Subgroup CFSG.Open CFSG.OddStandard.HigherRank.G2Three
  CFSG.OddStandard.HigherRank.G2Three.Sec1

variable {G : Type} [Group G] [Finite G] {L : Subgroup G}

theorem y6f4a_ctx_g_order (c : Ctx5 G L) (hRT : c.s.R ≠ c.s.T) : orderOf c.g = 2 := by
  have hg2 : c.g ^ 2 = 1 := by simpa [pow_two] using y6b_g_sq c hRT
  have hg1 : c.g ≠ 1 := by
    intro h
    exact (c.g_spec hRT).2.1 (h ▸ c.s.R.one_mem)
  exact orderOf_eq_prime hg2 hg1

theorem y6f4a_ctx_t_ne_g (c : Ctx5 G L) (hRT : c.s.R ≠ c.s.T) : c.s.t ≠ c.g := by
  intro h
  exact (c.g_spec hRT).2.1 (h ▸ s3_t_mem_R c.s)

theorem y6f4a_ctx_P_inf (c : Ctx5 G L) (hH : F33Hyp c.s c.e) (hRT : c.s.R ≠ c.s.T) :
    centEl L c.g ⊓ closure ({c.g, c.s.t} : Set G) = ⊥ := by
  have hg2 : c.g ^ 2 = 1 := by simpa [pow_two] using y6b_g_sq c hRT
  have ht2 : c.s.t ^ 2 = 1 := by simpa [pow_two] using y6b_t_sq c
  have hgM := y6b_g_not_mem_M c hH hRT
  have htH : c.s.t ∈ centIn c.s.H L :=
    Subgroup.mem_inf.mpr ⟨Subgroup.mem_centralizer_singleton_iff.mpr rfl, c.s.t_mem⟩
  refine y6f4a_P_inf_of_not_mem (L := L) inf_le_left hg2 ht2 (y6b_g_comm_t c hRT)
    (fun h => hgM (Subgroup.mem_sup_left h)) (s3_t_not_mem_L c.s hH.h31) ?_
  intro h
  apply hgM
  have h' := Subgroup.mul_mem_sup h ((centIn c.s.H L).inv_mem htH)
  rwa [mul_inv_cancel_right] at h'

theorem y6f4a_ctx_D_eq (c : Ctx5 G L) (hH : F33Hyp c.s c.e) (hRT : c.s.R ≠ c.s.T) :
    centralizer ({c.g} : Set G) ⊓ centralizer ({c.s.t} : Set G) =
      centEl L c.g ⊔ closure ({c.g, c.s.t} : Set G) := by
  haveI : Group.IsPerfect ↥L := isPerfect_of_hrSetting hH.hS
  refine y6f4a_D_decomp (by simpa [pow_two] using y6b_g_sq c hRT) (y6b_g_comm_t c hRT)
    (c.g_spec hRT).2.2.1 c.s.t_mem (s3_H_le_N c.s hH.hS) ?_ ?_ ?_
  · intro x hx hxc
    have hx' : x ∈ centIn c.s.H L := Subgroup.mem_inf.mpr ⟨hx, hxc⟩
    rwa [f3_centIn_H_L hH] at hx'
  · exact frame_inner_sup_sigma c.s.fr' c.s.facts.1 hH.hOut
  · exact frame_sigma_sq c.s.fr' c.s.facts.1

theorem y6f4a_ctx_P_equiv (c : Ctx5 G L) (hH : F33Hyp c.s c.e) (hRT : c.s.R ≠ c.s.T) :
    Nonempty (↥(centEl L c.g) ≃*
      MulAut (Matrix.ProjectiveSpecialLinearGroup (Fin 2) (GaloisField 2 3))) := by
  haveI : Group.IsPerfect ↥L := isPerfect_of_hrSetting hH.hS
  have hZ : center ↥L = ⊥ :=
    (Subgroup.map_eq_bot_iff_of_injective (center ↥L) (Subgroup.subtype_injective L)).mp
      (f3_zL_eq_bot hH)
  obtain ⟨e1⟩ := y6f4a_centEl_equiv hZ (c.g_spec hRT).2.2.1
  obtain ⟨⟨e2⟩, -⟩ := c.s.facts.2.2.2.2.2.2.1
  exact ⟨e1.trans e2⟩

theorem y6f4a_ctx_P_four (c : Ctx5 G L) (hH : F33Hyp c.s c.e) (hRT : c.s.R ≠ c.s.T) :
    ∀ p ∈ centEl L c.g, p ^ 4 = 1 → p ^ 2 = 1 := by
  haveI : Group.IsPerfect ↥L := isPerfect_of_hrSetting hH.hS
  have hZ : center ↥L = ⊥ :=
    (Subgroup.map_eq_bot_iff_of_injective (center ↥L) (Subgroup.subtype_injective L)).mp
      (f3_zL_eq_bot hH)
  obtain ⟨e⟩ := y6f4a_centEl_equiv hZ (c.g_spec hRT).2.2.1
  obtain ⟨-, hsyl⟩ := c.s.facts.2.2.2.2.2.2.1
  have hexp : ∀ x ∈ c.s.fr'.F, x ^ 2 = 1 := by
    intro x hx
    have hx' : x ∈ c.s.fr'.F ⊔ closure {c.s.fr'.σ} := Subgroup.mem_sup_left hx
    have h := c.s.facts.2.2.2.2.1.2.2.2.1.2.1.1.2 ⟨x, hx'⟩ (Subgroup.mem_top _)
    exact congrArg Subtype.val h
  intro p hp hp4
  have h4 : (⟨p, hp⟩ : ↥(centEl L c.g)) ^ 4 = 1 := Subtype.ext hp4
  have hq4 : (e ⟨p, hp⟩) ^ 4 = 1 := by rw [← map_pow, h4, map_one]
  have hq : ((e ⟨p, hp⟩ : ↥(centEl (innerAut (L ⧸ center L)) c.s.fr'.σ)) :
      MulAut (L ⧸ center L)) ^ 2 = 1 :=
    y6f4a_sq_eq_one_of_sylow_exp_two hsyl hexp (e ⟨p, hp⟩).2 (congrArg Subtype.val hq4)
  have h2 : e ((⟨p, hp⟩ : ↥(centEl L c.g)) ^ 2) = e 1 := by
    rw [map_pow, map_one]
    exact Subtype.ext hq
  exact congrArg Subtype.val (e.injective h2)

end CFSG.OddStandard.HigherRank.YamadaG23
