module

public import CFSG.LocalAnalysis.OddStandard.HigherRank.YamadaG23.Y6F4AE1
public import CFSG.LocalAnalysis.OddStandard.HigherRank.YamadaG23.Y6F4AI
public import CFSG.LocalAnalysis.OddStandard.HigherRank.YamadaG23.Y6E26C

public section

namespace CFSG.OddStandard.HigherRank.YamadaG23

open Subgroup CFSG.Open CFSG.OddStandard.HigherRank.G2Three
  CFSG.OddStandard.HigherRank.G2Three.Sec1

variable {G : Type} [Group G] [Finite G] {L : Subgroup G}

theorem y6f4a_ctx_M_cent (c : Ctx5 G L) (hF : c.Facts5) (hRT : c.s.R ≠ c.s.T) :
    ∀ m ∈ M3 c.s, c.g * m = m * c.g := by
  intro m hm
  have h := hF.2.2.2.1 hRT m hm
  rwa [mul_inv_eq_iff_eq_mul] at h

theorem y6f4a_ctx_M_inv (c : Ctx6 G L) (hH : F33Hyp c.s c.e) (hF : c.toCtx5.Facts5) :
    ∀ m ∈ M3 c.s, c.s.t * m * c.s.t⁻¹ = m⁻¹ := by
  rcases hF.2.2.2.2.2.2 with ⟨-, hE⟩ | ⟨-, -, -, hinv⟩
  · exfalso
    have hA : LFactsA c.s := lfactsA_of_setting hH.hS hH.hZ c.s
    have hz2 : orderOf c.s.fr.z = 2 := s3_z_order c.s hA
    obtain ⟨hord, -⟩ := Ctx5pre.u_facts c.toCtx5.toCtx5pre hz2
    have hdt : c.d * c.s.t ∈ V1 c.e := by
      rw [c.hV]
      exact Subgroup.mem_zpowers _
    have hdtM : c.d * c.s.t ∈ M3 c.s := (inf_le_right : V1 c.e ≤ M3 c.s) hdt
    have h2 : (c.d * c.s.t) ^ 2 = 1 := hE.2 _ hdtM
    have hdvd : orderOf (c.d * c.s.t) ∣ 2 := orderOf_dvd_of_pow_eq_one h2
    rw [hord] at hdvd
    omega
  · exact hinv

theorem y6f4a_ctx_g_not_mem_M (c : Ctx5 G L) (hH : F33Hyp c.s c.e) (hRT : c.s.R ≠ c.s.T) :
    c.g ∉ M3 c.s := by
  intro hgM
  have hgE : c.g ∈ y6bE c := y6b_E16_le_E c (y6b_g_mem_E16 c)
  have hgF : c.g ∈ y6bE c ⊓ M3 c.s := Subgroup.mem_inf.mpr ⟨hgE, hgM⟩
  rw [y6b_E_inf_M3 c hH hRT] at hgF
  exact y6b_g_not_mem_F c hH hRT hgF

theorem y6f4a_gData_of_ctx (c : Ctx6 G L) (hH : F33Hyp c.s c.e) (hF : c.toCtx5.Facts5)
    (hRT : c.s.R ≠ c.s.T)
    (hNH : centralizer ({c.g} : Set G) ⊓
      normalizer ((zpowers c.g ⊔ zpowers c.s.t : Subgroup G) : Set G) ≤ c.s.H) :
    Y6GData c.g c.s.t (centEl L c.g) (M3 c.s) := by
  have hg2 : c.g ^ 2 = 1 := by simpa [pow_two] using y6b_g_sq c.toCtx5 hRT
  have hord := y6f4a_ctx_g_order c.toCtx5 hRT
  have hg1 : c.g ≠ 1 := by
    intro h
    rw [h, orderOf_one] at hord
    omega
  have hcomm := y6b_g_comm_t c.toCtx5 hRT
  refine ⟨hord, c.s.t_order, hcomm, y6f4a_ctx_t_ne_g c.toCtx5 hRT, ?_,
    y6f4a_ctx_D_eq c.toCtx5 hH hRT, y6f4a_ctx_P_inf c.toCtx5 hH hRT,
    y6f4a_ctx_P_equiv c.toCtx5 hH hRT, y6f4a_ctx_P_four c.toCtx5 hH hRT,
    y6e_M3_equiv c hH hF, y6f4a_ctx_M_cent c.toCtx5 hF hRT, y6f4a_ctx_M_inv c hH hF,
    y6f4a_ctx_g_not_mem_M c.toCtx5 hH hRT⟩
  exact y6f4a_no_conj_of_normalizer hg2 hg1 hcomm hNH

end CFSG.OddStandard.HigherRank.YamadaG23
