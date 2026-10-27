module

public import CFSG.LocalAnalysis.OddStandard.HigherRank.YamadaG23.Y56Aut2
public import CFSG.LocalAnalysis.OddStandard.HigherRank.YamadaG23.Y56Sq
public import CFSG.LocalAnalysis.OddStandard.HigherRank.YamadaG23.Y56Y0
public import CFSG.LocalAnalysis.OddStandard.HigherRank.YamadaG23.Y56ASEc

public section

namespace CFSG.OddStandard.HigherRank.YamadaG23

open Subgroup CFSG.Open CFSG.OddStandard.HigherRank.G2Three
  CFSG.OddStandard.HigherRank.G2Three.Sec1
open scoped commutatorElement

variable {G : Type} [Group G] [Finite G] {L : Subgroup G}

theorem y56_M_exists (c : Ctx5 G L) (hH : F33Hyp c.s c.e) :
    ∃ M : Subgroup G, IsC4Cand c.s c.d M := by
  obtain ⟨y₀, hy₀⟩ := y56_exists_y0 c hH
  obtain ⟨M, hQM, hMY, hMN, hMX, hMYX, hdM⟩ :=
    ase_split_sub (Q := e4Q c.s) (X₀ := e4X0 c.s) (Y := e4Y c.s) (N := normIn L c.s.fr.E)
      (E := c.s.fr.E) (φ := f3phi c.s) (z := c.s.fr.z) (wz := c.d) (v₀ := y56v0 c.s)
      (w₀ := y₀) (a := y5a c.s)
      (y56_Q_le_X0 hH) (y56_X0_le_Y hH) (y56_Y_norm_Q hH) (y56_Y_sq c hH)
      (fun n hn y hy => y56_N_norm_Y hH n (y56_NL_le_N hH hn) y hy)
      (fun n hn q hq => y56_N_norm_Q hH n (y56_NL_le_N hH hn) q hq)
      (fun n hn f hf => by
        have hnN : n ∈ normalizer (c.s.fr.E : Set G) := (Subgroup.mem_inf.mp hn).2
        exact (Subgroup.mem_normalizer_iff.mp hnN f).mp hf)
      (fun n hn x hx => Subgroup.mem_sup_left (y56_NL_X0 hH n hn x hx))
      (y56_phi_mul hH) (y56_phi_mem hH) (y56_phi_eq_one hH) (y56_phi_surj c hH)
      (fun n hn y _ => y56_phi_conj hH n (y56_NL_le_N hH hn) y)
      (y56_E_isE3 hH) (y56_z_mem_E hH) (y56_v0 hH).2.2.2.1 (y56_NE_le_Cz hH)
      (fun a ha b hb ha1 haz hb1 hbz => y56_NE_trans hH a ha ha1 haz b hb hb1 hbz)
      (y56_NE_pairs hH)
      (y56_d_mem_Y c hH) (y56_phi_d c hH) (y56_NE_fix_d c hH)
      (y56_V_le_E hH (y56_v0 hH).1) (y56_v0 hH).2.2.1 (y56_v0 hH).2.2.2.2.1
      (y56_y0_mem_Y hH hy₀) (y56_phi_y0 hy₀)
      (fun n hn hv => y56_y0_B_fix c hH hy₀ n (y56_stab_v0 hH n hn hv))
      (y56_A_le_NE hH (y5a_mem_A c.s)) (y5a_conj_w (s := c.s) hH) (y56_y0_a c hH hy₀)
  exact ⟨M, hQM, hMY, hMN, hMX, hMYX, hdM⟩

end CFSG.OddStandard.HigherRank.YamadaG23
