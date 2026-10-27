module

public import CFSG.LocalAnalysis.OddStandard.HigherRank.YamadaG23.Y54MDef
public import CFSG.LocalAnalysis.OddStandard.HigherRank.YamadaG23.Y54ASLc
public import CFSG.LocalAnalysis.OddStandard.HigherRank.YamadaG23.Y54Card
public import CFSG.LocalAnalysis.OddStandard.HigherRank.YamadaG23.Y54Sq

public section

namespace CFSG.OddStandard.HigherRank.YamadaG23

open Subgroup CFSG.Open CFSG.OddStandard.HigherRank.G2Three
  CFSG.OddStandard.HigherRank.G2Three.Sec1
open scoped commutatorElement

variable {G : Type} [Group G] [Finite G] {L : Subgroup G}

theorem y54_M_exists (c : Ctx5 G L) (hH : F33Hyp c.s c.e) : ∃ M : Subgroup G, IsM3Cand c.s M := by
  obtain ⟨M, h1, h2, h3, h4, h5⟩ :=
    asl_split_sub (F := c.s.fr.F) (X₀ := f4X0 c.s) (Y := f4Y c.s)
      (N := normIn L c.s.fr.F) (S := c.s.fr.S) (φ := f3phi c.s)
      (le_trans le_sup_left (y54_P_le_X0 hH)) (y54_X0_le_Y hH)
      (fun y hy f hf => by
        have hyc : y ∈ centralizer (↑(c.s.fr.F) : Set G) := (Subgroup.mem_inf.mp hy).2
        rw [show y * f = f * y from (Subgroup.mem_centralizer_iff.mp hyc f hf).symm, mul_assoc,
          mul_inv_cancel, mul_one]
        exact hf)
      (y54_Y_sq c hH)
      (fun n hn y hy => y54_N_norm_Y hH n (y54_NL_le_N hH hn) y hy)
      (fun n hn f hf => by
        have hnN : n ∈ normalizer (↑(c.s.fr.F) : Set G) := (Subgroup.mem_inf.mp hn).2
        exact (Subgroup.mem_normalizer_iff.mp hnN f).mp hf)
      (y54_NL_X0 hH)
      (y54_phi_mul hH) (y54_phi_mem hH) (y54_phi_eq_one hH) (y54_phi_surj hH)
      (fun n hn y _ => y54_phi_conj hH n (y54_NL_le_N hH hn) y)
      (y54_F_isE3 hH) (y54_trans2 hH) (y54_S_le_N hH) (y54_card_NS hH)
      (y54_d_mem_Y hH) (by rw [y54_phi_d hH]; exact y54_z_ne_one hH) (y54_S_fix_d hH)
  exact ⟨M, h1, h2, h3, h4, h5⟩

end CFSG.OddStandard.HigherRank.YamadaG23
