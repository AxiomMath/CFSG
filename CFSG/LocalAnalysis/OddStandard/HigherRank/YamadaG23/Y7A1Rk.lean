module

public import CFSG.LocalAnalysis.OddStandard.HigherRank.YamadaG23.Y7RHb
public import CFSG.LocalAnalysis.OddStandard.HigherRank.YamadaG23.Y7NMH
public import CFSG.LocalAnalysis.OddStandard.HigherRank.YamadaG23.Y7SFc
public import CFSG.LocalAnalysis.OddStandard.HigherRank.YamadaG23.Y31Q

public section

namespace CFSG.OddStandard.HigherRank.YamadaG23

open Subgroup CFSG.Open CFSG.OddStandard.HigherRank.G2Three
  CFSG.OddStandard.HigherRank.G2Three.Sec1

variable {G : Type} [Group G] [Finite G] {L : Subgroup G}

theorem y7a_rank_H (c : Ctx5 G L) (hH : F33Hyp c.s c.e) :
    ∀ E : Subgroup G, E ≤ centralizer ({c.s.t} : Set G) → IsElemAbelian 2 E →
      Nat.card ↥E ≤ 32 := by
  intro E hE hEab
  by_cases hRT : c.s.R = c.s.T
  ·
    have hTS : c.s.T = c.s.fr.S ⊔ zpowers c.s.t := by
      apply le_antisymm
      · intro r hr
        obtain ⟨x, hxS, q, hq, rfl⟩ := s3_R_eq_SQ c.s hH.hS hH.hZ r (hRT ▸ hr)
        rw [s3_Q_eq c.s hH.hS hH.hZ hH.hOut] at hq
        exact Subgroup.mul_mem _ (Subgroup.mem_sup_left hxS) (Subgroup.mem_sup_right hq)
      · exact sup_le (c.s.S_le_R.trans c.s.R_le_T)
          (Subgroup.zpowers_le.mpr (s3_t_mem_T c.s))
    have ht2 : c.s.t ^ 2 = 1 := by
      rw [← c.s.t_order]
      exact pow_orderOf_eq_one c.s.t
    have hcomm : ∀ x ∈ c.s.fr.S, x * c.s.t = c.s.t * x :=
      fun x hx => s3_comm_t_of_mem_L c.s (s3_S_le_L c.s hx)
    exact (cent_elem_bound (s3_rankFacts hH) ht2 hTS hcomm c.s.sylow_T
      E hE hEab).trans (by norm_num)
  ·
    exact y7n_mH_le hH.hDef hRT E hE hEab

end CFSG.OddStandard.HigherRank.YamadaG23
