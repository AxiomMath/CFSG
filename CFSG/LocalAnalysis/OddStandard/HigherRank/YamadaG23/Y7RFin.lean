module

public import CFSG.LocalAnalysis.OddStandard.HigherRank.YamadaG23.Y7RTr
public import CFSG.LocalAnalysis.OddStandard.HigherRank.YamadaG23.Y7SFc
public import CFSG.LocalAnalysis.OddStandard.HigherRank.YamadaG23.Y7Split
public import CFSG.LocalAnalysis.OddStandard.HigherRank.YamadaG23.Y5Final
public import CFSG.LocalAnalysis.OddStandard.HigherRank.YamadaG23.Y31Q

public section

namespace CFSG.OddStandard.HigherRank.YamadaG23

open Subgroup CFSG.Open CFSG.OddStandard.HigherRank.G2Three
  CFSG.OddStandard.HigherRank.G2Three.Sec1

@[expose] def Sec7WreathRT : Prop :=
  ∀ (G : Type) [Group G] [Finite G] (L : Subgroup G), HRSetting G L → HRG23 (L ⧸ center L) →
    ∀ c : Ctx7 G L, c.toCtx5.Facts5 → c.s.R = c.s.T →
      ∃ P U : Subgroup G, Wr7 c.s.t P U ∧ P ⊓ centralizer ({c.s.t} : Set G) = c.s.fr.S

theorem sec7SylowRT_of (hB : Sec3Inputs) (hW : Sec7WreathRT) : Sec7SylowRT := by
  intro G _ _ L hS hL c h5 hRT
  obtain ⟨P, U, hwr, hcP⟩ := hW G L hS hL c h5 hRT
  have hH := f33hyp_of hB hS hL c.s c.e
  have htP : c.s.t ∉ P := by
    intro htP
    have htS : c.s.t ∈ c.s.fr.S :=
      hcP ▸ Subgroup.mem_inf.mpr ⟨htP, Subgroup.mem_centralizer_singleton_iff.mpr rfl⟩
    have h1 : c.s.t = 1 := s3_S_inf_cent c.s hS hH.hZ c.s.t htS c.s.t_mem
    have h2 := c.s.t_order
    rw [h1, orderOf_one] at h2
    exact absurd h2 (by norm_num)
  have hQ := s3_Q_eq c.s hS hH.hZ hH.hOut
  have hTS : c.s.T = c.s.fr.S ⊔ zpowers c.s.t := by
    apply le_antisymm
    · intro r hr
      obtain ⟨x, hxS, q, hq, rfl⟩ := s3_R_eq_SQ c.s hS hH.hZ r (hRT ▸ hr)
      rw [hQ] at hq
      exact Subgroup.mul_mem _ (Subgroup.mem_sup_left hxS) (Subgroup.mem_sup_right hq)
    · exact sup_le (c.s.S_le_R.trans c.s.R_le_T) (Subgroup.zpowers_le.mpr (s3_t_mem_T c.s))
  exact hwr.transfer_data (s3_rankFacts hH) c.s.sylow_S.2.1 hcP htP
    (fun x hx => s3_comm_t_of_mem_L c.s (s3_S_le_L c.s hx)) hTS c.s.sylow_T

end CFSG.OddStandard.HigherRank.YamadaG23
