module

public import CFSG.LocalAnalysis.OddStandard.HigherRank.YamadaG23.Y7NAb
public import CFSG.LocalAnalysis.OddStandard.HigherRank.YamadaG23.Y7NCk
public import CFSG.LocalAnalysis.OddStandard.HigherRank.YamadaG23.Y7NGn
public import CFSG.LocalAnalysis.OddStandard.HigherRank.YamadaG23.Y7NCx
public import CFSG.LocalAnalysis.OddStandard.HigherRank.YamadaG23.Y7NAs1

public section

namespace CFSG.OddStandard.HigherRank.YamadaG23

open Subgroup CFSG.Open CFSG.OddStandard.HigherRank.G2Three
  CFSG.OddStandard.HigherRank.G2Three.Sec1

variable {G : Type} [Group G] [Finite G] {L : Subgroup G}

theorem y7n_ntAbs_of_setting (hB : Sec3Inputs) (h29 : Aut29Idx) (hS : HRSetting G L)
    (hL : HRG23 (L ⧸ center L)) (c : Ctx7 G L) (h5 : c.toCtx5.Facts5) (h7 : c.Upto79)
    (hRT : c.s.R ≠ c.s.T) {L1 P1 : Subgroup G} (hL1 : IsCompPre c.s L1)
    (hsyl : IsSylowIn 2 (normalizer (K7 c.s : Set G)) P1)
    (hle : P7 c.e ⊔ (closure {c.g, c.s.t} : Subgroup G) ≤ P1) :
    NtAbs c.s.t c.g ⁅L1, L1⁆ (P7 c.e) c.s.fr.S (U7 c L1) P1 := by
  have hH : F33Hyp c.s c.e := f33hyp_of hB hS hL c.s c.e
  obtain ⟨hgT, _hgR, hgσ, hg2, -⟩ := c.g_spec hRT
  have hF : SgFacts c.s.fr.S c.s.fr.F c.g := sgFacts_of_setting hH hg2 hgσ
  obtain ⟨hwr, hcent⟩ := y7n_wr7_of_cfg h5 h7 hL1
  obtain ⟨⟨⟨⟨⟨⟨⟨⟨h71, h72⟩, _⟩, _⟩, h75⟩, h76⟩, _⟩, _⟩, h79⟩ := id h7
  obtain ⟨hext, hns, hcard, hLam⟩ := y7n_Lam_facts hH h79 hL1
  have hdir := (h79 L1 hL1).1
  have hgP1 : c.g ∈ P1 :=
    hle (Subgroup.mem_sup_right (Subgroup.subset_closure (by simp)))
  have htP1 : c.s.t ∈ P1 :=
    hle (Subgroup.mem_sup_right (Subgroup.subset_closure (by simp)))
  refine ⟨?_, hg2, ?_, hsyl.2.1, htP1, hgP1, le_sup_left.trans hle, hwr, hcent, ?_, h76.2.1,
    inf_le_left, hdir.2.2, hdir.2.1, hLam, ?_, ?_, ?_, ?_, ?_, ?_, hF.g_notin, hF.g_norm⟩
  · simpa [c.s.t_order] using pow_orderOf_eq_one c.s.t
  · exact (Subgroup.mem_centralizer_singleton_iff.mp (c.s.sylow_T.1 hgT)).symm
  · rw [y54_card_S hH]
    norm_num
  · intro hbot
    rw [hbot, Subgroup.card_bot] at hcard
    omega
  · exact fun x hx => y7n_perm_Lam hH h7 hL1 (hsyl.1 hx)
  · exact fun z hz hzL hzLt => y7n_cent_P1_K h7 hL1 hLam hsyl.2.1 hz hzL hzLt
  · exact fun Z hZ hN => y7n_aut_bound h29 hext hns hcard hLam hZ hN
  · exact y7n_g_norm_Lam hH h5 h7 hRT hL1
  · exact y7n_g_norm_P hRT h71 h72 h75

end CFSG.OddStandard.HigherRank.YamadaG23
