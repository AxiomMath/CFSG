module

public import CFSG.LocalAnalysis.OddStandard.HigherRank.YamadaG23.Y7NSc
public import CFSG.LocalAnalysis.OddStandard.HigherRank.YamadaG23.Y7NMo
public import CFSG.LocalAnalysis.OddStandard.HigherRank.YamadaG23.Y7NC2b
public import CFSG.LocalAnalysis.OddStandard.HigherRank.YamadaG23.Y7NC1d
public import CFSG.LocalAnalysis.OddStandard.HigherRank.YamadaG23.Y7NCx
public import CFSG.LocalAnalysis.OddStandard.HigherRank.YamadaG23.Y7NGn

public section

namespace CFSG.OddStandard.HigherRank.YamadaG23

open Subgroup CFSG.Open CFSG.OddStandard.HigherRank.G2Three
  CFSG.OddStandard.HigherRank.G2Three.Sec1

variable {G : Type} [Group G] [Finite G] {L : Subgroup G}

theorem y7n_ntTwo_of_setting (hB : Sec3Inputs) (hS : HRSetting G L)
    (hL : HRG23 (L ⧸ center L)) (c : Ctx7 G L) (h5 : c.toCtx5.Facts5) (h7 : c.Upto79)
    (hRT : c.s.R ≠ c.s.T) {L1 : Subgroup G} (hL1 : IsCompPre c.s L1) :
    NtTwo c.s.t c.g (P7 c.e) (U7 c L1) c.s.fr.S c.s.fr.F (M3 c.s) := by
  have hH : F33Hyp c.s c.e := f33hyp_of hB hS hL c.s c.e
  obtain ⟨hgT, _hgR, hgσ, hg2, -⟩ := c.g_spec hRT
  obtain ⟨hwr, hcent⟩ := y7n_wr7_of_cfg h5 h7 hL1
  have hgLam := y7n_g_norm_Lam hH h5 h7 hRT hL1
  obtain ⟨⟨⟨⟨⟨⟨⟨⟨h71, h72⟩, _⟩, _⟩, h75⟩, _⟩, _⟩, _⟩, _⟩ := id h7
  refine ⟨hwr, hcent, sgFacts_of_setting hH hg2 hgσ, sgMore_of_setting hH hg2 hgσ, ?_, ?_,
    y7n_card_M3 c.toCtx5 hH, y7n_comm_P_M3 hH hRT h7 hL1⟩
  · exact (Subgroup.mem_centralizer_singleton_iff.mp (c.s.sylow_T.1 hgT)).symm
  · intro u hu
    refine ⟨?_, y7n_g_norm_P hRT h71 h72 h75 u hu.2⟩
    have hmem : c.g * u * c.g⁻¹ ∈ conjSub c.g ⁅L1, L1⁆ :=
      (mem_conjSub_iff' c.g ⁅L1, L1⁆ _).mpr ⟨u, hu.1, rfl⟩
    rwa [hgLam] at hmem

theorem y7n_char_M3 (hB : Sec3Inputs) (hS : HRSetting G L) (hL : HRG23 (L ⧸ center L))
    (c : Ctx7 G L) (h5 : c.toCtx5.Facts5) (h7 : c.Upto79) (hRT : c.s.R ≠ c.s.T)
    {L1 P1 P0 : Subgroup G} (hcfg : NTCfg c L1 P1 P0) {n : G} (hn : conjSub n P1 = P1) :
    conjSub n (M3 c.s) = M3 c.s := by
  have hH : F33Hyp c.s c.e := f33hyp_of hB hS hL c.s c.e
  have hT := y7n_ntTwo_of_setting hB hS hL c h5 h7 hRT hcfg.comp
  have hMn : P1 ≤ normalizer (M3 c.s : Set G) := by
    intro x hx
    have hx' := y7n_conj_M3 hH h7 hcfg.comp (hcfg.syl.1 hx)
    exact Subgroup.mem_normalizer_iff_map_conj_eq.mpr (by simpa [conjSub] using hx')
  rcases hcfg.cases with hcase1 | hcase2
  · obtain ⟨g0, _, hg0sq, hg0U, hU0eq, hg0g0t, hdir, hiso⟩ := hcase1
    exact y7n_char_case1 hT ⟨hg0sq, hg0U, hU0eq, hg0g0t, hdir, hiso⟩ hcfg.split hMn hn
  · obtain ⟨_, hP0⟩ := hcase2
    exact y7n_char_case2 hT (by rw [hcfg.split, hP0]) hMn hn

end CFSG.OddStandard.HigherRank.YamadaG23
