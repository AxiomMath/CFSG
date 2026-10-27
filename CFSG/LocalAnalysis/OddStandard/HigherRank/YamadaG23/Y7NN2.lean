module

public import CFSG.LocalAnalysis.OddStandard.HigherRank.YamadaG23.Y7NSd
public import CFSG.LocalAnalysis.OddStandard.HigherRank.YamadaG23.Y7NXc
public import CFSG.LocalAnalysis.OddStandard.HigherRank.YamadaG23.Y7NN1
public import CFSG.LocalAnalysis.OddStandard.HigherRank.YamadaG23.Y7NN3

public section

namespace CFSG.OddStandard.HigherRank.YamadaG23

open Subgroup CFSG.Open CFSG.OddStandard.HigherRank.G2Three
  CFSG.OddStandard.HigherRank.G2Three.Sec1

theorem sec7nt2_of (hB : Sec3Inputs) : Sec7NT2 := by
  intro G _ _ L hS hL c h5 h7 hRT L1 P1 P0 hcfg
  refine y7n_isSylowIn_top_of_normalizer_le hcfg.syl fun n hn => ?_
  have hconj : conjSub n P1 = P1 :=
    Subgroup.mem_normalizer_iff_map_conj_eq.mp hn
  have hM : conjSub n (M3 c.s) = M3 c.s := y7n_char_M3 hB hS hL c h5 h7 hRT hcfg hconj
  exact y7n_N_M3_le_N_K c.s (Subgroup.mem_normalizer_iff_map_conj_eq.mpr hM)

theorem sec7NT_holds (hB : Sec3Inputs) (h29 : Aut29Idx) : Sec7NT :=
  sec7NT_of (sec7nt1_of hB h29) (sec7nt2_of hB) (sec7nt3_of hB)

end CFSG.OddStandard.HigherRank.YamadaG23
