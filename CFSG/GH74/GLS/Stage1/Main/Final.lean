module

public import CFSG.GH74.GLS.Stage1.Main.Build
public import CFSG.GH74.GLS.Stage1.Main.Closed
public import CFSG.GH74.GLS.Stage1.Main.Outcome
public import CFSG.GH74.GLS.Stage1.Main.Std9
public import CFSG.GH74.GLS.Stage1.Main.Assembly
public import CFSG.GH74.GLS.Bg.Rank

public section

namespace CFSG.GH74.GLS.Stage1.Main

open Subgroup CFSG CFSG.GH74 CFSG.GH74.GLS CFSG.Blueprint CFSG.Assembly.LowTwoRank
  CFSG.GH74.GLS.Stage12 CFSG.GH74.GLS.Stage2.Local CFSG.GH74.GLS.Stage1.Thm3.Sec5
  CFSG.GH74.GLS.Stage1.Thm3.Sec6 CFSG.GH74.GLS.Stage1.Thm3.Sec7 CFSG.GH74.GLS.Stage1.Thm3.Sec8
  CFSG.GH74.GLS.Stage1.Thm4

theorem stage1_out_four (hthm2 : S_stage1_thm2_Std) (h61 : Prop6_1) (h71 : Prop7_1) (h81 : Prop8_1)
    (h92 : Prop9_2) (h93 : Prop9_3) (hB2 : B2Split) (hG4 : Gen4NoL34)
    (hRG : RankG2)
    (hbase : BaseBridge) (hpair7 : PairBridge7) (hpsp : PSp4Extra) (hl4nf : L4NFExtra) (hl4fld : L4NFField)
    (hpairF : PairBridgeF) (hl4f : L4FExtra) (hdet : NoFAutBridge) (hdet1 : NoFAutBridgeR1) (hspor : SporadicNoRank1) :
    Stage1OutFour := by
  intro G _ _ hStd h4 hT
  obtain ⟨x, K, hxK, hB⟩ := hT
  by_cases hrk : pRank 2 ↥K = 1
  · obtain ⟨z, S, hcen, hzc, hc6, hr, hterm⟩ :=
      thm3_outcome hthm2 h61 h71 h81 hStd ⟨x, K, hxK, hrk⟩
    have hrank : pRank 2 ↥S = 4 := hcen.pRank_eq.trans h4
    rcases hterm with hg | ⟨q, w, hT7⟩ | ⟨ε, hL⟩
    · have := hRG G z S hg
      omega
    · by_cases hw : w = 1
      · subst hw
        exact ⟨z, S, Kind.psp4, Or.inl rfl, hcen.central, hcen.sylow,
          out_psp4 hbase hpair7 hpsp hdet hdet1 hcen hzc hr hc6 hT7⟩
      · obtain ⟨ε, hout⟩ := out_l4NF hbase hpair7 hl4nf hl4fld hdet hdet1 hcen hzc hr hc6 hT7 hw
        exact ⟨z, S, Kind.l4 ε, Or.inr (Or.inl ⟨ε, rfl⟩), hcen.central, hcen.sylow, hout⟩
    · exact ⟨z, S, Kind.l4 ε, Or.inr (Or.inl ⟨ε, rfl⟩), hcen.central, hcen.sylow,
        out_l4F hbase hpairF hl4f hdet hdet1 hcen hzc hr hc6 hL⟩
  · rcases hB2 G K hB hrk with ⟨n, hn8, hn11, hcov, hr4⟩ | ⟨hqs, hl34, hex⟩
    · have hH : Hyp9 G (HatT K) := ⟨hStd, ⟨n, hn8, hn11, hcov⟩, ⟨x, K, hxK, ⟨MulEquiv.refl _⟩⟩⟩
      obtain ⟨z, t, S, K', hstd9⟩ := exists_std9 h92 hH
      obtain ⟨-, n', hn8', hn11', hsp, hcz⟩ := h93 G (HatT K) z t S K' hstd9
      have hcen : Cen2 G z S := ⟨hStd, hcz, hstd9.sylow⟩
      obtain ⟨-, hm, hl⟩ := out_sporadic hspor hcen hn8' hn11' hsp
      by_cases h9 : n' ≤ 9
      · exact ⟨z, S, Kind.mcl, Or.inr (Or.inr (Or.inl rfl)), hcz, hstd9.sylow, hm h9⟩
      · exact ⟨z, S, Kind.ly, Or.inr (Or.inr (Or.inr rfl)), hcz, hstd9.sylow, hl (by omega)⟩
    · exact absurd ⟨hqs, hl34, hex⟩ (hG4 G hStd.gen4 K)

theorem stage1_out_three_r3 (hthm2 : S_stage1_thm2_Std) (h61 : Prop6_1) (h71 : Prop7_1)
    (h81r : Prop8_1Rank3) (hB2 : B2Split) (hG4 : Gen4NoL34) (hR7 : RankTerm7)
    (hbase : BaseBridge) (hG2 : G2ShapeBridge) (hdet : NoFAutBridge) (hdet1 : NoFAutBridgeR1) :
    Stage1OutThree := by
  intro G _ _ hStd h3 hT
  obtain ⟨x, K, hxK, hB⟩ := hT
  by_cases hrk : pRank 2 ↥K = 1
  · obtain ⟨z, S, hcen, hzc, hc6, hr, hterm⟩ :=
      thm3_outcome_three hthm2 h61 h71 h81r hStd h3 ⟨x, K, hxK, hrk⟩
    have hrank : pRank 2 ↥S = 3 := hcen.pRank_eq.trans h3
    rcases hterm with hg | ⟨q, w, hT7⟩
    · exact ⟨z, S, hcen.central, hcen.sylow, out_g2 hbase hG2 hdet hdet1 hcen hzc hr hc6 hg h3⟩
    · have := hR7 G z S q w hT7
      omega
  · rcases hB2 G K hB hrk with ⟨n, hn8, hn11, hcov, hr4⟩ | ⟨hqs, hl34, hex⟩
    · have := Bg.pRank_subgroup_le (p := 2) (by norm_num) K
      omega
    · exact absurd ⟨hqs, hl34, hex⟩ (hG4 G hStd.gen4 K)

end CFSG.GH74.GLS.Stage1.Main
