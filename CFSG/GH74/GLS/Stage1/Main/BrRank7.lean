module

public import CFSG.GH74.GLS.Stage1.Main.Closed
public import CFSG.GH74.GLS.Stage1.Main.BrModel
public import CFSG.GH74.GLS.Stage1.Main.BrRankE16
public import CFSG.LocalAnalysis.SectionRank.Framework.SylowRank
public import CFSG.LieType.SteinbergBRTwoRankBound

public section

namespace CFSG.GH74.GLS.Stage1.Main

open Subgroup CFSG CFSG.GH74 CFSG.GH74.GLS CFSG.Blueprint CFSG.Assembly.LowTwoRank
  CFSG.GH74.GLS.Stage12 CFSG.GH74.GLS.Stage2.Local CFSG.GH74.GLS.Stage1.Thm3.Sec4
  CFSG.GH74.GLS.Stage1.Thm3.Sec5 CFSG.GH74.GLS.Stage1.Thm3.Sec6 CFSG.GH74.GLS.Stage1.Thm3.Sec7
  CFSG.GH74.GLS.Stage1.Thm3.Sec8 CFSG.GH74.GLS.Stage1.Thm2.Recip CFSG.GH74.GLS.Stage1.Thm6.Prod
  CFSG.GH74.GLS.Stage2.Final
open scoped commutatorElement

theorem rankTerm7_thm : RankTerm7 := by
  intro G _ _ z S q w hT
  obtain ⟨K₁, K₂, hs, hodd, h5, hK₁, hK₂, hT7⟩ := hT
  obtain ⟨Gs, iGs, fGs, z', t', w', S', E₁, E₂, hz'o, hcen, hz'S', hz'c, hC, hD, hww⟩ :=
    exists_term7_model hodd h5 hK₁ hT7
  have hz'sq : z' * z' = 1 := by
    have := pow_orderOf_eq_one z'
    rwa [hz'o, pow_two] at this
  have hz'1 : z' ≠ 1 := by
    intro h
    rw [h, orderOf_one] at hz'o
    omega
  have ht'sq : t' * t' = 1 := by
    have := pow_orderOf_eq_one t'
    rwa [hD.t_ord, pow_two] at this
  have hz'E : z' ∈ E₁ ∧ z' ∈ E₂ := by
    have : z' ∈ E₁ ⊓ E₂ := by rw [hD.inter_E]; exact mem_zpowers z'
    exact this
  have htE : t' ∉ E₁ ⊔ E₂ := by
    intro h
    have h1 : t' ∈ IVK.Ez z' ⊓ (zpowers t' ⊔ zpowers w') :=
      ⟨by rw [hD.Ez_eq]; exact h, Subgroup.mem_sup_left (mem_zpowers t')⟩
    rw [hD.inter, Subgroup.mem_bot] at h1
    have := hD.t_ord
    rw [h1, orderOf_one] at this
    omega
  obtain ⟨a, ha, b, hb, haa, hbb, hba⟩ :=
    exists_quat_pair hodd hD.sl2 hz'E.1 hz'sq hz'1 (fun x hx => hD.comm_E x hx z' hz'E.2)
  obtain ⟨E, hE, hEcard⟩ := exists_E16 hz'sq hz'1 ht'sq (hz'c t' hD.t_mem) hD.E₂_eq hD.inter_E
    hD.comm_E htE ha hb haa hbb hba
  have h16 : 4 ≤ CFSG.pRank 2 Gs :=
    CFSG.LieType.SteinbergBR.le_pRank_of_card Nat.one_lt_two E hE hEcard
  have h1 : CFSG.pRank 2 ↥(S' : Subgroup Gs) = CFSG.pRank 2 Gs :=
    (CFSG.SectionRank.pRank_sylow S').2
  have hSp : IsPGroup 2 ↥S := hs.sylow.isPGroup
  obtain ⟨e⟩ := exists_equiv_of_compat (le_sup_right : S ≤ K₁ ⊔ K₂ ⊔ S)
    (fun s hs' hz => eq_one_of_mem_pgroup_oddCore hSp hs' hz) hC
  have h2 : CFSG.pRank 2 ↥S = CFSG.pRank 2 ↥(S' : Subgroup Gs) := by
    rw [CFSG.SectionRank.pRank_eq_open_pRank_top, CFSG.SectionRank.pRank_eq_open_pRank_top]
    exact CFSG.SectionRank.pRank_top_eq_of_mulEquiv Nat.one_lt_two e
  omega

end CFSG.GH74.GLS.Stage1.Main
