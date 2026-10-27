module

public import CFSG.LocalAnalysis.RankFourTheoremC.PEmpty.L6LeavesKxEmb
public import CFSG.LocalAnalysis.RankFourTheoremC.PEmpty.L6LeavesKxCount
public import CFSG.LocalAnalysis.RankFourTheoremC.PEmpty.L6LeavesKxDefs

public section

namespace CFSG.LocalAnalysis.RankFourTheoremC.PEmpty

open CFSG CFSG.Open Subgroup

variable {G : Type} [Group G] [Finite G]

namespace KxCfg

variable {p : ℕ} {P : Sylow p G} {M : Subgroup G} {x z : G} {T S L : Subgroup G}

theorem false_of_j1 (hE : KFactJ1Sylow) (h27 : KFactJ1L27) (c : KxCfg p P M x z T S L)
    (h : Nonempty (↥L ≃* (TauCeti.CFSGIndex.sporadic .J1).Group)) : False := by
  have hp := c.conf.config.prime
  haveI : Fact p.Prime := ⟨hp⟩
  haveI : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hp5 : 5 ≤ p := c.conf.config.situation.p_ge
  set R : Subgroup G := ⁅zpowers z, S⁆ with hR
  have hzR : z ∈ normalizer (R : Set G) := c.conf.z_le_normalizer_R (mem_zpowers z)
  have hRM : R ≤ M := c.conf.R_le_S.trans c.conf.S_le_M
  obtain ⟨E, hEsyl, hRE⟩ := exists_isSylowOf_ge (f := 2) c.commutator_le c.conf.R_isPGroup
  obtain ⟨-, hEcard⟩ := hE G L E c.isSimple h hEsyl
  have hRcard : Nat.card R ∣ 8 := hEcard ▸ Subgroup.card_dvd_of_le hRE
  obtain ⟨hp7, hR8⟩ := eq_seven_of_not_centralizes hp5 c.orderOf_z hzR hRcard c.exists_not_commute
  have hRE' : R = E := Subgroup.eq_of_le_of_card_ge hRE (by omega)
  have hz7 : orderOf z = 7 := hp7 ▸ c.orderOf_z
  have hzE : z ∈ normalizer (E : Set G) := hRE' ▸ hzR
  have hNR : normalizer (R : Set G) ⊓ L ≤ M ⊓ L := by
    refine inf_le_inf_right L (c.normalizer_le c.commutator_le c.conf.R_isPGroup hzR ?_)
    rw [inf_eq_left.mpr hRM]
    exact c.conf.R_ne_bot
  have hLJ : L ≤ M ⊓ L := h27 G L E z h hEsyl c.z_mem hz7 hzE (M ⊓ L)
    (le_inf c.normalizer_zpowers_le inf_le_right) (hRE' ▸ hNR)
  exact c.not_le (hLJ.trans inf_le_left)

end KxCfg

end CFSG.LocalAnalysis.RankFourTheoremC.PEmpty
