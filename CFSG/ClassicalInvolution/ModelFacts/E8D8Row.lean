module

public import CFSG.ClassicalInvolution.ModelFacts.E8D8RowFund12
public import CFSG.ClassicalInvolution.ModelFacts.E8D8RowOrth
public import CFSG.ClassicalInvolution.ModelFacts.E8D8RowShape
public import CFSG.ClassicalInvolution.RouteD.TypeTwistedE6PerpExc
public import CFSG.ClassicalInvolution.RouteD.ExoticTwinProofExcLayerTwisted
public import CFSG.ClassicalInvolution.RouteD.TypeDLocal
public import Certificates.Certificate45
public import Certificates.Certificate46
public import Certificates.Certificate47
public import Certificates.Certificate48
public import Certificates.Certificate49
public import Certificates.Certificate50
public import Certificates.Certificate51
public import Certificates.Certificate52
public import Certificates.Certificate53
public import Certificates.Certificate54
public import Certificates.Certificate55
public import Certificates.Certificate56
public import Certificates.Certificate57
public import Certificates.Certificate58
public import Certificates.Certificate59
public import Certificates.Certificate60
public import Certificates.Certificate61
public import Certificates.Certificate62
public import Certificates.Certificate63
public import Certificates.Certificate64
public import Certificates.Certificate65
public import Certificates.Certificate66
public import Certificates.Certificate67
public import Certificates.Certificate68
public import Certificates.Certificate69
public import Certificates.Certificate70
public import Certificates.Certificate71
public import Certificates.Certificate72
public import Certificates.Certificate73
public import Certificates.Certificate74
public import Certificates.Certificate75
public import Certificates.Certificate76
public import Certificates.Certificate77
public import Certificates.Certificate78
public import Certificates.Certificate79
public import Certificates.Certificate80
public import Certificates.Certificate81
public import Certificates.Certificate113
public import Certificates.Certificate114
public import Certificates.Certificate115
public import Certificates.Certificate116
public import Certificates.Certificate117
public import Certificates.Certificate118
public import Certificates.Certificate119
public import Certificates.Certificate120
public import Certificates.Certificate121
public import Certificates.Certificate122
public import Certificates.Certificate123
public import Certificates.Certificate3951
public import Certificates.Certificate3952
public import CFSG.ClassicalInvolution.ModelFacts.ClassicalIsFundamentalE6
public import CFSG.ClassicalInvolution.ModelFacts.ClassicalIsFundamentalE7
public import CFSG.ClassicalInvolution.ModelFacts.ClassicalIsFundamentalTwistedE6
public import CFSG.LocalAnalysis.ComponentClassification.BadTwoComponentSubgroup

public section

namespace CFSG.ClassicalInvolution.RouteD.TypeE8

open CFSG.ClassicalInvolution.Generic CFSG.ClassicalInvolution.RouteD.Exotic
  CFSG.ClassicalInvolution.RouteD.NonClassical CFSG.Assembly.LowTwoRank

variable (p f : ℕ) [Fact p.Prime]

theorem e8D8Row' : E8D8Row' p f := by
  intro hp2 hq t n e he hfund hG2 hD4 hadm R₀ hR₀ k hkR hkc φ hφ h0
  subst he
  have hk : R₀ ≤ Subgroup.centralizer ({k} : Set _) := fun r hr =>
    Subgroup.mem_centralizer_iff.mpr fun h hh => by
      rw [Set.mem_singleton_iff] at hh
      subst hh
      exact (hkc r hr).symm
  have h0' : φ ⟨R₀, hR₀, hk⟩ = none := h0 _ rfl
  have hfund' : ModelFacts.IsFundTag t := by
    cases t <;> trivial
  have hfin : Finite (modelUniv t n p e Fact.out).K :=
    ModelFacts.finite_modelUniv hp2 Fact.out hfund' hadm
  have hne : Nonempty (Fund12 p e) := by
    obtain ⟨R, hR⟩ := nonempty_fund_plus (p := p) (f := e) (m := 6) (by norm_num)
    exact ⟨⟨R, hR⟩⟩
  have hcount := card_commuting_of_d8Layer p e hR₀ hkR hk φ hφ h0'
  have hm := card_fund12_mul p e hp2 hq
  have hnc : NoTE6Config (fundamentalSubgroups t (modelUniv t n p e Fact.out).D) → False :=
    fun hN => by
      obtain ⟨R₁, hP, hT⟩ := exists_partner_of_d8Layer p e hne hR₀ hkR hk φ hφ h0'
      exact hN R₀ hR₀ R₁ hP hT
  cases t with
  | PSL => exact (hnc (noTE6Config_psl_model hp2 hadm)).elim
  | PSU => exact (hnc (noTE6Config_psu_model hp2 hadm)).elim
  | PSp => exact (hnc (noTE6Config_psp_model hp2 hadm)).elim
  | POmegaOdd => exact (ModelFacts.E8D8.d8_false_odd hp2 hq hadm hR₀ hcount hm).elim
  | POmegaPlus => exact ⟨rfl, ModelFacts.E8D8.d8_eq_plus hp2 hq hadm hR₀ hcount hm⟩
  | POmegaMinus => exact (ModelFacts.E8D8.d8_false_minus hp2 hq hadm hR₀ hcount hm).elim
  | G2 => exact absurd rfl hG2
  | F4 =>
    exact (hnc (noTE6Config_of_hasQuasisimpleLayer hp2 (by omega) hfund hadm
      (excLayer hp2 hq .F4 n (Or.inl rfl) hadm))).elim
  | E6 =>
    exact (hnc (noTE6Config_of_hasQuasisimpleLayer hp2 (by omega) hfund hadm
      (excLayer hp2 hq .E6 n (Or.inr (Or.inl rfl)) hadm))).elim
  | E7 =>
    exact (hnc (noTE6Config_of_hasQuasisimpleLayer hp2 (by omega) hfund hadm
      (excLayer hp2 hq .E7 n (Or.inr (Or.inr (Or.inl rfl))) hadm))).elim
  | E8 =>
    exact (hnc (noTE6Config_of_hasQuasisimpleLayer hp2 (by omega) hfund hadm
      (excLayer hp2 hq .E8 n (Or.inr (Or.inr (Or.inr (Or.inl rfl)))) hadm))).elim
  | twistedE6 =>
    exact (hnc (noTE6Config_of_hasQuasisimpleLayer hp2 (by omega) hfund hadm
      (excLayer hp2 hq .twistedE6 n (Or.inr (Or.inr (Or.inr (Or.inr rfl)))) hadm))).elim
  | trialityD4 => exact absurd rfl hD4
  | twistedB2 => exact hfund.elim
  | twistedG2 => exact hfund.elim
  | twistedF4 => exact hfund.elim
  | Tits => exact hfund.elim

end CFSG.ClassicalInvolution.RouteD.TypeE8
