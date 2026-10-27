module

public import CFSG.GH74.Generic.S45.LEvSporCfg
public import CFSG.GH74.Generic.S45.LEvSporEmbed
public import CFSG.GH74.Generic.S45.LEvSporFacts

public section

open Subgroup CFSG CFSG.ABGLocalTools CFSG.Sporadic.Schreier CFSG.Sporadic.SmallOddCore
  CFSG.ComponentClassification.M12Cover
open CFSG.GH74.Generic.S45 CFSG.GH74.Generic.S45.EvSpor

namespace CFSG.GH74.GLS

theorem b_spor_outer_invol_proved :
    B_spor_outer_invol := by
  intro G _ _ N H K Q x cfg
  obtain ⟨E, hcfg⟩ := cfg.cfgData
  rcases cfg.sporadic with hM | hJ
  ·
    obtain ⟨e⟩ := hM
    have eD : ↥H ≃* ↥blockGroup := e.trans m12EquivD
    have hcardNR : Nat.card ↥N = Nat.card ↥autModel := by
      rw [cfg.index_two, Nat.card_congr eD.toEquiv, card_autModel_eq]
    obtain ⟨ψ, hψ⟩ := exists_corr_equiv m12_smallAutModel cfg.socle.le cfg.socle.normal
      cfg.socle.centralizer_trivial hcardNR eD
    obtain ⟨K', Q', E', x', hC', -, -, -, hxN, hx'⟩ := CfgData.of_corr ψ hψ hcfg
    obtain ⟨e'⟩ := hC'.K5
    obtain ⟨u', hu'N, hu'H, hu'2, hu'x⟩ := leaf2_of_m12Facts m12_autFacts hC'.hHN
      hC'.hnorm hC'.hKH e' (hC'.hQC hC'.hxQ).2 hC'.hx2 hC'.hKx
    exact Corr.pull_outer ψ hψ hxN hu'N hu'H hu'2 (by rw [hx']; exact hu'x)
  ·
    obtain ⟨e⟩ := hJ
    have eP : ↥H ≃* ↥j2P := e.trans j2PermEquiv
    have hcardNR : Nat.card ↥N = Nat.card ↥j2R := by
      obtain ⟨-, -, -, -, -, -, -, -, hRcard, -⟩ := ctuc_j2_normalizing_involution_permutation_model
      rw [cfg.index_two, Nat.card_congr eP.toEquiv, card_j2P, hRcard]
    obtain ⟨ψ, hψ⟩ := exists_corr_equiv j2_autModel cfg.socle.le cfg.socle.normal
      cfg.socle.centralizer_trivial hcardNR eP
    obtain ⟨K', Q', E', x', hC', -, -, -, hxN, hx'⟩ := CfgData.of_corr ψ hψ hcfg
    obtain ⟨u', hu'N, hu'H, hu'2, hu'x⟩ := leaf2_of_j2Facts j2_autFacts hC'.hnorm
      (hC'.hQC hC'.hxQ).2 hC'.hx2
    exact Corr.pull_outer ψ hψ hxN hu'N hu'H hu'2 (by rw [hx']; exact hu'x)

end CFSG.GH74.GLS
