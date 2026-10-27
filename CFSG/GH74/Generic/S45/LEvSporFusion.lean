module

public import CFSG.GH74.Generic.S45.LEvSporCfg
public import CFSG.GH74.Generic.S45.LEvSporEmbed
public import CFSG.GH74.Generic.S45.LEvSporFacts

public section

open Subgroup CFSG CFSG.ABGLocalTools CFSG.Sporadic.Schreier CFSG.Sporadic.SmallOddCore
  CFSG.ComponentClassification.M12Cover
open CFSG.GH74.Generic.S45 CFSG.GH74.Generic.S45.EvSpor

namespace CFSG.GH74.GLS

theorem b_spor_fusion_proved :
    B_spor_fusion := by
  intro G _ _ N H K Q x y cfg hyN hy2 hynot hemb
  obtain ⟨E, hcfg⟩ := cfg.cfgData
  rcases cfg.sporadic with hM | hJ
  ·
    obtain ⟨e⟩ := hM
    have eD : ↥H ≃* ↥blockGroup := e.trans m12EquivD
    have hcardNR : Nat.card ↥N = Nat.card ↥autModel := by
      rw [cfg.index_two, Nat.card_congr eD.toEquiv, card_autModel_eq]
    obtain ⟨ψ, hψ⟩ := exists_corr_equiv m12_smallAutModel cfg.socle.le cfg.socle.normal
      cfg.socle.centralizer_trivial hcardNR eD
    obtain ⟨K', Q', E', x', hC', -, hQ', -, hxN, hx'⟩ := CfgData.of_corr ψ hψ hcfg
    subst hx'
    obtain ⟨e'⟩ := hC'.K5
    obtain ⟨hynot', hdvd'⟩ := fusion_transport ψ hxN hyN hynot hemb
    obtain ⟨n', hn'W, hn'Q⟩ := leaf3_of_m12Facts m12_autFacts hC'.hHN hC'.hnorm hC'.hKH e'
      hC'.hQC hC'.hQs hC'.hxQ hC'.hx2 hC'.hKx (ψ ⟨y, hyN⟩).2
      ((orderOf_corr ψ ⟨y, hyN⟩).trans hy2) hynot' hdvd'
    exact Corr.pull_conj ψ hQ' hyN hn'W hn'Q
  ·
    obtain ⟨e⟩ := hJ
    have eP : ↥H ≃* ↥j2P := e.trans j2PermEquiv
    have hcardNR : Nat.card ↥N = Nat.card ↥j2R := by
      obtain ⟨-, -, -, -, -, -, -, -, hRcard, -⟩ := ctuc_j2_normalizing_involution_permutation_model
      rw [cfg.index_two, Nat.card_congr eP.toEquiv, card_j2P, hRcard]
    obtain ⟨ψ, hψ⟩ := exists_corr_equiv j2_autModel cfg.socle.le cfg.socle.normal
      cfg.socle.centralizer_trivial hcardNR eP
    obtain ⟨K', Q', E', x', hC', -, -, -, hxN, hx'⟩ := CfgData.of_corr ψ hψ hcfg
    subst hx'
    obtain ⟨e'⟩ := hC'.K5
    obtain ⟨hynot', hdvd'⟩ := fusion_transport ψ hxN hyN hynot hemb
    exact (leaf3_of_j2Facts j2_autFacts hC'.hHN hC'.hnorm hC'.hcard hC'.hKH e' hC'.hQC hC'.hxQ
      hC'.hx2 hC'.hKx hC'.hEQ hC'.hEa hC'.hE4 (ψ ⟨y, hyN⟩).2
      ((orderOf_corr ψ ⟨y, hyN⟩).trans hy2) hynot' hdvd').elim

end CFSG.GH74.GLS
