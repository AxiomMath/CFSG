module

public import CFSG.LocalAnalysis.ComponentClassification.RankTwoL3FourHypII
public import CFSG.LocalAnalysis.ComponentClassification.RankTwoL3FourHypIICensusW
public import Certificates.Certificate15012

public section

namespace CFSG.ComponentClassification.RankTwoL3Four.HypII

open Subgroup CFSG.Open CFSG.ComponentClassification.RankTwoSporadic CFSG.ABGLocalTools
open CFSG.ComponentClassification.RankTwoSporadic.Cert CFSG.ComponentClassification.PSL3Four
open CFSG.RankThree.Native CFSG.Monster.B.Co2 CFSG.Monster.B.Co2.Native CFSG.Monster.B.Fischer
open CFSG.KC.Census

theorem l34_checkII :
    ∃ (prog : List (ℕ × ℕ)) (sG roots : Array ℕ) (nodes : Array NodeP) (cS : ArrCertP)
      (wcs : Array (Array ArrCertP)), l34CheckWII prog sG roots nodes cS wcs = true :=
  Certificates.certificate15012

theorem l34_yCensusIIW {prog : List (ℕ × ℕ)} {sG roots : Array ℕ}
    {nodes : Array NodeP} {cS : ArrCertP} {wcs : Array (Array ArrCertP)}
    (h : l34CheckWII prog sG roots nodes cS wcs = true) :
    YCensus (S.subgroupOf R) (· ≤ S.subgroupOf R) := by
  simp only [l34CheckWII, Bool.and_eq_true, beq_iff_eq] at h
  obtain ⟨⟨⟨⟨hch, hslp⟩, hc⟩, hgen⟩, hsize⟩ := h
  refine yCensusII_of_checkW_regs (k := 8) (m := 945) S_le_R S_normal l34PS_lt
    (fun a g ha => l34InSW_iff hch ha) (fun r hr => ?_) hc hgen hsize
    (by rw [card_R]; norm_num) (by decide)
  obtain ⟨g, hg, hrep⟩ := rep_slpRegs hslp r hr
  exact ⟨g, closure_permsA_l34GensR ▸ hg, hrep⟩

theorem hypII_L34 :
    AS81.L34HypII := by
  intro A _ _ hA hL
  obtain ⟨_, _, _, _, _, _, hc⟩ := l34_checkII
  obtain ⟨e⟩ := nonempty_equiv_of_stated (A ⧸ center A) hL
  exact hypII_of_yCensus l34AutModel (l34_yCensusIIW hc) hA e

end CFSG.ComponentClassification.RankTwoL3Four.HypII
