module

public import CFSG.LocalAnalysis.ComponentClassification.RankTwoHypIICoverU42
public import CFSG.LocalAnalysis.ComponentClassification.RankTwoSporadicPairCensusW
public import Certificates.Certificate15018

public section

namespace CFSG.ComponentClassification.RankTwoHypIICover.U42

open Subgroup CFSG.Open CFSG.ComponentClassification CFSG.ComponentClassification.RankTwoSporadic
open CFSG.ComponentClassification.RankTwoSporadic.Cert CFSG.RankThree.Native
open CFSG.Monster.B.Co2 CFSG.Monster.B.Co2.Native CFSG.Certificates CFSG.Certificates.Native
open CFSG.ComponentClassification.CatFactsSmall.PSp43 CFSG.KC.Census

theorem u42_check :
    ∃ (sG roots : Array ℕ) (nodes : Array NodeP) (cS : ArrCertP) (wcs : Array (Array ArrCertP)),
      u42CheckW sG roots nodes cS wcs = true :=
  Certificates.certificate15018

theorem rep_u42FP : Rep 45 (unpackP 45 6 u42FP) f45 := by
  have h : unpackP 45 6 u42FP = arr45 f45 := by decide +kernel
  rw [h]
  exact rep_arr45 f45

theorem u42_yCensusW {sG roots : Array ℕ} {nodes : Array NodeP}
    {cS : ArrCertP} {wcs : Array (Array ArrCertP)} (hc : u42CheckW sG roots nodes cS wcs = true) :
    YCensus (QP45.originalSubgroup.subgroupOf QA45.originalSubgroup)
      (· ≤ QP45.originalSubgroup.subgroupOf QA45.originalSubgroup) := by
  simp only [u42CheckW, Bool.and_eq_true, beq_iff_eq] at hc
  obtain ⟨⟨⟨hch, hc⟩, hgen⟩, hsize⟩ := hc
  exact yCensusII_pair_of_checkW (k := 7) (m := 405) QP45_le_QA45 u42AutModel.normal u42PS_lt
    (u42InX_iff hch) rep_u42FP f45_mem_QA45 hc hgen hsize (by rw [card_QA45]; norm_num)
    (by decide)

theorem hypII_of_psu_four_two
    {A : Type} [Group A] (hA : commutator A = ⊤)
    (h : CFSG.Assembly.LowTwoRank.StatedClassicalModel (A ⧸ center A) .PSU 4 2 1) :
    AS76b.HypII A := by
  obtain ⟨_, _, _, _, _, hc⟩ := u42_check
  obtain ⟨e⟩ := CFSG.Blueprint.EvenSource.nonempty_mulEquiv_of_statedClassicalModel
    (CFSG.GH74.Exceptional.statedClassicalModel_PSp_two_three_of_PSU_four_two h)
    statedClassicalModel_PSp43
  exact hypII_of_yCensus u42AutModel (u42_yCensusW hc) hA (e.trans psp43EquivP)

end CFSG.ComponentClassification.RankTwoHypIICover.U42
