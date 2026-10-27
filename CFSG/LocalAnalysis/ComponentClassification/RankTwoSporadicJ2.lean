module

public import CFSG.LocalAnalysis.ComponentClassification.RankTwoSporadicJ2W
public import CFSG.LocalAnalysis.ComponentClassification.RankTwoSporadicJ2Data
public import CFSG.LocalAnalysis.ComponentClassification.J2CoverAut
public import CFSG.LocalAnalysis.ComponentClassification.RankTwoSporadicPairCensus
public import CFSG.LocalAnalysis.ComponentClassification.RankTwoSporadicPairCensusW

public section

namespace CFSG.ComponentClassification.RankTwoSporadic.J2

open Subgroup CFSG.Open CFSG.ComponentClassification.RankTwoSporadic CFSG.ABGLocalTools
open CFSG.ComponentClassification.AschbacherTightEmbedding
open CFSG.ComponentClassification.RankTwoSporadic.Cert CFSG.ComponentClassification.J2Cover
open CFSG.Monster.B.Co2 CFSG.Monster.B.Co2.Native CFSG.RankThree.Native

theorem j2InP_iff (a : Array ℕ) (g : Equiv.Perm (Fin 315))
    (h : Rep 315 a g) :
    j2InP a = true ↔ g ∈ P :=
  mem_P_iff h

theorem j2_normal : (P.subgroupOf R).Normal :=
  (normal_subgroupOf_iff_le_normalizer P_le_R).2 R_le_normalizer

theorem j2AutModel :
    AutModel (Blueprint.NativeSporadic.Carrier .J2) ↥R (P.subgroupOf R) :=
  autModel_of_conj P_le_R nativeEquivP.symm (MulEquiv.ofBijective rConj rConj_bijective)
    fun x p => rConj_apply x p

@[expose] noncomputable def j2E0Sub : Subgroup (Equiv.Perm (Fin 315)) :=
  closure (permsA 315 j2E0)

theorem j2_yCensusII {sG roots : Array ℕ}
    {nodes : Array CFSG.KC.Census.NodeP} {cS : CFSG.KC.Census.ArrCertP}
    {wcs : Array (Array CFSG.KC.Census.ArrCertP)} (h : j2CheckWII sG roots nodes cS wcs = true) :
    YCensus (P.subgroupOf R) (· ≤ P.subgroupOf R) := by
  simp only [j2CheckWII, Bool.and_eq_true, beq_iff_eq] at h
  obtain ⟨⟨hc, hgen⟩, hsize⟩ := h
  exact yCensusII_pair_of_checkW (k := 8) (m := 4725) P_le_R j2_normal j2PS_lt j2InP_iff rep_permU
    permU_mem_R hc hgen hsize (by rw [card_R]; norm_num) (by decide)

theorem j2_yCensusExc {sG roots : Array ℕ}
    {nodes : Array CFSG.KC.Census.NodeP} {cS : CFSG.KC.Census.ArrCertP}
    {wcs : Array (Array CFSG.KC.Census.ArrCertP)} {excs : List CFSG.KC.Census.ExcRefP}
    (h : j2CheckWExc j2E0 sG roots nodes cS wcs excs = true) :
    YCensus (P.subgroupOf R) (ExcClass R j2E0Sub) := by
  simp only [j2CheckWExc, Bool.and_eq_true, beq_iff_eq] at h
  obtain ⟨⟨hc, hgen⟩, hsize⟩ := h
  exact yCensusExc_pair_of_checkW (k := 8) (m := 4725) P_le_R j2_normal j2PS_lt j2InP_iff
    rep_permU permU_mem_R hc hgen hsize (by rw [card_R]; norm_num) (by decide)

end CFSG.ComponentClassification.RankTwoSporadic.J2
