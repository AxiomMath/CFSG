module

public import CFSG.GH74.QTGen4.DCopy.Quasithin.H13.Stmt331F4
public import CFSG.GH74.QTGen4.DCopy.Quasithin.Vol2.Ch11StatementsInputs
public import CFSG.Quasithin.Vol2.Ch11SecOE1E

public section
namespace CFSG.Quasithin.Vol2.Ch11

open Subgroup CFSG.Quasithin CFSG.Quasithin.H13
open CFSG.Open (pCoreOf)

theorem tmpL6_3_2_2_six_of_F4 (hC58 : TheoremC58) (h317 : AS317Sylow) (h331 : Stmt3_3_1_F4)
    (h3228 : Ch10.TmpL6_3_2_2_eight) (h4 : TmpL6_3_2_2_four) : TmpL6_3_2_2_six_F4 := by
  intro G _ _ T L I hfsu hne hU
  obtain ⟨hVH, hVred, hOC⟩ := h3228 G T L I hfsu
  have hLc : L ∈ cComp (L ⊔ T) := cComp_of_isLocal hfsu.maximal.1
  have hperf : ⁅L, L⁆ = L := perfect_of_mem_cComp hLc
  have hT2 : IsPGroup 2 T := hfsu.sylow.1
  have hred : IsTwoReducedIn (fsuL0 T L ⊔ T) (fsuV T I) :=
    isTwoReducedIn_iff_isPrimeReduced_subgroupOf.2 ⟨hVH, hVred⟩
  have hyp : Hyp318 T (fsuM T L) (fsuL0 T L) (fsuV T I) :=
    { inM := ⟨hU.1.1, le_sup_right.trans hU.1.2⟩
      nonempty := ((h331 G T hfsu.simple hfsu.nonabelian hfsu.qtke hfsu.sylow).2 L
        hfsu.maximal hfsu.quasisimple).2.2.1
      perfect := eq_oTwoUpper_of_perfect (perfect_conjClosure hperf)
      le_M := le_normalizer
      normal := le_rfl
      unique := hU
      reduced := hred
      centralizer := hOC }
  rcases theorem318_three hC58 h317 hfsu.simple hfsu.nonabelian hfsu.qtke hfsu.sylow hyp with
    ⟨hJ, hFF⟩ | ⟨-, -, hZ⟩
  ·
    refine ⟨?_, ⟨hred.2.2.1.1, hFF⟩⟩
    have hL₀L : fsuL0 T L ≤ normalizer (L : Set G) := conjClosure_le fun t ht l hl =>
      LocDbl.le_normalizer_of_mem_cComp hLc
        (LocDbl.map_conj_mem_cComp hLc (le_normalizer (mem_sup_right ht))) ⟨l, hl, rfl⟩
    have hL₀n : ((fsuL0 T L).subgroupOf (fsuL0 T L ⊔ T)).Normal :=
      (Subgroup.normal_subgroupOf_iff_le_normalizer le_sup_left).mpr
        (sup_le le_normalizer (le_normalizer_conjClosure L T))
    have hOT : pCoreOf 2 (fsuL0 T L) ≤ T :=
      (CFSG.RankThreeEvenClassification.Helpers.pCoreOf_le_pCoreOf_of_normal 2 _ _ le_sup_left
        hL₀n).trans (pCoreOf_two_le_of_isSylowTwoOf
          (isSylowTwoOf_of_quasithinIsSylowTwo hfsu.sylow le_sup_right))
    exact OE1.eq_commutator_thompsonJ hperf hfsu.quasisimple hT2 hL₀L hOT
      (by rw [hOC]; exact hJ)
  ·
    exfalso
    have hVT : fsuV T I ≤ T := (A4.le_pCoreOf_of_isTwoReducedIn hred).trans (by
      rw [hOC]
      exact inf_le_left)
    have hYne : fsuV T I ⊓ centralizer (fsuL0 T L : Set G) ≠ ⊥ := by
      intro h
      apply hne
      rw [(h4 G T L I hfsu).2, h, OE1.conjClosure_bot]
    have hTY : T ≤ normalizer
        ((fsuV T I ⊓ centralizer (fsuL0 T L : Set G) : Subgroup G) : Set G) :=
      OE1.le_normalizer_inf (le_normalizer_conjClosure I T)
        ((le_normalizer_conjClosure L T).trans (OE1.normalizer_le_normalizer_centralizer _))
    obtain ⟨z, hzY, hz1, hzT⟩ :=
      OE1.exists_ne_one_mem_centralizer hT2 (inf_le_left.trans hVT) hTY hYne
    have hle : fsuL0 T L ⊔ T ≤ centralizer ({z} : Set G) := sup_le
      (fun l hl => Subgroup.mem_centralizer_singleton_iff.mpr (mem_centralizer_iff.mp hzY.2 l hl))
      (fun t ht => Subgroup.mem_centralizer_singleton_iff.mpr (mem_centralizer_iff.mp hzT t ht))
    have hzc : z ∈ CFSG.Quasithin.centerOf (fsuL0 T L ⊔ T) :=
      ⟨hVH hzY.1, mem_centralizer_iff.mpr fun g hg =>
        Subgroup.mem_centralizer_singleton_iff.mp (hle hg)⟩
    rw [hZ, mem_bot] at hzc
    exact hz1 hzc

end CFSG.Quasithin.Vol2.Ch11
