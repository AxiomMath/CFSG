module

public import CFSG.ClassicalInvolution.Q3.PhilipHall.Frame.TwinPerpSmSp1Wit
public import CFSG.CGT.PushingUpLit.SolKNA.R4.TwinLeafQ16J2
public import Certificates.Certificate397505

public section

namespace CFSG.ClassicalInvolution.Q3.PhilipHall.Frame.TwinPerp.Small.SP1

open CFSG CFSG.Open CFSG.ClassicalInvolution CFSG.ClassicalInvolution.Q3
open CFSG.Monster.B.Co2 CFSG.Monster.B.Co2.Native CFSG.RankThree.Native
open CFSG.CGT.PushingUpLit.SolKNA.R4.Check (qGens)
open Certificates.TwinPerpSmSp1

set_option linter.unusedSectionVars false

theorem j2SmallAutModel :
    CFSG.Sporadic.SmallOddCore.AutModel CFSG.ComponentClassification.J2Cover.P
      CFSG.ComponentClassification.J2Cover.R where
  le := CFSG.ComponentClassification.J2Cover.P_le_R
  conj_mem x hx p hp :=
    (Subgroup.mem_normalizer_iff.1 (CFSG.ComponentClassification.J2Cover.R_le_normalizer hx) p).1
      hp
  surj α := by
    obtain ⟨r, hr⟩ := CFSG.ComponentClassification.J2Cover.rConj_bijective.2 α
    exact ⟨r, r.2, fun p => by rw [← hr, CFSG.ComponentClassification.J2Cover.rConj_apply]⟩
  inj x _ hc := by
    have hx : x ∈ Subgroup.centralizer
        (CFSG.ComponentClassification.J2Cover.P : Set (Equiv.Perm (Fin 315))) :=
      Subgroup.mem_centralizer_iff.2 fun p hp => (hc p hp).symm
    rw [CFSG.ComponentClassification.J2Cover.centralizer_P, Subgroup.mem_bot] at hx
    exact hx

theorem j2Syl_le_R :
    Subgroup.closure (permsA 315 (qGens j2Wit.syl)) ≤ CFSG.ComponentClassification.J2Cover.R := by
  have h := Certificates.certificate397505.2.1.1
  refine syl_le_of_q8WitCheck j2Wit h _ fun l hl => ?_
  have hv := pg_valid_of_q8WitCheck j2Wit h l hl
  have hsz : j2Wit.syl.pg.size = 3 := rfl
  have hl3 : l < 3 := by rw [← hsz]; exact hl
  have hget : j2Wit.syl.pg[l]! = CFSG.ComponentClassification.J2Cover.sylowStrong[l]! :=
    CFSG.CGT.PushingUpLit.SolKNA.R4.TwinLeaf.j2Q16_pg_get hl3
  rw [hget] at hv ⊢
  interval_cases l
  · exact CFSG.CGT.PushingUpLit.SolKNA.R4.TwinLeaf.perm_mem_R_of_sylow hv
      CFSG.ComponentClassification.J2Cover.sylow_check.2.2.1
  · exact CFSG.CGT.PushingUpLit.SolKNA.R4.TwinLeaf.perm_mem_R_of_sylow hv
      CFSG.ComponentClassification.J2Cover.sylow_check.2.2.2.1
  · exact CFSG.CGT.PushingUpLit.SolKNA.R4.TwinLeaf.perm_mem_R_of_sylow hv
      CFSG.ComponentClassification.J2Cover.sylow_check.2.2.2.2


theorem leaf_j2 {n : ℕ} :
    NoTwinS n (fun F _ => CFSG.Blueprint.NativeSporadic.IsSporadic F .J2) := by
  have h := Certificates.certificate397505.2.1.1
  refine noTwinS_of_q8Wit j2SmallAutModel (Subgroup.closure (permsA 315 (qGens j2Wit.syl)))
    j2Syl_le_R (k := 8) (m := 4725) (card_syl_of_q8WitCheck j2Wit h) (by decide)
    (by rw [CFSG.ComponentClassification.J2Cover.card_R]; norm_num)
    (hwit_of_q8WitCheck j2Wit rfl h _ fun l hl => ?_) ?_
  · exact (CFSG.ComponentClassification.J2Cover.mem_P_iff
      (rep_of_validA (xg_valid_of_q8WitCheck j2Wit h l hl))).1
      (allLt_spec Certificates.certificate397505.2.1.2 hl)
  · intro Y _ _ R' S t hP hF
    obtain ⟨ψ⟩ := hF
    haveI := hP.core.simple
    haveI : (genFittingFStar Y).Normal := genFittingFStar_normal Y
    refine ⟨⟨ψ.trans CFSG.ComponentClassification.J2Cover.nativeEquivP⟩, ?_⟩
    exact isPGroup_core_of_oddCore hP
      (CFSG.ComponentClassification.J2Cover.ctuc_j2_almost_simple_involution_centralizer_odd_core_trivial
        (genFittingFStar Y) ψ (Nobq.centralizer_genFittingFStar_eq_bot hP.core.nonab) t
        hP.core.datum.order)

end CFSG.ClassicalInvolution.Q3.PhilipHall.Frame.TwinPerp.Small.SP1
