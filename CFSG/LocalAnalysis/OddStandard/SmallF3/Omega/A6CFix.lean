module

public import CFSG.LocalAnalysis.OddStandard.SmallF3.Omega.FF6MK0
public import CFSG.LocalAnalysis.OddStandard.SmallF3.Omega.FF6MK3
public import CFSG.LocalAnalysis.OddStandard.SmallF3.Omega.FF6MK4
public import CFSG.LocalAnalysis.OddStandard.SmallF3.Omega.FF6MN1
public import CFSG.LocalAnalysis.OddStandard.SmallF3.Omega.FF6MN2
public import CFSG.LocalAnalysis.OddStandard.SmallF3.Omega.FF6MShapes

public section

attribute [-instance] instAddCommGroupOfIsSimpleAddGroupOfIsNilpotent
  instCommGroupOfIsSimpleGroupOfIsNilpotent

namespace CFSG.OddStandard.SmallF3.Omega

open Subgroup CFSG.Blueprint

variable {V : Type} [AddCommGroup V] [Module (ZMod 3) V] [FiniteDimensional (ZMod 3) V]
  {Q : QuadraticForm (ZMod 3) V}

theorem a6c_fix_small (hQ : Q.Nondegenerate) (hdim : Module.finrank (ZMod 3) V = 6)
    (hsgn : quadSign Q = -1) {y : ProjSim Q} (hy2 : y * y = 1) (hy1 : y ≠ 1)
    (E : Subgroup ↥(omegaProj hQ)) (hE : E ≤ ffFix hQ (by omega) y)
    (hperf : Group.IsPerfect ↥E) (hcard : 6048 < Nat.card ↥E) : KM2 y := by
  have h2 : 2 ≤ Module.finrank (ZMod 3) V := by omega
  have hEF : Group.IsPerfect ↥(E.subgroupOf (ffFix hQ h2 y)) := by
    haveI := hperf
    have h := Group.IsPerfect.range (Subgroup.inclusion hE)
    rwa [Subgroup.inclusion_range] at h
  have hcardEF : Nat.card ↥(E.subgroupOf (ffFix hQ h2 y)) = Nat.card ↥E :=
    Nat.card_congr (Subgroup.subgroupOfEquivOfLe hE).toEquiv
  haveI : Nontrivial ↥(E.subgroupOf (ffFix hQ h2 y)) := by
    rw [← Finite.one_lt_card_iff_nontrivial, hcardEF]
    omega
  have hsolv : ¬ Group.IsSolvable ↥(ffFix hQ h2 y) := by
    intro hs
    haveI := hs
    haveI := hEF
    exact Group.IsPerfect.not_isSolvable (G := ↥(E.subgroupOf (ffFix hQ h2 y))) inferInstance
  rcases ff6m_model_classify hQ hdim hsgn hy2 with h1 | h0 | hn1 | hk2 | h3 | hn2 | h4
  · exact absurd h1 hy1
  · exact absurd (ff6m_K0_solvable hQ hdim hsgn h0) hsolv
  · obtain ⟨E1, hE1, hlie, hq⟩ := ff6m_N1_layerModel hQ hdim hsgn hn1
    haveI : E1.Normal := hE1
    have hle := ff_perfect_le_of_quot_two E1 hq (E.subgroupOf (ffFix hQ h2 y)) hEF
    have hc := Subgroup.card_le_of_le hle
    rw [hcardEF, ff_card_model_psl2 hlie] at hc
    omega
  · exact hk2
  · exact absurd (ff6m_K3_solvable hQ hdim hsgn h3) hsolv
  · obtain ⟨E1, hE1, hlie, hq⟩ := ff6m_N2_layerModel hQ hdim hsgn hn2
    haveI : E1.Normal := hE1
    have hle := ff_perfect_le_of_quot_two E1 hq (E.subgroupOf (ffFix hQ h2 y)) hEF
    have hc := Subgroup.card_le_of_le hle
    rw [hcardEF, ff_card_model_psu3 hlie] at hc
    omega
  · obtain ⟨E1, hE1, hlie, hq⟩ := ff6m_K4_layerModel hQ hdim hsgn hy2 h4
    haveI : E1.Normal := hE1
    have hle := ff_perfect_le_of_quot_two E1 hq (E.subgroupOf (ffFix hQ h2 y)) hEF
    have hc := Subgroup.card_le_of_le hle
    rw [hcardEF, ff_card_model_psl2 hlie] at hc
    omega

end CFSG.OddStandard.SmallF3.Omega
