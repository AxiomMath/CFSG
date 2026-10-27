module

public import CFSG.LocalAnalysis.EvenSporadicStandard.Solomon78.BRowAbstract
public import CFSG.Monster.B.CTIB.SylowCenter
public import CFSG.Monster.B.CTIB.CoreCensus
public import CFSG.Monster.B.CTIB.FourClasses
public import CFSG.Monster.Existence.BabyTableIVOf
public import CFSG.Monster.Existence.BabyW3Classes
public import CFSG.LocalAnalysis.EvenSporadicStandard.Common
public import CFSG.LocalAnalysis.EvenSporadicStandard.Solomon78.Out1SlimEquiv
public import CFSG.LocalAnalysis.ZStar.BrauerSylowFusion
public import CFSG.LocalAnalysis.ZStar.PrincipalBlockTraceApplication
public import CFSG.Walter.JRFacts

public section

attribute [-instance] instCommGroupOfIsSimpleGroupOfIsNilpotent
  instAddCommGroupOfIsSimpleAddGroupOfIsNilpotent

namespace CFSG.EvenSporadicStandard.Solomon78

open Subgroup CFSG.Monster.B CFSG.Monster.B.CTIB CFSG.Monster.B.CTIB.Native CFSG.Monster.GMS
  CFSG.Monster.Existence CFSG.Blueprint.NativeSporadic

attribute [local instance] kvLeft


@[expose] def path171 : List ℕ :=
  [0, 1, 0, 1, 0, 1, 0, 1, 1, 1, 0, 1, 1, 0, 1, 1, 1, 1, 0, 1, 1, 0, 1, 1, 0, 1, 1, 0, 1]

theorem vecW_mem_orbit_of_path
    (path : List ℕ) (hp : ∀ m ∈ path, m < 2) (v : ℕ) :
    vecW (path.foldl (fun x m => censusAct m x) v) ∈
      MulAction.orbit (Subgroup.closure (censusGen '' {m | m < 2})) (vecW v) := by
  induction path generalizing v with
  | nil => exact MulAction.mem_orbit_self _
  | cons m rest ih =>
    have hm : m < 2 := hp m (List.mem_cons_self ..)
    have h1 := ih (fun x hx => hp x (List.mem_cons_of_mem _ hx)) (censusAct m v)
    have h2 : vecW (censusAct m v) ∈
        MulAction.orbit (Subgroup.closure (censusGen '' {m | m < 2})) (vecW v) := by
      rw [vecW_censusAct hm]
      exact ⟨⟨censusGen m, Subgroup.subset_closure ⟨m, hm, rfl⟩⟩, rfl⟩
    rw [MulAction.orbit_eq_iff.2 h2] at h1
    exact h1

set_option maxRecDepth 100000 in
theorem babyW3W4Commute_B : BabyW3W4Commute := by
  have hcomm : Commute (rs 5) (qS 171) := by
    have e : qS 171 * hs 6 = hs 6 * qS (autApply gArr liftImgs6.toArray 171) := by
      rw [← conj_hs6_qS]
      group
    show rs 5 * qS 171 = qS 171 * rs 5
    rw [show rs 5 = hs 6 * qS 61 from rfl, mul_assoc, qS_mul, ← mul_assoc, e, mul_assoc, qS_mul,
      show qmul gArr (autApply gArr liftImgs6.toArray 171) 61 = qmul gArr 61 171 by decide]
  have h0 : psiS (qS 7) ≠ 0 := psiS_qS_ne_zero (by decide)
  have hmem : psiS (qS 171) ∈ jOrbit (qS 7) := by
    rw [jOrbit_code]
    have h := vecW_mem_orbit_of_path path171 (by decide) 7
    have e : path171.foldl (fun x m => censusAct m x) 7 = 171 := by decide
    rwa [e] at h
  have hconj : IsConj (qS 171) (qS 7) := by
    apply isConj_of_mem_jClass
    rw [jClass_eq_fiber (qS_mem 7) h0]
    exact ⟨qS_mem 171, hmem⟩
  have h3 : BabyInv 2 (babyRep 3) :=
    ⟨orderOf_babyRep (by norm_num), natCard_centralizer_rep_three⟩
  refine ⟨babyRep 5, iotaEquiv.symm (qS 171), babyInv_three_babyRep_five,
    BabyInv.of_isConj h3 ?_, ?_⟩
  · have h : IsConj (rs 3) (qS 171) := by
      rw [rs3_eq]
      exact hconj.symm
    obtain ⟨c, hc⟩ := isConj_iff.1 h
    refine isConj_iff.2 ⟨iotaEquiv.symm c, ?_⟩
    have e : iotaEquiv.symm c * iotaEquiv.symm (rs 3) * (iotaEquiv.symm c)⁻¹ =
        iotaEquiv.symm (c * rs 3 * c⁻¹) := by
      rw [map_mul, map_mul, map_inv]
    exact e.trans (congrArg iotaEquiv.symm hc)
  · show iotaEquiv.symm (rs 5) * iotaEquiv.symm (qS 171) =
      iotaEquiv.symm (qS 171) * iotaEquiv.symm (rs 5)
    rw [← map_mul, ← map_mul, hcomm.eq]

end CFSG.EvenSporadicStandard.Solomon78
