module

public import CFSG.LocalAnalysis.SeitzReduction.E7PilotClassYCoreChecks
public import CFSG.LocalAnalysis.ComponentClassification.AS76bSec8E7CentLevel
public import CFSG.LocalAnalysis.SeitzReduction.E7PilotClassYBruhat

public section

namespace CFSG.SeitzReduction.E7Pilot

open Subgroup CFSG.Blueprint.Chevalley CFSG.LieType.Chevalley CFSG.LieType.Steinberg.Adjoint
open CFSG.SeitzReduction.E6Pilot (rootProd RootCommFamily conjCoeff rootProd_add
  rootProd_congr rootProd_injective rootProd_zero)

local instance e7ClassYCoreNeZeroRank : NeZero Tag.E7.rank := ⟨by decide⟩

open CFSG.ComponentClassification.RankTwoExceptional.E7Sec8
open CFSG.LieType.Chevalley.RootOps (isRootB isRootB_iff)

section Certs2

theorem yParabolic_le_linConj :
    parabolicSubgroup .E7 (ZMod 2) yNodes ≤ linConjSubgroup (ZMod 2) yPsi := by
  refine parabolicSubgroup_le_linConjSubgroup yPsi_check.1
    (fun _ hβ => isRoot_of_mem_yPsi hβ) yPsi_comm ?_ ?_
  · intro α hα β hβ
    exact conj_hyp_of_yLevel_nonneg (by
      have h := yLevel_pos_of_mem_parabolicRadicalRoots hα
      omega) β hβ
  · intro j hj β hβ
    have hlev : yLevel (Pi.single j 1 : Fin Tag.E7.rank → ℤ) = 0 := by
      simp only [yLevel, Pi.single_eq_of_ne (Ne.symm hj)]
    have hlev' : yLevel (-(Pi.single j 1) : Fin Tag.E7.rank → ℤ) = 0 := by
      rw [yLevel_neg, hlev, neg_zero]
    exact ⟨conj_hyp_of_yLevel_nonneg hlev.ge β hβ,
      conj_hyp_of_yLevel_nonneg hlev'.ge β hβ⟩

noncomputable def yChoice (g : ModGL .E7 (ZMod 2))
    (hg : g ∈ linConjSubgroup (ZMod 2) yPsi) (v : Fin 10 → ZMod 2) :
    (Fin Tag.E7.rank → ℤ) → ZMod 2 :=
  (hg.1 (yDecode v)).choose

noncomputable def yAct (g : ModGL .E7 (ZMod 2))
    (hg : g ∈ linConjSubgroup (ZMod 2) yPsi) (v : Fin 10 → ZMod 2) :
    Fin 10 → ZMod 2 :=
  yRestrict (yChoice g hg v)

theorem yChoice_spec (g : ModGL .E7 (ZMod 2))
    (hg : g ∈ linConjSubgroup (ZMod 2) yPsi) (v : Fin 10 → ZMod 2) :
    g * rootProd .E7 (ZMod 2) yPsi (yDecode v) * g⁻¹ =
      rootProd .E7 (ZMod 2) yPsi (yChoice g hg v) :=
  (hg.1 (yDecode v)).choose_spec.1

theorem yAct_spec (g : ModGL .E7 (ZMod 2))
    (hg : g ∈ linConjSubgroup (ZMod 2) yPsi) (v : Fin 10 → ZMod 2) :
    rootProd .E7 (ZMod 2) yPsi (yDecode (yAct g hg v)) =
      g * rootProd .E7 (ZMod 2) yPsi (yDecode v) * g⁻¹ := by
  rw [yChoice_spec, yAct]
  exact rootProd_congr fun β hβ => by
    rw [yDecode, if_pos hβ, yRestrict, yVec_yIdx hβ]

theorem yAct_eq_of_rootProd_eq {v w : Fin 10 → ZMod 2}
    (h : rootProd .E7 (ZMod 2) yPsi (yDecode v) =
      rootProd .E7 (ZMod 2) yPsi (yDecode w)) : v = w := by
  have h' := E6Pilot.rootProd_injective yPsi_check.1
    (fun β hβ => pos_of_mem_yPsi hβ) h
  funext k
  have := h' (yVec k) (yVec_mem k)
  simpa [yDecode, yVec_mem, yIdx_yVec] using this

theorem yAct_mul (g h : ModGL .E7 (ZMod 2))
    (hg : g ∈ linConjSubgroup (ZMod 2) yPsi)
    (hh : h ∈ linConjSubgroup (ZMod 2) yPsi) (v : Fin 10 → ZMod 2) :
    yAct (g * h) (mul_mem hg hh) v = yAct g hg (yAct h hh v) := by
  apply yAct_eq_of_rootProd_eq
  rw [yAct_spec (g * h) (mul_mem hg hh) v, yAct_spec g hg (yAct h hh v),
    yAct_spec h hh v]
  group

theorem yAct_one (v : Fin 10 → ZMod 2) :
    yAct 1 (one_mem (linConjSubgroup (ZMod 2) yPsi)) v = v := by
  apply yAct_eq_of_rootProd_eq
  rw [yAct_spec]
  group

theorem yAct_zero (g : ModGL .E7 (ZMod 2))
    (hg : g ∈ linConjSubgroup (ZMod 2) yPsi) :
    yAct g hg (0 : Fin 10 → ZMod 2) = 0 := by
  apply yAct_eq_of_rootProd_eq
  have hz : yDecode (0 : Fin 10 → ZMod 2) = 0 := by
    funext β
    simp [yDecode]
  have hzr : rootProd .E7 (ZMod 2) yPsi (yDecode (0 : Fin 10 → ZMod 2)) = 1 := by
    rw [show rootProd .E7 (ZMod 2) yPsi (yDecode (0 : Fin 10 → ZMod 2)) =
      rootProd .E7 (ZMod 2) yPsi (0 : (Fin Tag.E7.rank → ℤ) → ZMod 2) from by rw [hz]]
    exact rootProd_zero yPsi
  calc rootProd .E7 (ZMod 2) yPsi (yDecode (yAct g hg 0)) =
        g * rootProd .E7 (ZMod 2) yPsi (yDecode 0) * g⁻¹ := yAct_spec g hg 0
    _ = g * 1 * g⁻¹ := by rw [hzr]
    _ = 1 := by group
    _ = rootProd .E7 (ZMod 2) yPsi (yDecode 0) := hzr.symm

theorem yAct_add (g : ModGL .E7 (ZMod 2))
    (hg : g ∈ linConjSubgroup (ZMod 2) yPsi) (v w : Fin 10 → ZMod 2) :
    yAct g hg (v + w) = yAct g hg v + yAct g hg w := by
  apply yAct_eq_of_rootProd_eq
  have hx : rootProd .E7 (ZMod 2) yPsi (yDecode (v + w)) =
      rootProd .E7 (ZMod 2) yPsi (yDecode v) *
        rootProd .E7 (ZMod 2) yPsi (yDecode w) := by
    rw [← rootProd_add yPsi_comm]
    exact rootProd_congr fun β hβ => by
      simp only [yDecode, if_pos hβ, Pi.add_apply]
  have hy : rootProd .E7 (ZMod 2) yPsi (yDecode (yAct g hg v + yAct g hg w)) =
      rootProd .E7 (ZMod 2) yPsi (yDecode (yAct g hg v)) *
        rootProd .E7 (ZMod 2) yPsi (yDecode (yAct g hg w)) := by
    rw [← rootProd_add yPsi_comm]
    exact rootProd_congr fun β hβ => by
      simp only [yDecode, if_pos hβ, Pi.add_apply]
  calc rootProd .E7 (ZMod 2) yPsi (yDecode (yAct g hg (v + w))) =
        g * rootProd .E7 (ZMod 2) yPsi (yDecode (v + w)) * g⁻¹ := yAct_spec g hg (v + w)
    _ = g * (rootProd .E7 (ZMod 2) yPsi (yDecode v) *
          rootProd .E7 (ZMod 2) yPsi (yDecode w)) * g⁻¹ := by rw [hx]
    _ = (g * rootProd .E7 (ZMod 2) yPsi (yDecode v) * g⁻¹) *
          (g * rootProd .E7 (ZMod 2) yPsi (yDecode w) * g⁻¹) := by group
    _ = rootProd .E7 (ZMod 2) yPsi (yDecode (yAct g hg v)) *
          rootProd .E7 (ZMod 2) yPsi (yDecode (yAct g hg w)) := by
        rw [yAct_spec g hg v, yAct_spec g hg w]
    _ = rootProd .E7 (ZMod 2) yPsi (yDecode (yAct g hg v + yAct g hg w)) := hy.symm

theorem yAct_smul (g : ModGL .E7 (ZMod 2))
    (hg : g ∈ linConjSubgroup (ZMod 2) yPsi) (t : ZMod 2) (v : Fin 10 → ZMod 2) :
    yAct g hg (t • v) = t • yAct g hg v := by
  have ht : t = 0 ∨ t = 1 := by
    revert t
    decide
  rcases ht with rfl | rfl
  · rw [zero_smul, zero_smul]
    exact yAct_zero g hg
  · rw [one_smul, one_smul]

noncomputable def yIsoSubgroup : Subgroup (ModGL .E7 (ZMod 2)) where
  carrier := {g | ∃ hg : g ∈ linConjSubgroup (ZMod 2) yPsi,
    ∀ v, yQ (yAct g hg v) = yQ v}
  mul_mem' := by
    rintro g h ⟨hg, hgQ⟩ ⟨hh, hhQ⟩
    refine ⟨mul_mem hg hh, fun v => ?_⟩
    rw [yAct_mul g h hg hh]
    exact (hgQ _).trans (hhQ v)
  one_mem' := ⟨one_mem _, fun v => by rw [yAct_one]⟩
  inv_mem' := by
    rintro g ⟨hg, hgQ⟩
    refine ⟨inv_mem hg, fun v => ?_⟩
    have h1 : yAct g hg (yAct g⁻¹ (inv_mem hg) v) = v := by
      apply yAct_eq_of_rootProd_eq
      rw [yAct_spec g hg (yAct g⁻¹ (inv_mem hg) v), yAct_spec g⁻¹ (inv_mem hg) v]
      group
    calc yQ (yAct g⁻¹ (inv_mem hg) v)
        = yQ (yAct g hg (yAct g⁻¹ (inv_mem hg) v)) := (hgQ _).symm
      _ = yQ v := by rw [h1]

theorem yPinnedX_mem_yIsoSubgroup {α : Fin Tag.E7.rank → ℤ}
    (hα : α ∈ yLevelZeroRoots) (t : ZMod 2) :
    pinnedX .E7 (ZMod 2) α t ∈ yIsoSubgroup := by
  have hroot := yIsRoot_of_mem_yLevelZeroRoots hα
  have hlev := yLevel_of_mem_yLevelZeroRoots hα
  have hlin := pinnedX_mem_linConjSubgroup yPsi_check.1
    (fun _ hβ => isRoot_of_mem_yPsi hβ) yPsi_comm hroot
    (conj_hyp_of_yLevel_nonneg hlev.ge) t
  refine ⟨hlin, fun v => ?_⟩
  have hconj := conj_rootProd_yPsi hroot hlev.ge t (yDecode v)
  have hact : yAct (pinnedX .E7 (ZMod 2) α t) hlin v =
      yRestrict (conjCoeff α t yPsi (yDecode v)) := by
    apply yAct_eq_of_rootProd_eq
    calc rootProd .E7 (ZMod 2) yPsi
            (yDecode (yAct (pinnedX .E7 (ZMod 2) α t) hlin v)) =
          pinnedX .E7 (ZMod 2) α t *
            rootProd .E7 (ZMod 2) yPsi (yDecode v) *
              (pinnedX .E7 (ZMod 2) α t)⁻¹ := yAct_spec _ _ _
      _ = rootProd .E7 (ZMod 2) yPsi (conjCoeff α t yPsi (yDecode v)) := hconj
      _ = rootProd .E7 (ZMod 2) yPsi
            (yDecode (yRestrict (conjCoeff α t yPsi (yDecode v)))) :=
          (rootProd_congr fun β hβ => by
            rw [yDecode, if_pos hβ, yRestrict, yVec_yIdx hβ]).symm
  rw [hact, yRestrict_conjCoeff, yRestrict_yDecode]
  exact yLevelZeroRoots_qcheck α hα t v

theorem yPinnedX_mem_yIsoSubgroup_radical {α : Fin Tag.E7.rank → ℤ}
    (hα : α ∈ parabolicRadicalRoots .E7 yNodes) (t : ZMod 2) :
    pinnedX .E7 (ZMod 2) α t ∈ yIsoSubgroup := by
  have hroot : IsRoot .E7 α := hα.1.1
  have hlin := pinnedX_mem_linConjSubgroup yPsi_check.1
    (fun _ hβ => isRoot_of_mem_yPsi hβ) yPsi_comm hroot
    (fun β hβ => conj_hyp_of_yLevel_nonneg (by
      have h := yLevel_pos_of_mem_parabolicRadicalRoots hα; omega) β hβ) t
  refine ⟨hlin, fun v => ?_⟩
  have hmem : pinnedX .E7 (ZMod 2) α t ∈ parabolicRadical .E7 (ZMod 2) yNodes :=
    Subgroup.mem_iSup_of_mem α
      (Subgroup.mem_iSup_of_mem hα (Subgroup.subset_closure ⟨t, rfl⟩))
  have hcomm : Commute (pinnedX .E7 (ZMod 2) α t)
      (rootProd .E7 (ZMod 2) yPsi (yDecode v)) :=
    mem_centralizer_singleton_iff.1
      ((parabolicRadical_le_centralizer_rootProd_yPsi (yDecode v)) hmem)
  have hfix : pinnedX .E7 (ZMod 2) α t *
      rootProd .E7 (ZMod 2) yPsi (yDecode v) *
        (pinnedX .E7 (ZMod 2) α t)⁻¹ =
      rootProd .E7 (ZMod 2) yPsi (yDecode v) := by
    rw [hcomm.eq]; group
  have hact := yAct_spec (pinnedX .E7 (ZMod 2) α t) hlin v
  rw [hfix] at hact
  have hdec : yDecode (yAct (pinnedX .E7 (ZMod 2) α t) hlin v) = yDecode v := by
    funext β
    by_cases hβ : β ∈ yPsi
    · exact rootProd_injective yPsi_check.1 (fun β hβ => pos_of_mem_yPsi hβ) hact β hβ
    · simp only [yDecode, if_neg hβ]
  have hactv : yAct (pinnedX .E7 (ZMod 2) α t) hlin v = v := by
    calc yAct (pinnedX .E7 (ZMod 2) α t) hlin v =
          yRestrict (yDecode (yAct (pinnedX .E7 (ZMod 2) α t) hlin v)) :=
          (yRestrict_yDecode _).symm
      _ = yRestrict (yDecode v) := by rw [hdec]
      _ = v := yRestrict_yDecode v
  rw [hactv]

theorem ySimple_mem_yLevelZeroRoots {j : Fin Tag.E7.rank} (hj : j ∈ yNodes) :
    (Pi.single j (1 : ℤ) : Fin Tag.E7.rank → ℤ) ∈ yLevelZeroRoots ∧
      (-Pi.single j (1 : ℤ) : Fin Tag.E7.rank → ℤ) ∈ yLevelZeroRoots := by
  have hj' : j ≠ 5 := by simpa only [yNodes, Set.mem_ofPred_eq] using hj
  exact ySingle_mem_levelZero j hj'

theorem yTorusGroup_le_yIsoSubgroup : torusGroup .E7 (ZMod 2) ≤ yIsoSubgroup := by
  have hunit : ∀ u : (ZMod 2)ˣ, u = 1 := fun u => Subsingleton.elim u 1
  rw [CFSG.SeitzReduction.EPilot.torusGroup_eq_bot_of_forall_units_eq_one (τ := .E7)
    (K := ZMod 2) hunit]
  exact bot_le

theorem yParabolic_le_yIsoSubgroup :
    parabolicSubgroup .E7 (ZMod 2) yNodes ≤ yIsoSubgroup := by
  rw [← parabolicRadical_sup_parabolicLevi yNodes]
  refine sup_le (iSup₂_le fun α hα => (Subgroup.closure_le _).2 ?_) (sup_le
    yTorusGroup_le_yIsoSubgroup ((Subgroup.closure_le _).2 ?_))
  · rintro _ ⟨t, rfl⟩
    exact yPinnedX_mem_yIsoSubgroup_radical hα t
  · rintro _ ⟨j, hj, t, rfl | rfl⟩
    · rw [← pinnedX_single]
      exact yPinnedX_mem_yIsoSubgroup (ySimple_mem_yLevelZeroRoots hj).1 t
    · rw [← pinnedX_neg_single]
      exact yPinnedX_mem_yIsoSubgroup (ySimple_mem_yLevelZeroRoots hj).2 t

theorem yAct_yQ_of_parabolic_mem {g : ModGL .E7 (ZMod 2)}
    (hg : g ∈ parabolicSubgroup .E7 (ZMod 2) yNodes)
    (hgl : g ∈ linConjSubgroup (ZMod 2) yPsi) (v : Fin 10 → ZMod 2) :
    yQ (yAct g hgl v) = yQ v := by
  obtain ⟨hgl', hQ⟩ := yParabolic_le_yIsoSubgroup hg
  rw [show yAct g hgl v = yAct g hgl' v from rfl]
  exact hQ v

theorem yRestrict_yCoeff : yRestrict (yCoeff (K := ZMod 2)) = yY := by
  decide +kernel

theorem yRootProd_eq_of_yRestrict_eq {c d : (Fin Tag.E7.rank → ℤ) → ZMod 2}
    (h : yRestrict c = yRestrict d) :
    rootProd .E7 (ZMod 2) yPsi c = rootProd .E7 (ZMod 2) yPsi d :=
  rootProd_congr fun β hβ => by
    have := congrFun h (yIdx β)
    simpa [yRestrict, yVec_yIdx hβ] using this

theorem yRootProd_yPsi_yCoeff_eq :
    rootProd .E7 (ZMod 2) yPsi (yDecode yY) = yAS (ZMod 2) := by
  rw [yRootProd_eq_of_yRestrict_eq (c := yDecode yY) (d := yCoeff (K := ZMod 2))
    (by rw [yRestrict_yDecode, yRestrict_yCoeff])]
  exact rootProd_yPsi_yCoeff

theorem yLift_proj {v : Fin 10 → ZMod 2} (hv : yB v yY = 0) :
    yLiftFun (yProjFun v) = v + (v 0) • yY := by
  have hB : yB (yOf2 (yTo2 v)) yY = 0 := by rwa [yOf2_yTo2]
  have h := yLift_proj_check (yTo2 v) hB
  rwa [yOf2_yTo2] at h

theorem yProj_kernel {v : Fin 10 → ZMod 2} (hv : yB v yY = 0) (hp : yProjFun v = 0) :
    v = 0 ∨ v = yY := by
  have hB : yB (yOf2 (yTo2 v)) yY = 0 := by rwa [yOf2_yTo2]
  have hp' : yProjFun (yOf2 (yTo2 v)) = 0 := by rwa [yOf2_yTo2]
  have h := yProj_kernel_check (yTo2 v) hB hp'
  rwa [yOf2_yTo2] at h

@[expose] noncomputable def yActLin (g : ModGL .E7 (ZMod 2))
    (hg : g ∈ linConjSubgroup (ZMod 2) yPsi) :
    (Fin 10 → ZMod 2) →ₗ[ZMod 2] (Fin 10 → ZMod 2) where
  toFun := yAct g hg
  map_add' := yAct_add g hg
  map_smul' := yAct_smul g hg

@[expose] noncomputable def yN : Subgroup (adjointGroup .E7 (ZMod 2)) :=
  CFSG.Open.pCoreOf 2 (centralizer ({e7ASRep (ZMod 2) 1} : Set (adjointGroup .E7 (ZMod 2))))

theorem yN_le_centralizer :
    yN ≤ centralizer ({e7ASRep (ZMod 2) 1} : Set (adjointGroup .E7 (ZMod 2))) :=
  CFSG.LieType.BorelTits.pCoreOf_le (r := 2) _

theorem yN_isPGroup : IsPGroup 2 yN :=
  CFSG.LieType.BorelTits.pCoreOf_isPGroup (r := 2) _

theorem yN_mem_parabolic (n : yN) :
    (n : ModGL .E7 (ZMod 2)) ∈ parabolicSubgroup .E7 (ZMod 2) yNodes :=
  mem_subgroupOf.1 (centralizer_e7ASRep_one_le_parabolic (yN_le_centralizer n.2))

theorem yN_mem_linConj (n : yN) :
    (n : ModGL .E7 (ZMod 2)) ∈ linConjSubgroup (ZMod 2) yPsi :=
  yParabolic_le_linConj (yN_mem_parabolic n)

theorem yN_commute_yAS (n : yN) :
    (n : ModGL .E7 (ZMod 2)) * yAS (ZMod 2) = yAS (ZMod 2) * (n : ModGL .E7 (ZMod 2)) := by
  have h := congrArg Subtype.val (mem_centralizer_singleton_iff.1 (yN_le_centralizer n.2))
  simpa only [Subgroup.coe_mul, coe_e7ASRep_one] using h

@[expose] noncomputable def yActN (n : yN) : (Fin 10 → ZMod 2) →ₗ[ZMod 2] (Fin 10 → ZMod 2) :=
  yActLin (n : ModGL .E7 (ZMod 2)) (yN_mem_linConj n)

theorem yActN_apply (n : yN) (v : Fin 10 → ZMod 2) :
    yActN n v = yAct (n : ModGL .E7 (ZMod 2)) (yN_mem_linConj n) v := rfl

theorem yActN_one : yActN (1 : yN) = 1 :=
  LinearMap.ext fun v => yAct_one v

theorem yActN_mul (m n : yN) : yActN (m * n) = (yActN m).comp (yActN n) :=
  LinearMap.ext fun v => yAct_mul (m : ModGL .E7 (ZMod 2)) (n : ModGL .E7 (ZMod 2))
    (yN_mem_linConj m) (yN_mem_linConj n) v

theorem yActN_yY (n : yN) : yActN n yY = yY := by
  apply yAct_eq_of_rootProd_eq
  rw [yActN_apply, yAct_spec, yRootProd_yPsi_yCoeff_eq, yN_commute_yAS]
  group

theorem yActN_yQ (n : yN) (v : Fin 10 → ZMod 2) : yQ (yActN n v) = yQ v :=
  yAct_yQ_of_parabolic_mem (yN_mem_parabolic n) (yN_mem_linConj n) v

theorem yActN_yB (n : yN) (v w : Fin 10 → ZMod 2) :
    yB (yActN n v) (yActN n w) = yB v w := by
  simp only [yB]
  rw [← map_add (yActN n), yActN_yQ, yActN_yQ, yActN_yQ]

theorem yActN_mem_yPerp (n : yN) {v : Fin 10 → ZMod 2} (hv : yB v yY = 0) :
    yB (yActN n v) yY = 0 := by
  rw [← yActN_yY n, yActN_yB n v yY, hv]

@[expose] noncomputable def yProjLin : (Fin 10 → ZMod 2) →ₗ[ZMod 2] (Fin 8 → ZMod 2) where
  toFun := yProjFun
  map_add' u v := by
    funext j
    rfl
  map_smul' c u := by
    funext j
    rfl

theorem yProj_add (a b : Fin 10 → ZMod 2) :
    yProjFun (a + b) = yProjFun a + yProjFun b := map_add yProjLin a b

theorem yProj_smul (c : ZMod 2) (a : Fin 10 → ZMod 2) :
    yProjFun (c • a) = c • yProjFun a := map_smul yProjLin c a

@[expose] noncomputable def ySmul (n : yN) (u : Fin 8 → ZMod 2) : Fin 8 → ZMod 2 :=
  yProjFun (yActN n (yLiftFun u))

theorem yLift_zero : yLiftFun (0 : Fin 8 → ZMod 2) = 0 := by
  funext k
  by_cases h : (k : ℕ) < 2 <;> simp [yLiftFun, h]

theorem yProj_zero : yProjFun (0 : Fin 10 → ZMod 2) = 0 := rfl

theorem ySmul_zero (n : yN) : ySmul n (0 : Fin 8 → ZMod 2) = 0 := by
  rw [ySmul, yLift_zero, map_zero, yProj_zero]

noncomputable instance yMulAction : MulAction yN (Fin 8 → ZMod 2) where
  smul := ySmul
  one_smul u := by
    change yProjFun (yActN (1 : yN) (yLiftFun u)) = u
    rw [yActN_one]
    exact yProj_lift u
  mul_smul m n u := by
    have hvB : yB (yActN n (yLiftFun u)) yY = 0 :=
      yActN_mem_yPerp n (yLift_mem_yPerp u)
    have hlift := yLift_proj hvB
    change yProjFun (yActN (m * n) (yLiftFun u)) =
      yProjFun (yActN m (yLiftFun (yProjFun (yActN n (yLiftFun u)))))
    rw [yActN_mul, LinearMap.comp_apply]
    conv_rhs => rw [hlift]
    rw [map_add, map_smul, yActN_yY, yProj_add, yProj_smul, yProj_yY, smul_zero, add_zero]

theorem yN_exists_fixed :
    ∃ u : Fin 8 → ZMod 2, u ≠ 0 ∧ ∀ n : yN, ySmul n u = u := by
  have hcard : Nat.card (Fin 8 → ZMod 2) = 256 := by
    rw [Nat.card_eq_fintype_card, Fintype.card_fun]
    norm_num [ZMod.card]
  have hmod := IsPGroup.card_modEq_card_fixedPoints (p := 2) yN_isPGroup
    (Fin 8 → ZMod 2)
  have h0 : (0 : Fin 8 → ZMod 2) ∈ MulAction.fixedPoints yN (Fin 8 → ZMod 2) := by
    rw [MulAction.mem_fixedPoints]
    intro n
    exact ySmul_zero n
  haveI : Fintype (MulAction.fixedPoints yN (Fin 8 → ZMod 2)) := Fintype.ofFinite _
  have hmod2 : Nat.card (MulAction.fixedPoints yN (Fin 8 → ZMod 2)) % 2 = 0 := by
    have h : Nat.card (Fin 8 → ZMod 2) ≡
        Nat.card (MulAction.fixedPoints yN (Fin 8 → ZMod 2)) [MOD 2] := hmod
    rw [hcard] at h
    change (256 : ℕ) % 2 =
      Nat.card (MulAction.fixedPoints yN (Fin 8 → ZMod 2)) % 2 at h
    have h2 : (256 : ℕ) % 2 = 0 := by norm_num
    rw [h2] at h
    omega
  have hdvd : 2 ∣ Nat.card (MulAction.fixedPoints yN (Fin 8 → ZMod 2)) :=
    Nat.dvd_iff_mod_eq_zero.2 hmod2
  haveI hne : Nonempty (MulAction.fixedPoints yN (Fin 8 → ZMod 2)) := ⟨⟨0, h0⟩⟩
  have hpos : 0 < Nat.card (MulAction.fixedPoints yN (Fin 8 → ZMod 2)) := Nat.card_pos
  have hge : 2 ≤ Nat.card (MulAction.fixedPoints yN (Fin 8 → ZMod 2)) :=
    Nat.le_of_dvd hpos hdvd
  have hlt : 1 < Fintype.card (MulAction.fixedPoints yN (Fin 8 → ZMod 2)) := by
    rw [← Nat.card_eq_fintype_card]
    omega
  obtain ⟨u, hune⟩ := Fintype.exists_ne_of_one_lt_card hlt ⟨0, h0⟩
  refine ⟨u.1, ?_, ?_⟩
  · intro hu
    exact hune (Subtype.ext hu)
  · intro n
    exact MulAction.mem_fixedPoints.1 u.2 n

theorem yN_fixed_w :
    ∃ w : Fin 10 → ZMod 2, yB w yY = 0 ∧ w ≠ 0 ∧ w ≠ yY ∧
      ∀ n : yN, yActN n w = w ∨ yActN n w = w + yY := by
  obtain ⟨u, hu0, hufix⟩ := yN_exists_fixed
  refine ⟨yLiftFun u, yLift_mem_yPerp u, yLift_ne_zero hu0, yLift_ne_yY u, ?_⟩
  intro n
  have hv : yProjFun (yActN n (yLiftFun u)) = u := hufix n
  have hxperp : yB (yActN n (yLiftFun u) + yLiftFun u) yY = 0 := by
    rw [yB_add_left, yActN_mem_yPerp n (yLift_mem_yPerp u), yLift_mem_yPerp u, add_zero]
  have hxproj : yProjFun (yActN n (yLiftFun u) + yLiftFun u) = 0 := by
    rw [yProj_add, hv, yProj_lift u]
    rw [← two_smul (ZMod 2) u]
    have h2 : (2 : ZMod 2) = 0 := by decide
    rw [h2, zero_smul]
  have hx := yProj_kernel hxperp hxproj
  rcases hx with h0 | hy
  · left
    exact yEq_of_add_eq_zero h0
  · right
    exact yEq_of_add_eq hy

@[expose] def yT : Set (Fin 10 → ZMod 2) :=
  {w | yB w yY = 0 ∧ ∀ n : yN, yActN n w = w ∨ yActN n w = w + yY}

theorem yT_add (u v : Fin 10 → ZMod 2) (hu : u ∈ yT) (hv : v ∈ yT) : u + v ∈ yT := by
  obtain ⟨huB, huN⟩ := hu
  obtain ⟨hvB, hvN⟩ := hv
  refine ⟨?_, ?_⟩
  · rw [yB_add_left, huB, hvB, add_zero]
  · intro n
    rw [map_add]
    rcases huN n with h1 | h1 <;> rcases hvN n with h2 | h2 <;> rw [h1, h2]
    · left; rfl
    · right; abel
    · right; abel
    · left
      calc u + yY + (v + yY) = u + (yY + (v + yY)) := add_assoc ..
        _ = u + (v + (yY + yY)) := by abel
        _ = u + (v + 0) := by rw [yAdd_self]
        _ = u + v := by rw [add_zero]

theorem yT_tau {v : Fin 10 → ZMod 2} (hv : v ∈ yT) : v + yY ∈ yT := by
  obtain ⟨hvB, hvN⟩ := hv
  refine ⟨?_, ?_⟩
  · rw [yB_add_left, hvB, yB_self, add_zero]
  · intro n
    rw [map_add, yActN_yY]
    rcases hvN n with h | h
    · left; rw [h]
    · right; rw [h]

theorem yAct_pinnedX_mem_yIso {α : Fin Tag.E7.rank → ℤ}
    (hα : α ∈ yLevelZeroRoots) (t : ZMod 2)
    (hlin : pinnedX .E7 (ZMod 2) α t ∈ linConjSubgroup (ZMod 2) yPsi)
    (v : Fin 10 → ZMod 2) :
    yAct (pinnedX .E7 (ZMod 2) α t) hlin v = yRootStep α t v := by
  apply yAct_eq_of_rootProd_eq
  rw [yAct_spec, conj_rootProd_yPsi (yIsRoot_of_mem_yLevelZeroRoots hα)
    (yLevel_of_mem_yLevelZeroRoots hα).ge t (yDecode v)]
  refine rootProd_congr fun β hβ => ?_
  have hco : yRestrict (conjCoeff α t yPsi (yDecode v)) = yRootStep α t v := by
    rw [yRestrict_conjCoeff, yRestrict_yDecode]
  have := congrFun hco (yIdx β)
  simpa [yRestrict, yDecode, if_pos hβ, yVec_yIdx hβ] using this

theorem yIsoSubgroup_yQ {g : ModGL .E7 (ZMod 2)} (hg : g ∈ yIsoSubgroup)
    (hgl : g ∈ linConjSubgroup (ZMod 2) yPsi) (v : Fin 10 → ZMod 2) :
    yQ (yAct g hgl v) = yQ v := by
  obtain ⟨hgl', hQ⟩ := hg
  exact (show yQ (yAct g hgl v) = yQ (yAct g hgl' v) from rfl).trans (hQ v)

theorem yIsoSubgroup_yB {g : ModGL .E7 (ZMod 2)} (hg : g ∈ yIsoSubgroup)
    (hgl : g ∈ linConjSubgroup (ZMod 2) yPsi)
    (hgY : yAct g hgl yY = yY) (v w : Fin 10 → ZMod 2) :
    yB (yAct g hgl v) (yAct g hgl w) = yB v w := by
  have hQ := yIsoSubgroup_yQ hg hgl
  simp only [yB]
  rw [← yAct_add g hgl v w, hQ, hQ, hQ]

theorem yAct_eq_of_eq {g h : ModGL .E7 (ZMod 2)}
    (hg : g ∈ linConjSubgroup (ZMod 2) yPsi)
    (hh : h ∈ linConjSubgroup (ZMod 2) yPsi) (hgh : g = h) (v : Fin 10 → ZMod 2) :
    yAct g hg v = yAct h hh v := by
  cases hgh
  rfl

theorem yT_step {p : YRootTable} (hp : p ∈ yS0RootData) {v : Fin 10 → ZMod 2}
    (hv : v ∈ yT) : yStepFun p.table 1 v ∈ yT := by
  obtain ⟨hvB, hvN⟩ := hv
  have hpL : p.root ∈ yLevelZeroRoots := yS0Root_mem_levelZero hp
  have hlin : pinnedX .E7 (ZMod 2) p.root 1 ∈ linConjSubgroup (ZMod 2) yPsi :=
    pinnedX_mem_linConjSubgroup yPsi_check.1 (fun _ hβ => isRoot_of_mem_yPsi hβ) yPsi_comm
      (yIsRoot_of_mem_yLevelZeroRoots hpL)
      (conj_hyp_of_yLevel_nonneg (yLevel_of_mem_yLevelZeroRoots hpL).ge) 1
  have hact : yAct (pinnedX .E7 (ZMod 2) p.root 1) hlin v = yStepFun p.table 1 v := by
    rw [yAct_pinnedX_mem_yIso hpL 1 hlin v, yRootStep, yS0RootData_tableOf p hp]
  have hactY : yAct (pinnedX .E7 (ZMod 2) p.root 1) hlin yY = yY := by
    rw [yAct_pinnedX_mem_yIso hpL 1 hlin yY, yRootStep, yS0RootData_tableOf p hp]
    exact yS0RootData_fix p hp
  have hiso : pinnedX .E7 (ZMod 2) p.root 1 ∈ yIsoSubgroup :=
    yPinnedX_mem_yIsoSubgroup hpL 1
  have hsG : pinnedX .E7 (ZMod 2) p.root 1 ∈ adjointGroup .E7 (ZMod 2) :=
    pinnedX_mem_adjointGroup _ _
  set s : adjointGroup .E7 (ZMod 2) := ⟨pinnedX .E7 (ZMod 2) p.root 1, hsG⟩ with hs_def
  have hsval : (s : ModGL .E7 (ZMod 2)) = pinnedX .E7 (ZMod 2) p.root 1 := rfl
  have hcommGL : (s : ModGL .E7 (ZMod 2)) * yAS (ZMod 2) =
      yAS (ZMod 2) * (s : ModGL .E7 (ZMod 2)) := by
    have h := yAct_spec (pinnedX .E7 (ZMod 2) p.root 1) hlin yY
    rw [hactY, yRootProd_yPsi_yCoeff_eq] at h
    calc (s : ModGL .E7 (ZMod 2)) * yAS (ZMod 2)
        = (pinnedX .E7 (ZMod 2) p.root 1 * yAS (ZMod 2) *
            (pinnedX .E7 (ZMod 2) p.root 1)⁻¹) * pinnedX .E7 (ZMod 2) p.root 1 := by
          rw [hsval]; group
      _ = yAS (ZMod 2) * pinnedX .E7 (ZMod 2) p.root 1 := by rw [← h]
      _ = yAS (ZMod 2) * (s : ModGL .E7 (ZMod 2)) := by rw [hsval]
  have hsC : s ∈ centralizer ({e7ASRep (ZMod 2) 1} : Set (adjointGroup .E7 (ZMod 2))) := by
    rw [mem_centralizer_singleton_iff]
    apply Subtype.ext
    simpa only [Subgroup.coe_mul, coe_e7ASRep_one, hsval] using hcommGL
  have hsN : s ∈ Subgroup.normalizer (yN : Set (adjointGroup .E7 (ZMod 2))) :=
    CFSG.LieType.BorelTits.le_normalizer_pCoreOf (r := 2) _ hsC
  refine ⟨?_, ?_⟩
  · rw [← hact]
    calc yB (yAct (pinnedX .E7 (ZMod 2) p.root 1) hlin v) yY
        = yB (yAct (pinnedX .E7 (ZMod 2) p.root 1) hlin v)
            (yAct (pinnedX .E7 (ZMod 2) p.root 1) hlin yY) := by rw [hactY]
      _ = yB v yY := yIsoSubgroup_yB hiso hlin hactY v yY
      _ = 0 := hvB
  · rw [← hact]
    intro n
    have hn'mem : s⁻¹ * (n : adjointGroup .E7 (ZMod 2)) * s ∈ yN := by
      have h := (Subgroup.mem_normalizer_iff.1 (inv_mem hsN)
        (n : adjointGroup .E7 (ZMod 2))).1 n.2
      simpa using h
    set n' : yN := ⟨s⁻¹ * (n : adjointGroup .E7 (ZMod 2)) * s, hn'mem⟩ with hn'_def
    have hn'val : ((n' : yN) : ModGL .E7 (ZMod 2)) =
        ((s⁻¹ * (n : adjointGroup .E7 (ZMod 2)) * s : adjointGroup .E7 (ZMod 2)) :
          ModGL .E7 (ZMod 2)) := rfl
    have hgroup : (n : ModGL .E7 (ZMod 2)) * (s : ModGL .E7 (ZMod 2)) =
        (s : ModGL .E7 (ZMod 2)) * (n' : ModGL .E7 (ZMod 2)) := by
      rw [hn'val]
      simp only [Subgroup.coe_mul, Subgroup.coe_inv]
      group
    have hcomp : yActN n (yAct (pinnedX .E7 (ZMod 2) p.root 1) hlin v) =
        yAct (pinnedX .E7 (ZMod 2) p.root 1) hlin (yActN n' v) := by
      calc yActN n (yAct (pinnedX .E7 (ZMod 2) p.root 1) hlin v)
          = yAct ((n : ModGL .E7 (ZMod 2)) * (s : ModGL .E7 (ZMod 2)))
              (mul_mem (yN_mem_linConj n) hlin) v := by
            rw [yActN_apply]
            exact (yAct_mul (n : ModGL .E7 (ZMod 2)) (s : ModGL .E7 (ZMod 2))
              (yN_mem_linConj n) hlin v).symm
        _ = yAct ((s : ModGL .E7 (ZMod 2)) * (n' : ModGL .E7 (ZMod 2)))
              (mul_mem hlin (yN_mem_linConj n')) v :=
            yAct_eq_of_eq _ _ hgroup v
        _ = yAct (pinnedX .E7 (ZMod 2) p.root 1) hlin
              (yAct (n' : ModGL .E7 (ZMod 2)) (yN_mem_linConj n') v) := by
            exact yAct_mul (s : ModGL .E7 (ZMod 2)) (n' : ModGL .E7 (ZMod 2))
              hlin (yN_mem_linConj n') v
        _ = yAct (pinnedX .E7 (ZMod 2) p.root 1) hlin (yActN n' v) := rfl
    rw [hcomp]
    rcases hvN n' with h | h
    · left; rw [h]
    · right; rw [h, yAct_add, hactY]

theorem yT_gen (i : Fin 27) {v : Fin 10 → ZMod 2} (hv : v ∈ yT) :
    yGenFun (yGenAt i) v ∈ yT := by
  rcases yGenAt_cases i with ⟨p, hp, hpe⟩ | hpe
  · rw [hpe]
    exact yT_step hp hv
  · rw [hpe]
    exact yT_tau hv

theorem yPerp_subset_of_closed {T : Set (Fin 10 → ZMod 2)}
    (hadd : ∀ u ∈ T, ∀ v ∈ T, u + v ∈ T)
    (hgen : ∀ i : Fin 27, ∀ v ∈ T, yGenFun (yGenAt i) v ∈ T)
    {w : Fin 10 → ZMod 2} (hwB : yB w yY = 0) (hw0 : w ≠ 0) (hwy : w ≠ yY)
    (hwT : w ∈ T) :
    ∀ v, yB v yY = 0 → v ∈ T := by
  have h0 : (0 : Fin 10 → ZMod 2) ∈ T := by
    have := hadd w hwT w hwT
    rwa [yAdd_self] at this
  have hbB : yB (yOf2 (yTo2 w)) yY = 0 := by rwa [yOf2_yTo2]
  have hb0 : yOf2 (yTo2 w) ≠ 0 := by rwa [yOf2_yTo2]
  have hby : yOf2 (yTo2 w) ≠ yY := by rwa [yOf2_yTo2]
  have hbase : yBase0 ∈ T ∨ yBase1 ∈ T := by
    rcases yReach_flag (yTo2 w) hbB hb0 hby with hf | hf
    · left
      have hword := yReach_check0 (yTo2 w) hbB hb0 hby hf
      rw [yOf2_yTo2] at hword
      rw [← hword]
      exact yApply_mem_of_closed (fun i v hv => hgen i v hv) _ hwT
    · right
      have hword := yReach_check1 (yTo2 w) hbB hb0 hby hf
      rw [yOf2_yTo2] at hword
      rw [← hword]
      exact yApply_mem_of_closed (fun i v hv => hgen i v hv) _ hwT
  intro v hv
  rcases hbase with hb | hb
  · have hL : ∀ x ∈ ySpanVecs0, x ∈ T := by
      intro x hx
      obtain ⟨word, -, rfl⟩ := List.mem_map.1 hx
      exact yApply_mem_of_closed (fun i v hv => hgen i v hv) word hb
    have hspan := ySpan0_check (yTo2 v) (by rwa [yOf2_yTo2])
    rw [yOf2_yTo2] at hspan
    rw [hspan]
    exact ySubsetSum_mem_of_closed h0 hadd hL (yMaskOf0 (yTo2 v))
  · have hL : ∀ x ∈ ySpanVecs1, x ∈ T := by
      intro x hx
      obtain ⟨word, -, rfl⟩ := List.mem_map.1 hx
      exact yApply_mem_of_closed (fun i v hv => hgen i v hv) word hb
    have hspan := ySpan1_check (yTo2 v) (by rwa [yOf2_yTo2])
    rw [yOf2_yTo2] at hspan
    rw [hspan]
    exact ySubsetSum_mem_of_closed h0 hadd hL (yMaskOf1 (yTo2 v))

theorem yPerp_subset_yT : ∀ v : Fin 10 → ZMod 2, yB v yY = 0 → v ∈ yT := by
  obtain ⟨w, hwB, hw0, hwy, hwN⟩ := yN_fixed_w
  exact yPerp_subset_of_closed (fun u hu v hv => yT_add u v hu hv) yT_gen hwB hw0 hwy
    ⟨hwB, hwN⟩

theorem yActN_on_yPerp (n : yN) {w : Fin 10 → ZMod 2} (hw : yB w yY = 0) :
    yActN n w = w ∨ yActN n w = w + yY :=
  (yPerp_subset_yT w hw).2 n

theorem yAdd_self_zmod2 (a : ZMod 2) : a + a = 0 := by
  rw [← two_smul (ZMod 2) a]
  have h2 : (2 : ZMod 2) = 0 := by decide
  rw [h2, zero_smul]

theorem yQ_add_yY {w : Fin 10 → ZMod 2} (hw : yB w yY = 0) :
    yQ (w + yY) = yQ w + 1 := by
  rw [yQ_add, yQ_yY, ← yB_eq_polarFun w yY, hw, add_zero]

theorem yActN_eq_id_or_tau (n : yN) :
    (∀ v, yActN n v = v) ∨ (∀ v, yActN n v = v + yB v yY • yY) := by
  have hfix : ∀ w, yB w yY = 0 → yActN n w = w := by
    intro w hw
    rcases yActN_on_yPerp n hw with h | h
    · exact h
    · exfalso
      have hQ := yActN_yQ n w
      rw [h, yQ_add_yY hw] at hQ
      have h1 : (yQ w + 1 : ZMod 2) = yQ w + 0 := by rw [add_zero]; exact hQ
      exact one_ne_zero (add_left_cancel h1)
  have hv0 : yB (Pi.single (0 : Fin 10) (1 : ZMod 2)) yY = 1 := by
    rw [yB_yY]; simp
  set v0 : Fin 10 → ZMod 2 := Pi.single (0 : Fin 10) (1 : ZMod 2) with hv0def
  set u : Fin 10 → ZMod 2 := yActN n v0 + v0 with hudef
  have hu : u = 0 ∨ u = yY := by
    apply yPerp_dual_check
    intro k
    have hb : yB (yPerpBasis k) yY = 0 := yPerpBasis_mem k
    have hw := hfix (yPerpBasis k) hb
    calc yB u (yPerpBasis k)
        = yB (yActN n v0) (yPerpBasis k) + yB v0 (yPerpBasis k) := yB_add_left _ _ _
      _ = yB (yActN n v0) (yActN n (yPerpBasis k)) + yB v0 (yPerpBasis k) := by rw [hw]
      _ = yB v0 (yPerpBasis k) + yB v0 (yPerpBasis k) := by rw [yActN_yB]
      _ = 0 := yAdd_self_zmod2 _
  have hv0u : yActN n v0 = v0 + u := yEq_of_add_eq rfl
  have hdecomp : ∀ v : Fin 10 → ZMod 2,
      v = (v + (yB v yY) • v0) + (yB v yY) • v0 := by
    intro v
    rw [add_assoc, ← add_smul, yAdd_self_zmod2, zero_smul, add_zero]
  have hwc : ∀ v : Fin 10 → ZMod 2, yB (v + (yB v yY) • v0) yY = 0 := by
    intro v
    rw [yB_add_left, yB_smul_left, hv0]
    have hc : (yB v yY) • (1 : ZMod 2) = yB v yY := by simp
    rw [hc]
    exact yAdd_self_zmod2 _
  rcases hu with hu0 | huy
  · left
    intro v
    conv_lhs => rw [hdecomp v]
    rw [map_add, hfix _ (hwc v), map_smul, hv0u, hu0, add_zero]
    exact (hdecomp v).symm
  · right
    intro v
    conv_lhs => rw [hdecomp v]
    rw [map_add, hfix _ (hwc v), map_smul, hv0u, huy, smul_add]
    have ha : (yB v yY) • v0 + (yB v yY) • v0 = 0 := by
      rw [← add_smul, yAdd_self_zmod2, zero_smul]
    calc (v + (yB v yY) • v0) + ((yB v yY) • v0 + (yB v yY) • yY)
        = v + (((yB v yY) • v0 + (yB v yY) • v0) + (yB v yY) • yY) := by abel
      _ = v + (yB v yY) • yY := by rw [ha, zero_add]

theorem yDecode_add_smul_yY (v : Fin 10 → ZMod 2) (c : ZMod 2) :
    yDecode (v + c • yY) = yDecode v + c • yDecode yY := by
  funext β
  by_cases hβ : β ∈ yPsi
  · simp only [yDecode, if_pos hβ, Pi.add_apply, Pi.smul_apply]
  · simp only [yDecode, if_neg hβ, Pi.add_apply, Pi.smul_apply, smul_zero, add_zero]

theorem pCoreOf_centralizer_e7ASRep_one_conj_mem (g : adjointGroup .E7 (ZMod 2))
    (hg : g ∈ CFSG.Open.pCoreOf 2
      (centralizer ({e7ASRep (ZMod 2) 1} : Set (adjointGroup .E7 (ZMod 2)))))
    (c : (Fin Tag.E7.rank → ℤ) → ZMod 2) :
    (g : ModGL .E7 (ZMod 2)) * rootProd .E7 (ZMod 2) yPsi c * (g : ModGL .E7 (ZMod 2))⁻¹ =
        rootProd .E7 (ZMod 2) yPsi c ∨
      (g : ModGL .E7 (ZMod 2)) * rootProd .E7 (ZMod 2) yPsi c * (g : ModGL .E7 (ZMod 2))⁻¹ =
        rootProd .E7 (ZMod 2) yPsi c * yAS (ZMod 2) := by
  set n : yN := ⟨g, hg⟩ with hn_def
  have hgl : (g : ModGL .E7 (ZMod 2)) ∈ linConjSubgroup (ZMod 2) yPsi := yN_mem_linConj n
  have hspec := yAct_spec (g : ModGL .E7 (ZMod 2)) hgl (yRestrict c)
  have hv : rootProd .E7 (ZMod 2) yPsi (yDecode (yRestrict c)) =
      rootProd .E7 (ZMod 2) yPsi c := yRootProd_eq_of_yRestrict_eq (by rw [yRestrict_yDecode])
  rw [hv] at hspec
  rcases yActN_eq_id_or_tau n with hid | htau
  · left
    rw [← hspec]
    change rootProd .E7 (ZMod 2) yPsi (yDecode (yActN n (yRestrict c))) =
      rootProd .E7 (ZMod 2) yPsi c
    rw [hid]
    exact hv
  · have hacteq : yAct (g : ModGL .E7 (ZMod 2)) hgl (yRestrict c) =
        yRestrict c + yB (yRestrict c) yY • yY := by
      have h := htau (yRestrict c)
      rwa [show yActN n (yRestrict c) =
        yAct (g : ModGL .E7 (ZMod 2)) hgl (yRestrict c) from rfl] at h
    rw [← hspec, hacteq]
    rcases (by decide : ∀ t : ZMod 2, t = 0 ∨ t = 1) (yB (yRestrict c) yY) with hd | hd
    · left
      rw [hd, zero_smul, add_zero]
      exact hv
    · right
      rw [yDecode_add_smul_yY (v := yRestrict c) (c := yB (yRestrict c) yY),
        rootProd_add yPsi_comm, hv, hd, one_smul, yRootProd_yPsi_yCoeff_eq]

theorem pCoreOf_centralizer_e7ASRep_one_le_normalizer {V : Subgroup (adjointGroup .E7 (ZMod 2))}
    (hyV : e7ASRep (ZMod 2) 1 ∈ V)
    (hV : ∀ v ∈ V, ∃ c : (Fin Tag.E7.rank → ℤ) → ZMod 2,
      (v : ModGL .E7 (ZMod 2)) = rootProd .E7 (ZMod 2) yPsi c) :
    CFSG.Open.pCoreOf 2
        (centralizer ({e7ASRep (ZMod 2) 1} : Set (adjointGroup .E7 (ZMod 2)))) ≤
      Subgroup.normalizer (V : Set (adjointGroup .E7 (ZMod 2))) := by
  have hstep : ∀ (x : adjointGroup .E7 (ZMod 2)), x ∈ yN →
      ∀ v : adjointGroup .E7 (ZMod 2), v ∈ V → x * v * x⁻¹ ∈ V := by
    intro x hx v hv
    obtain ⟨c, hc⟩ := hV v hv
    have h := pCoreOf_centralizer_e7ASRep_one_conj_mem x hx c
    have hcast : ((x * v * x⁻¹ : adjointGroup .E7 (ZMod 2)) : ModGL .E7 (ZMod 2)) =
        (x : ModGL .E7 (ZMod 2)) * (v : ModGL .E7 (ZMod 2)) * (x : ModGL .E7 (ZMod 2))⁻¹ := by
      simp only [Subgroup.coe_mul, Subgroup.coe_inv]
    rcases h with h | h
    · have he : x * v * x⁻¹ = v := Subtype.ext (by rw [hcast, hc, h, ← hc])
      rwa [he]
    · have he : x * v * x⁻¹ = v * e7ASRep (ZMod 2) 1 := by
        apply Subtype.ext
        rw [hcast, hc, h, ← hc]
        simp only [Subgroup.coe_mul, coe_e7ASRep_one]
      rw [he]
      exact mul_mem hv hyV
  intro x hx
  rw [Subgroup.mem_normalizer_iff]
  intro v
  constructor
  · intro hv
    exact hstep x hx v hv
  · intro hv
    have h1 := hstep x⁻¹ (inv_mem hx) (x * v * x⁻¹) hv
    have he : x⁻¹ * (x * v * x⁻¹) * (x⁻¹)⁻¹ = v := by group
    rwa [he] at h1

end Certs2

end CFSG.SeitzReduction.E7Pilot
