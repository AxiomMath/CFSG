module

public import CFSG.LocalAnalysis.SeitzReduction.E6PilotCentralizerZLevi
public import CFSG.LocalAnalysis.SeitzReduction.E7PilotClassYRoots

public section

namespace CFSG.SeitzReduction.E7Pilot

open Subgroup CFSG.Blueprint.Chevalley CFSG.LieType.Chevalley CFSG.LieType.Steinberg.Adjoint
open CFSG.SeitzReduction.E6Pilot (rootProd RootCommFamily conjCoeff)

open CFSG.LieType.Chevalley.RootOps (isRootB isRootB_iff)

local instance e7ClassYCoreChecksNeZeroRank : NeZero Tag.E7.rank := ⟨by decide⟩

theorem yPsi_length : yPsi.length = 10 := rfl

@[expose] def yVec (k : Fin 10) : Fin Tag.E7.rank → ℤ :=
  yPsi.get (Fin.cast yPsi_length.symm k)

@[expose] def yIdx (β : Fin Tag.E7.rank → ℤ) : Fin 10 :=
  Fin.ofNat 10 (yPsi.idxOf β)

@[expose] def yRestrict (c : (Fin Tag.E7.rank → ℤ) → ZMod 2) : Fin 10 → ZMod 2 :=
  fun k => c (yVec k)

@[expose] def yDecode (v : Fin 10 → ZMod 2) : (Fin Tag.E7.rank → ℤ) → ZMod 2 :=
  fun β => if β ∈ yPsi then v (yIdx β) else 0

theorem yVec_mem (k : Fin 10) : yVec k ∈ yPsi := yPsi.get_mem _

theorem yVec_yIdx {β : Fin Tag.E7.rank → ℤ} (hβ : β ∈ yPsi) : yVec (yIdx β) = β := by
  have hlt : yPsi.idxOf β < 10 := by
    rw [← yPsi_length]
    exact List.idxOf_lt_length_iff.2 hβ
  have hcast : Fin.cast yPsi_length.symm (yIdx β) =
      ⟨yPsi.idxOf β, by rw [yPsi_length]; exact hlt⟩ := by
    apply Fin.ext
    simp only [yIdx, Fin.ofNat, Fin.cast, Fin.val_mk, Nat.mod_eq_of_lt hlt]
  calc yVec (yIdx β) = yPsi.get (Fin.cast yPsi_length.symm (yIdx β)) := rfl
    _ = yPsi.get ⟨yPsi.idxOf β, by rw [yPsi_length]; exact hlt⟩ := congrArg yPsi.get hcast
    _ = β := List.idxOf_get (l := yPsi) (a := β) (List.idxOf_lt_length_iff.2 hβ)

theorem yIdx_yVec (k : Fin 10) : yIdx (yVec k) = k := by
  have hlt : yPsi.idxOf (yVec k) < 10 := by
    rw [← yPsi_length]
    exact List.idxOf_lt_length_iff.2 (yVec_mem k)
  apply Fin.ext
  simp only [yIdx, Fin.ofNat, Fin.val_mk, Nat.mod_eq_of_lt hlt]
  have h := List.get_idxOf (l := yPsi) yPsi_check.1 (Fin.cast yPsi_length.symm k)
  simpa [yVec, Fin.cast] using h

theorem yRestrict_yDecode (v : Fin 10 → ZMod 2) : yRestrict (yDecode v) = v := by
  funext k
  simp only [yRestrict, yDecode, yVec_mem, ite_true, yIdx_yVec]

@[expose] def yQ (v : Fin 10 → ZMod 2) : ZMod 2 :=
  v 2 * v 9 + v 3 * v 8 + v 4 * v 7 + v 5 * v 6 + v 0 * v 1

@[expose] def yB (v w : Fin 10 → ZMod 2) : ZMod 2 :=
  yQ (v + w) + yQ v + yQ w

@[expose] def yPolarFun (w v : Fin 10 → ZMod 2) : ZMod 2 :=
  v 2 * w 9 + v 9 * w 2 + v 3 * w 8 + v 8 * w 3 + v 4 * w 7 + v 7 * w 4 +
    v 5 * w 6 + v 6 * w 5 + v 0 * w 1 + v 1 * w 0

@[expose] def yPolar (w : Fin 10 → ZMod 2) : (Fin 10 → ZMod 2) →ₗ[ZMod 2] ZMod 2 where
  toFun := yPolarFun w
  map_add' a b := by
    simp only [yPolarFun, Pi.add_apply]
    ring
  map_smul' a b := by
    simp only [yPolarFun, Pi.smul_apply, smul_eq_mul, RingHom.id_apply]
    ring

theorem yQ_add (v w : Fin 10 → ZMod 2) :
    yQ (v + w) = yQ v + yQ w + yPolarFun w v := by
  simp only [yQ, yPolarFun, Pi.add_apply]
  ring

@[expose] def yY : Fin 10 → ZMod 2 :=
  fun k => if k = 0 ∨ k = 1 then 1 else 0

theorem yB_eq_polarFun (v w : Fin 10 → ZMod 2) : yB v w = yPolarFun w v := by
  simp only [yB, yQ_add]
  have h2 : (2 : ZMod 2) = 0 := by decide
  ring_nf
  simp only [h2, mul_zero, zero_mul, add_zero, zero_add]

theorem yQ_yY : yQ yY = 1 := by
  simp [yQ, yY]

theorem yB_yY : ∀ v : Fin 10 → ZMod 2, yB v yY = v 0 + v 1 := by
  decide +kernel

theorem yB_add_left (u v w : Fin 10 → ZMod 2) : yB (u + v) w = yB u w + yB v w := by
  rw [yB_eq_polarFun, yB_eq_polarFun u, yB_eq_polarFun v]
  exact map_add (yPolar w) u v

theorem yB_smul_left (c : ZMod 2) (v w : Fin 10 → ZMod 2) : yB (c • v) w = c • yB v w := by
  rw [yB_eq_polarFun, yB_eq_polarFun]
  exact map_smul (yPolar w) c v

theorem yB_self : ∀ v : Fin 10 → ZMod 2, yB v v = 0 := by
  decide +kernel

@[expose] def yPerpBasis (k : Fin 9) : Fin 10 → ZMod 2 :=
  if k = 0 then yY else Pi.single ⟨k.val + 1, by have := k.isLt; omega⟩ (1 : ZMod 2)

theorem yPerpBasis_mem (k : Fin 9) : yB (yPerpBasis k) yY = 0 := by
  revert k
  decide +kernel

theorem yPerp_dual_check : ∀ u : Fin 10 → ZMod 2,
    (∀ k : Fin 9, yB u (yPerpBasis k) = 0) → u = 0 ∨ u = yY := by
  decide +kernel

structure YRootTable where
  root : Fin Tag.E7.rank → ℤ
  table : Fin 10 → ℕ

@[expose] def yStepFun (tab : Fin 10 → ℕ) (t : ZMod 2) (v : Fin 10 → ZMod 2) :
    Fin 10 → ZMod 2 :=
  fun k => v k + if tab k < 10 then t * v (Fin.ofNat 10 (tab k)) else 0

theorem yFinOfNat_eq {n : ℕ} (h : n < 10) : (Fin.ofNat 10 n) = ⟨n, h⟩ :=
  Fin.ext (Nat.mod_eq_of_lt h)

@[expose] def yTableOf (α : Fin Tag.E7.rank → ℤ) : Fin 10 → ℕ :=
  fun k => if (yVec k - α ∈ yPsi) ∧ α ≠ yVec k - α then yPsi.idxOf (yVec k - α) % 10 else 10

@[expose] def yRootStep (α : Fin Tag.E7.rank → ℤ) (t : ZMod 2) (v : Fin 10 → ZMod 2) :
    Fin 10 → ZMod 2 :=
  yStepFun (yTableOf α) t v

theorem yVec_idxOf_mod {β : Fin Tag.E7.rank → ℤ} (hβ : β ∈ yPsi) :
    yVec ⟨yPsi.idxOf β % 10, Nat.mod_lt _ (by decide)⟩ = β := by
  have h : (⟨yPsi.idxOf β % 10, Nat.mod_lt _ (by decide)⟩ : Fin 10) = yIdx β := by
    apply Fin.ext
    rfl
  rw [h]
  exact yVec_yIdx hβ

section CertAux

theorem yRestrict_conjCoeff (α : Fin Tag.E7.rank → ℤ) (t : ZMod 2)
    (c : (Fin Tag.E7.rank → ℤ) → ZMod 2) :
    yRestrict (conjCoeff α t yPsi c) = yRootStep α t (yRestrict c) := by
  funext k
  rw [yRestrict,
    E6Pilot.conjCoeff_apply yPsi_check.1 (fun _ hβ => isRoot_of_mem_yPsi hβ) α t c
      (yVec_mem k)]
  unfold yRootStep yStepFun yTableOf
  by_cases h : (yVec k - α ∈ yPsi) ∧ α ≠ yVec k - α
  · obtain ⟨h1, h2⟩ := h
    have hlt : yPsi.idxOf (yVec k - α) % 10 < 10 := Nat.mod_lt _ (by decide)
    have hcond : (True ∧ α ≠ yVec k - α) = True := by simp [h2]
    simp only [h1, hcond, if_true, ite_true, yRestrict, hlt, if_pos]
    rw [yFinOfNat_eq hlt, yVec_idxOf_mod h1]
  · simp [h, yRestrict]

end CertAux

@[expose] def yLevelRootData : List YRootTable := [
  ⟨![1, 0, 0, 0, 0, 0, 0], ![10, 10, 10, 2, 10, 10, 10, 10, 10, 8]⟩,
  ⟨![0, 1, 0, 0, 0, 0, 0], ![10, 5, 10, 10, 10, 10, 0, 10, 10, 10]⟩,
  ⟨![0, 0, 1, 0, 0, 0, 0], ![10, 10, 10, 10, 3, 10, 10, 10, 7, 10]⟩,
  ⟨![0, 0, 0, 1, 0, 0, 0], ![10, 10, 10, 10, 10, 4, 10, 6, 10, 10]⟩,
  ⟨![0, 0, 0, 0, 1, 0, 0], ![5, 10, 10, 10, 10, 10, 1, 10, 10, 10]⟩,
  ⟨![0, 0, 0, 0, 0, 0, 1], ![10, 10, 10, 10, 10, 10, 10, 10, 10, 10]⟩,
  ⟨![-1, 0, 0, 0, 0, 0, 0], ![10, 10, 3, 10, 10, 10, 10, 10, 9, 10]⟩,
  ⟨![1, 0, 1, 0, 0, 0, 0], ![10, 10, 10, 10, 2, 10, 10, 10, 10, 7]⟩,
  ⟨![0, -1, 0, 0, 0, 0, 0], ![6, 10, 10, 10, 10, 1, 10, 10, 10, 10]⟩,
  ⟨![0, 1, 0, 1, 0, 0, 0], ![10, 4, 10, 10, 10, 10, 10, 0, 10, 10]⟩,
  ⟨![0, 0, -1, 0, 0, 0, 0], ![10, 10, 10, 4, 10, 10, 10, 8, 10, 10]⟩,
  ⟨![0, 0, 1, 1, 0, 0, 0], ![10, 10, 10, 10, 10, 3, 10, 10, 6, 10]⟩,
  ⟨![0, 0, 0, -1, 0, 0, 0], ![10, 10, 10, 10, 5, 10, 7, 10, 10, 10]⟩,
  ⟨![0, 0, 0, 1, 1, 0, 0], ![4, 10, 10, 10, 10, 10, 10, 1, 10, 10]⟩,
  ⟨![0, 0, 0, 0, -1, 0, 0], ![10, 6, 10, 10, 10, 0, 10, 10, 10, 10]⟩,
  ⟨![0, 0, 0, 0, 0, 0, -1], ![10, 10, 10, 10, 10, 10, 10, 10, 10, 10]⟩,
  ⟨![-1, 0, -1, 0, 0, 0, 0], ![10, 10, 4, 10, 10, 10, 10, 9, 10, 10]⟩,
  ⟨![1, 0, 1, 1, 0, 0, 0], ![10, 10, 10, 10, 10, 2, 10, 10, 10, 6]⟩,
  ⟨![0, -1, 0, -1, 0, 0, 0], ![7, 10, 10, 10, 1, 10, 10, 10, 10, 10]⟩,
  ⟨![0, 1, 1, 1, 0, 0, 0], ![10, 3, 10, 10, 10, 10, 10, 10, 0, 10]⟩,
  ⟨![0, 1, 0, 1, 1, 0, 0], ![10, 10, 10, 10, 10, 10, 4, 5, 10, 10]⟩,
  ⟨![0, 0, -1, -1, 0, 0, 0], ![10, 10, 10, 5, 10, 10, 8, 10, 10, 10]⟩,
  ⟨![0, 0, 1, 1, 1, 0, 0], ![3, 10, 10, 10, 10, 10, 10, 10, 1, 10]⟩,
  ⟨![0, 0, 0, -1, -1, 0, 0], ![10, 7, 10, 10, 0, 10, 10, 10, 10, 10]⟩,
  ⟨![-1, 0, -1, -1, 0, 0, 0], ![10, 10, 5, 10, 10, 10, 9, 10, 10, 10]⟩,
  ⟨![1, 1, 1, 1, 0, 0, 0], ![10, 2, 10, 10, 10, 10, 10, 10, 10, 0]⟩,
  ⟨![1, 0, 1, 1, 1, 0, 0], ![2, 10, 10, 10, 10, 10, 10, 10, 10, 1]⟩,
  ⟨![0, -1, -1, -1, 0, 0, 0], ![8, 10, 10, 1, 10, 10, 10, 10, 10, 10]⟩,
  ⟨![0, -1, 0, -1, -1, 0, 0], ![10, 10, 10, 10, 6, 7, 10, 10, 10, 10]⟩,
  ⟨![0, 1, 1, 1, 1, 0, 0], ![10, 10, 10, 10, 10, 10, 3, 10, 5, 10]⟩,
  ⟨![0, 0, -1, -1, -1, 0, 0], ![10, 8, 10, 0, 10, 10, 10, 10, 10, 10]⟩,
  ⟨![-1, -1, -1, -1, 0, 0, 0], ![9, 10, 1, 10, 10, 10, 10, 10, 10, 10]⟩,
  ⟨![-1, 0, -1, -1, -1, 0, 0], ![10, 9, 0, 10, 10, 10, 10, 10, 10, 10]⟩,
  ⟨![1, 1, 1, 1, 1, 0, 0], ![10, 10, 10, 10, 10, 10, 2, 10, 10, 5]⟩,
  ⟨![0, -1, -1, -1, -1, 0, 0], ![10, 10, 10, 6, 10, 8, 10, 10, 10, 10]⟩,
  ⟨![0, 1, 1, 2, 1, 0, 0], ![10, 10, 10, 10, 10, 10, 10, 3, 4, 10]⟩,
  ⟨![-1, -1, -1, -1, -1, 0, 0], ![10, 10, 6, 10, 10, 9, 10, 10, 10, 10]⟩,
  ⟨![1, 1, 1, 2, 1, 0, 0], ![10, 10, 10, 10, 10, 10, 10, 2, 10, 4]⟩,
  ⟨![0, -1, -1, -2, -1, 0, 0], ![10, 10, 10, 7, 8, 10, 10, 10, 10, 10]⟩,
  ⟨![-1, -1, -1, -2, -1, 0, 0], ![10, 10, 7, 10, 9, 10, 10, 10, 10, 10]⟩,
  ⟨![1, 1, 2, 2, 1, 0, 0], ![10, 10, 10, 10, 10, 10, 10, 10, 2, 3]⟩,
  ⟨![-1, -1, -2, -2, -1, 0, 0], ![10, 10, 8, 9, 10, 10, 10, 10, 10, 10]⟩]

@[expose] def yS0RootData : List YRootTable := [
  ⟨![1, 0, 0, 0, 0, 0, 0], ![10, 10, 10, 2, 10, 10, 10, 10, 10, 8]⟩,
  ⟨![0, 0, 1, 0, 0, 0, 0], ![10, 10, 10, 10, 3, 10, 10, 10, 7, 10]⟩,
  ⟨![0, 0, 0, 1, 0, 0, 0], ![10, 10, 10, 10, 10, 4, 10, 6, 10, 10]⟩,
  ⟨![0, 0, 0, 0, 0, 0, 1], ![10, 10, 10, 10, 10, 10, 10, 10, 10, 10]⟩,
  ⟨![-1, 0, 0, 0, 0, 0, 0], ![10, 10, 3, 10, 10, 10, 10, 10, 9, 10]⟩,
  ⟨![1, 0, 1, 0, 0, 0, 0], ![10, 10, 10, 10, 2, 10, 10, 10, 10, 7]⟩,
  ⟨![0, 0, -1, 0, 0, 0, 0], ![10, 10, 10, 4, 10, 10, 10, 8, 10, 10]⟩,
  ⟨![0, 0, 1, 1, 0, 0, 0], ![10, 10, 10, 10, 10, 3, 10, 10, 6, 10]⟩,
  ⟨![0, 0, 0, -1, 0, 0, 0], ![10, 10, 10, 10, 5, 10, 7, 10, 10, 10]⟩,
  ⟨![0, 0, 0, 0, 0, 0, -1], ![10, 10, 10, 10, 10, 10, 10, 10, 10, 10]⟩,
  ⟨![-1, 0, -1, 0, 0, 0, 0], ![10, 10, 4, 10, 10, 10, 10, 9, 10, 10]⟩,
  ⟨![1, 0, 1, 1, 0, 0, 0], ![10, 10, 10, 10, 10, 2, 10, 10, 10, 6]⟩,
  ⟨![0, 1, 0, 1, 1, 0, 0], ![10, 10, 10, 10, 10, 10, 4, 5, 10, 10]⟩,
  ⟨![0, 0, -1, -1, 0, 0, 0], ![10, 10, 10, 5, 10, 10, 8, 10, 10, 10]⟩,
  ⟨![-1, 0, -1, -1, 0, 0, 0], ![10, 10, 5, 10, 10, 10, 9, 10, 10, 10]⟩,
  ⟨![0, -1, 0, -1, -1, 0, 0], ![10, 10, 10, 10, 6, 7, 10, 10, 10, 10]⟩,
  ⟨![0, 1, 1, 1, 1, 0, 0], ![10, 10, 10, 10, 10, 10, 3, 10, 5, 10]⟩,
  ⟨![1, 1, 1, 1, 1, 0, 0], ![10, 10, 10, 10, 10, 10, 2, 10, 10, 5]⟩,
  ⟨![0, -1, -1, -1, -1, 0, 0], ![10, 10, 10, 6, 10, 8, 10, 10, 10, 10]⟩,
  ⟨![0, 1, 1, 2, 1, 0, 0], ![10, 10, 10, 10, 10, 10, 10, 3, 4, 10]⟩,
  ⟨![-1, -1, -1, -1, -1, 0, 0], ![10, 10, 6, 10, 10, 9, 10, 10, 10, 10]⟩,
  ⟨![1, 1, 1, 2, 1, 0, 0], ![10, 10, 10, 10, 10, 10, 10, 2, 10, 4]⟩,
  ⟨![0, -1, -1, -2, -1, 0, 0], ![10, 10, 10, 7, 8, 10, 10, 10, 10, 10]⟩,
  ⟨![-1, -1, -1, -2, -1, 0, 0], ![10, 10, 7, 10, 9, 10, 10, 10, 10, 10]⟩,
  ⟨![1, 1, 2, 2, 1, 0, 0], ![10, 10, 10, 10, 10, 10, 10, 10, 2, 3]⟩,
  ⟨![-1, -1, -2, -2, -1, 0, 0], ![10, 10, 8, 9, 10, 10, 10, 10, 10, 10]⟩]

@[expose] def yLevelZeroRoots : List (Fin Tag.E7.rank → ℤ) :=
  yLevelRootData.map YRootTable.root

@[expose] def yS0Roots : List (Fin Tag.E7.rank → ℤ) :=
  yS0RootData.map YRootTable.root

theorem yTableOf_rootData : ∀ p ∈ yLevelRootData, yTableOf p.root = p.table := by
  decide +kernel

theorem yLevelRootData_qcheck :
    ∀ p ∈ yLevelRootData, ∀ t : ZMod 2, ∀ v : Fin 10 → ZMod 2,
      yQ (yStepFun p.table t v) = yQ v := by
  decide +kernel

theorem yLevelZeroRoots_qcheck :
    ∀ α ∈ yLevelZeroRoots, ∀ t : ZMod 2, ∀ v : Fin 10 → ZMod 2,
      yQ (yRootStep α t v) = yQ v := by
  intro α hα t v
  obtain ⟨p, hp, rfl⟩ := List.mem_map.1 hα
  rw [yRootStep, yTableOf_rootData p hp]
  exact yLevelRootData_qcheck p hp t v

theorem yS0RootData_fix : ∀ p ∈ yS0RootData, yStepFun p.table 1 yY = yY := by
  decide +kernel

theorem yLevelRootData_isRoot : ∀ p ∈ yLevelRootData, isRootB .E7 p.root = true := by
  decide +kernel

theorem yLevelRootData_level : ∀ p ∈ yLevelRootData, yLevel p.root = 0 := by
  decide +kernel

theorem yIsRoot_of_mem_yLevelZeroRoots
    {α : Fin Tag.E7.rank → ℤ}
    (hα : α ∈ yLevelZeroRoots) : IsRoot .E7 α := by
  obtain ⟨p, hp, rfl⟩ := List.mem_map.1 hα
  exact isRootB_iff.1 (yLevelRootData_isRoot p hp)

theorem yLevel_of_mem_yLevelZeroRoots {α : Fin Tag.E7.rank → ℤ}
    (hα : α ∈ yLevelZeroRoots) : yLevel α = 0 := by
  obtain ⟨p, hp, rfl⟩ := List.mem_map.1 hα
  exact yLevelRootData_level p hp

theorem ySingle_mem_levelZero : ∀ j : Fin Tag.E7.rank, j ≠ 5 →
    (Pi.single j (1 : ℤ) : Fin Tag.E7.rank → ℤ) ∈ yLevelZeroRoots ∧
      (-Pi.single j (1 : ℤ) : Fin Tag.E7.rank → ℤ) ∈ yLevelZeroRoots := by
  decide +kernel

theorem yS0RootData_tableOf : ∀ p ∈ yS0RootData, yTableOf p.root = p.table := by
  decide +kernel

abbrev yGen : Type := Option (Fin 10 → ℕ)

@[expose] def yGenFun (g : yGen) : (Fin 10 → ZMod 2) → Fin 10 → ZMod 2 :=
  match g with
  | none => fun v => v + yY
  | some tab => yStepFun tab 1

theorem yS0RootData_length : yS0RootData.length = 26 := rfl

@[expose] def yGens : List yGen := yS0RootData.map (fun p => some p.table) ++ [none]

theorem yGens_length : yGens.length = 27 := by
  simp only [yGens, List.length_append, List.length_map, yS0RootData_length,
    List.length_singleton]

@[expose] def yGenAt (i : Fin 27) : yGen :=
  yGens.get (Fin.cast yGens_length.symm i)

theorem yGenAt_mem (i : Fin 27) : yGenAt i ∈ yGens := List.get_mem _ _

theorem yGenAt_cases (i : Fin 27) :
    (∃ p ∈ yS0RootData, yGenAt i = some p.table) ∨ yGenAt i = none := by
  have h := yGenAt_mem i
  rw [yGens] at h
  rcases List.mem_append.1 h with h | h
  · obtain ⟨p, hp, hpe⟩ := List.mem_map.1 h
    exact Or.inl ⟨p, hp, hpe.symm⟩
  · rw [List.mem_singleton] at h
    exact Or.inr h

@[expose] def yApply (word : List (Fin 27)) (v : Fin 10 → ZMod 2) : Fin 10 → ZMod 2 :=
  word.foldl (fun v i => yGenFun (yGenAt i) v) v

theorem yApply_mem_of_closed {T : Set (Fin 10 → ZMod 2)}
    (h : ∀ (i : Fin 27) {v : Fin 10 → ZMod 2}, v ∈ T → yGenFun (yGenAt i) v ∈ T) :
    ∀ (word : List (Fin 27)) {v : Fin 10 → ZMod 2}, v ∈ T → yApply word v ∈ T := by
  intro word
  induction word with
  | nil => intro v hv; exact hv
  | cons i word ih => intro v hv; exact ih (h i hv)

@[expose] def yOf2 (b : Fin 10 → Fin 2) : Fin 10 → ZMod 2 := fun k => ((b k).val : ZMod 2)

@[expose] def yTo2 (v : Fin 10 → ZMod 2) : Fin 10 → Fin 2 :=
  fun k => ⟨(v k).val, ZMod.val_lt (v k)⟩

theorem yOf2_yTo2 (v : Fin 10 → ZMod 2) : yOf2 (yTo2 v) = v := by
  funext k
  exact ZMod.natCast_zmod_val (v k)

@[expose] def yBase0 : Fin 10 → ZMod 2 := ![0, 0, 1, 0, 0, 0, 0, 0, 0, 0]

@[expose] def yBase1 : Fin 10 → ZMod 2 := ![0, 0, 0, 0, 0, 1, 1, 0, 0, 0]

@[expose] def yWordOf (b : Fin 10 → Fin 2) : Bool × List (Fin 27) :=
(if b 0 = 0 then (if b 1 = 0 then (if b 2 = 0 then (if b 3 = 0 then (if b 4 = 0 then (if b 5 =
    0 then (if b 6 = 0 then (if b 7 = 0 then (if b 8 = 0 then (if b 9 = 0 then (true, []) else
    (true, [25,24,4,0])) else (if b 9 = 0 then (true, [25,24]) else (true, [25,24,0]))) else
    (if b 8 = 0 then (if b 9 = 0 then (true, [23,21]) else (true, [23,21,5])) else (if b 9 = 0
    then (true, [23,1,21]) else (true, [25,24,19,0])))) else (if b 7 = 0 then (if b 8 = 0 then
    (if b 9 = 0 then (true, [20,17]) else (true, [20,17,11])) else (if b 9 = 0 then (true,
    [20,7,17]) else (true, [25,24,16,0]))) else (if b 8 = 0 then (if b 9 = 0 then (true,
    [20,2,17]) else (true, [23,21,12,5])) else (if b 9 = 0 then (true, [20,1,2,17]) else (true,
    [25,24,2,16,0]))))) else (if b 6 = 0 then (if b 7 = 0 then (if b 8 = 0 then (if b 9 = 0
    then (true, [14,11]) else (true, [17,14,11])) else (if b 9 = 0 then (true, [16,14,11]) else
    (true, [25,24,7,0]))) else (if b 8 = 0 then (if b 9 = 0 then (true, [14,12,11]) else (true,
    [23,21,2,5])) else (if b 9 = 0 then (true, [14,1,12,11]) else (true, [25,24,12,7,0]))))
    else (if b 7 = 0 then (if b 8 = 0 then (if b 9 = 0 then (false, []) else (false, [11]))
    else (if b 9 = 0 then (false, [7]) else (false, [0,7]))) else (if b 8 = 0 then (if b 9 = 0
    then (false, [2]) else (false, [5,2])) else (if b 9 = 0 then (false, [1,2]) else (false,
    [0,1,2])))))) else (if b 5 = 0 then (if b 6 = 0 then (if b 7 = 0 then (if b 8 = 0 then (if
    b 9 = 0 then (true, [10,5]) else (true, [21,10,5])) else (if b 9 = 0 then (true, [19,10,5])
    else (true, [25,24,1,0]))) else (if b 8 = 0 then (if b 9 = 0 then (false, [2,8,2]) else
    (false, [2,8,5,2])) else (if b 9 = 0 then (false, [2,8,1,2]) else (false, [2,8,0,1,2]))))
    else (if b 7 = 0 then (if b 8 = 0 then (if b 9 = 0 then (true, [12,10,5]) else (true,
    [20,17,2,5])) else (if b 9 = 0 then (true, [7,12,10,5]) else (true, [25,24,12,1,0]))) else
    (if b 8 = 0 then (if b 9 = 0 then (false, [15,2]) else (false, [15,5,2])) else (if b 9 = 0
    then (false, [15,1,2]) else (false, [15,0,1,2]))))) else (if b 6 = 0 then (if b 7 = 0 then
    (if b 8 = 0 then (if b 9 = 0 then (true, [10,2,5]) else (true, [17,10,2,5])) else (if b 9 =
    0 then (true, [16,10,2,5]) else (true, [25,24,2,1,0]))) else (if b 8 = 0 then (if b 9 = 0
    then (false, [8,2]) else (false, [8,5,2])) else (if b 9 = 0 then (false, [8,1,2]) else
    (false, [8,0,1,2])))) else (if b 7 = 0 then (if b 8 = 0 then (if b 9 = 0 then (false, [8])
    else (false, [11,8])) else (if b 9 = 0 then (false, [8,7]) else (false, [8,0,7]))) else (if
    b 8 = 0 then (if b 9 = 0 then (true, [12,10,2,5]) else (true, [10,17,2,5])) else (if b 9 =
    0 then (true, [1,12,10,2,5]) else (true, [10,17,16,2,5]))))))) else (if b 4 = 0 then (if b
    5 = 0 then (if b 6 = 0 then (if b 7 = 0 then (if b 8 = 0 then (if b 9 = 0 then (true,
    [4,0]) else (true, [24,4,0])) else (if b 9 = 0 then (false, [7,13,7]) else (false,
    [7,13,0,7]))) else (if b 8 = 0 then (if b 9 = 0 then (true, [19,4,0]) else (true,
    [23,21,1,0])) else (if b 9 = 0 then (false, [7,13,1,2]) else (false, [7,13,0,1,2])))) else
    (if b 7 = 0 then (if b 8 = 0 then (if b 9 = 0 then (true, [16,4,0]) else (true,
    [11,16,4,0])) else (if b 9 = 0 then (false, [18,7]) else (false, [18,0,7]))) else (if b 8 =
    0 then (if b 9 = 0 then (true, [2,16,4,0]) else (true, [23,21,12,1,0])) else (if b 9 = 0
    then (false, [18,1,2]) else (false, [18,0,1,2]))))) else (if b 6 = 0 then (if b 7 = 0 then
    (if b 8 = 0 then (if b 9 = 0 then (true, [7,4,0]) else (true, [17,7,4,0])) else (if b 9 = 0
    then (false, [13,7]) else (false, [13,0,7]))) else (if b 8 = 0 then (if b 9 = 0 then (true,
    [12,7,4,0]) else (true, [23,21,2,1,0])) else (if b 9 = 0 then (false, [13,1,2]) else
    (false, [13,0,1,2])))) else (if b 7 = 0 then (if b 8 = 0 then (if b 9 = 0 then (false,
    [13]) else (false, [13,11])) else (if b 9 = 0 then (true, [16,7,4,0]) else (true,
    [4,17,7,0]))) else (if b 8 = 0 then (if b 9 = 0 then (false, [13,2]) else (false,
    [13,5,2])) else (if b 9 = 0 then (true, [16,12,7,4,0]) else (true, [4,17,12,7,0])))))) else
    (if b 5 = 0 then (if b 6 = 0 then (if b 7 = 0 then (if b 8 = 0 then (if b 9 = 0 then (true,
    [4,1,0]) else (true, [21,4,1,0])) else (if b 9 = 0 then (false, [2,13,8,7]) else (false,
    [2,13,8,0,7]))) else (if b 8 = 0 then (if b 9 = 0 then (false, [6,2,8,2]) else (false,
    [6,2,8,5,2])) else (if b 9 = 0 then (true, [19,4,1,0]) else (true, [4,21,1,0])))) else (if
    b 7 = 0 then (if b 8 = 0 then (if b 9 = 0 then (true, [12,4,1,0]) else (true,
    [20,17,2,1,0])) else (if b 9 = 0 then (false, [18,8,7]) else (false, [18,8,0,7]))) else (if
    b 8 = 0 then (if b 9 = 0 then (false, [15,13,2]) else (false, [15,13,5,2])) else (if b 9 =
    0 then (true, [19,12,4,1,0]) else (true, [4,21,12,1,0]))))) else (if b 6 = 0 then (if b 7 =
    0 then (if b 8 = 0 then (if b 9 = 0 then (true, [4,2,1,0]) else (true, [17,4,2,1,0])) else
    (if b 9 = 0 then (false, [13,8,7]) else (false, [13,8,0,7]))) else (if b 8 = 0 then (if b 9
    = 0 then (false, [6,8,2]) else (false, [6,8,5,2])) else (if b 9 = 0 then (true,
    [19,4,2,1,0]) else (true, [4,21,2,1,0])))) else (if b 7 = 0 then (if b 8 = 0 then (if b 9 =
    0 then (false, [6,8]) else (false, [11,6,8])) else (if b 9 = 0 then (true, [16,4,2,1,0])
    else (true, [4,17,2,1,0]))) else (if b 8 = 0 then (if b 9 = 0 then (true, [12,4,2,1,0])
    else (true, [10,17,2,1,0])) else (if b 9 = 0 then (false, [22,1,2]) else (false,
    [22,0,1,2])))))))) else (if b 3 = 0 then (if b 4 = 0 then (if b 5 = 0 then (if b 6 = 0 then
    (if b 7 = 0 then (if b 8 = 0 then (if b 9 = 0 then (true, []) else (false, [11,14,11]))
    else (if b 9 = 0 then (true, [24]) else (false, [11,14,0,7]))) else (if b 8 = 0 then (if b
    9 = 0 then (true, [21]) else (false, [11,14,5,2])) else (if b 9 = 0 then (true, [1,21])
    else (false, [11,14,0,1,2])))) else (if b 7 = 0 then (if b 8 = 0 then (if b 9 = 0 then
    (true, [17]) else (false, [20,11])) else (if b 9 = 0 then (true, [7,17]) else (false,
    [20,0,7]))) else (if b 8 = 0 then (if b 9 = 0 then (true, [2,17]) else (false, [20,5,2]))
    else (if b 9 = 0 then (true, [1,2,17]) else (false, [20,0,1,2]))))) else (if b 6 = 0 then
    (if b 7 = 0 then (if b 8 = 0 then (if b 9 = 0 then (true, [11]) else (false, [14,11])) else
    (if b 9 = 0 then (true, [16,11]) else (false, [14,0,7]))) else (if b 8 = 0 then (if b 9 = 0
    then (true, [12,11]) else (false, [14,5,2])) else (if b 9 = 0 then (true, [1,12,11]) else
    (false, [14,0,1,2])))) else (if b 7 = 0 then (if b 8 = 0 then (if b 9 = 0 then (false,
    [14]) else (true, [17,11])) else (if b 9 = 0 then (false, [14,7]) else (true, [17,16,11])))
    else (if b 8 = 0 then (if b 9 = 0 then (false, [14,2]) else (true, [17,12,11])) else (if b
    9 = 0 then (false, [14,1,2]) else (true, [17,1,12,11])))))) else (if b 5 = 0 then (if b 6 =
    0 then (if b 7 = 0 then (if b 8 = 0 then (if b 9 = 0 then (true, [5]) else (false,
    [12,11,10,8])) else (if b 9 = 0 then (true, [19,5]) else (false, [2,14,8,0,7]))) else (if b
    8 = 0 then (if b 9 = 0 then (false, [10,2,8,2]) else (true, [21,5])) else (if b 9 = 0 then
    (false, [10,2,8,1,2]) else (true, [21,19,5])))) else (if b 7 = 0 then (if b 8 = 0 then (if
    b 9 = 0 then (true, [12,5]) else (false, [11,10,8])) else (if b 9 = 0 then (true, [7,12,5])
    else (false, [20,8,0,7]))) else (if b 8 = 0 then (if b 9 = 0 then (false, [15,14,2]) else
    (true, [21,12,5])) else (if b 9 = 0 then (false, [15,14,1,2]) else (true, [21,7,12,5])))))
    else (if b 6 = 0 then (if b 7 = 0 then (if b 8 = 0 then (if b 9 = 0 then (true, [2,5]) else
    (false, [17,10,8])) else (if b 9 = 0 then (true, [16,2,5]) else (false, [14,8,0,7]))) else
    (if b 8 = 0 then (if b 9 = 0 then (false, [10,8,2]) else (true, [21,2,5])) else (if b 9 = 0
    then (false, [10,8,1,2]) else (true, [21,16,2,5])))) else (if b 7 = 0 then (if b 8 = 0 then
    (if b 9 = 0 then (false, [10,8]) else (true, [17,2,5])) else (if b 9 = 0 then (false,
    [10,8,7]) else (true, [17,16,2,5]))) else (if b 8 = 0 then (if b 9 = 0 then (true,
    [12,2,5]) else (false, [23,5,2])) else (if b 9 = 0 then (true, [1,12,2,5]) else (false,
    [23,0,1,2]))))))) else (if b 4 = 0 then (if b 5 = 0 then (if b 6 = 0 then (if b 7 = 0 then
    (if b 8 = 0 then (if b 9 = 0 then (true, [0]) else (false, [7,14,13,11])) else (if b 9 = 0
    then (false, [7,4,13,7]) else (true, [24,0]))) else (if b 8 = 0 then (if b 9 = 0 then
    (true, [19,0]) else (false, [7,14,13,5,2])) else (if b 9 = 0 then (false, [7,4,13,1,2])
    else (true, [24,19,0])))) else (if b 7 = 0 then (if b 8 = 0 then (if b 9 = 0 then (true,
    [16,0]) else (false, [20,13,11])) else (if b 9 = 0 then (false, [18,14,7]) else (true,
    [24,16,0]))) else (if b 8 = 0 then (if b 9 = 0 then (true, [2,16,0]) else (false,
    [20,13,5,2])) else (if b 9 = 0 then (false, [18,14,1,2]) else (true, [24,2,16,0]))))) else
    (if b 6 = 0 then (if b 7 = 0 then (if b 8 = 0 then (if b 9 = 0 then (true, [7,0]) else
    (false, [14,13,11])) else (if b 9 = 0 then (false, [4,13,7]) else (true, [24,7,0]))) else
    (if b 8 = 0 then (if b 9 = 0 then (true, [12,7,0]) else (false, [14,13,5,2])) else (if b 9
    = 0 then (false, [4,13,1,2]) else (true, [24,12,7,0])))) else (if b 7 = 0 then (if b 8 = 0
    then (if b 9 = 0 then (false, [4,13]) else (true, [17,7,0])) else (if b 9 = 0 then (true,
    [16,7,0]) else (false, [25,0,7]))) else (if b 8 = 0 then (if b 9 = 0 then (false, [4,13,2])
    else (true, [17,12,7,0])) else (if b 9 = 0 then (true, [16,12,7,0]) else (false,
    [25,0,1,2])))))) else (if b 5 = 0 then (if b 6 = 0 then (if b 7 = 0 then (if b 8 = 0 then
    (if b 9 = 0 then (true, [1,0]) else (false, [12,11,4,6,8])) else (if b 9 = 0 then (false,
    [2,13,10,8,7]) else (true, [24,1,0]))) else (if b 8 = 0 then (if b 9 = 0 then (false,
    [4,6,2,8,2]) else (true, [21,1,0])) else (if b 9 = 0 then (true, [19,1,0]) else (false,
    [25,2,8,0,1,2])))) else (if b 7 = 0 then (if b 8 = 0 then (if b 9 = 0 then (true, [12,1,0])
    else (false, [11,4,6,8])) else (if b 9 = 0 then (false, [18,10,8,7]) else (true,
    [24,12,1,0]))) else (if b 8 = 0 then (if b 9 = 0 then (false, [15,4,13,2]) else (true,
    [21,12,1,0])) else (if b 9 = 0 then (true, [19,12,1,0]) else (false, [25,15,0,1,2])))))
    else (if b 6 = 0 then (if b 7 = 0 then (if b 8 = 0 then (if b 9 = 0 then (true, [2,1,0])
    else (false, [17,4,6,8])) else (if b 9 = 0 then (false, [13,10,8,7]) else (true,
    [24,2,1,0]))) else (if b 8 = 0 then (if b 9 = 0 then (false, [4,6,8,2]) else (true,
    [21,2,1,0])) else (if b 9 = 0 then (true, [19,2,1,0]) else (false, [25,8,0,1,2])))) else
    (if b 7 = 0 then (if b 8 = 0 then (if b 9 = 0 then (false, [4,6,8]) else (true,
    [17,2,1,0])) else (if b 9 = 0 then (true, [16,2,1,0]) else (false, [25,8,0,7]))) else (if b
    8 = 0 then (if b 9 = 0 then (true, [12,2,1,0]) else (false, [23,13,5,2])) else (if b 9 = 0
    then (false, [22,14,1,2]) else (true, [24,12,2,1,0]))))))))) else (if b 2 = 0 then (if b 3
    = 0 then (if b 4 = 0 then (if b 5 = 0 then (if b 6 = 0 then (if b 7 = 0 then (if b 8 = 0
    then (if b 9 = 0 then (true, []) else (true, [])) else (if b 9 = 0 then (true, []) else
    (true, []))) else (if b 8 = 0 then (if b 9 = 0 then (true, []) else (true, [])) else (if b
    9 = 0 then (true, []) else (true, [])))) else (if b 7 = 0 then (if b 8 = 0 then (if b 9 = 0
    then (true, []) else (true, [])) else (if b 9 = 0 then (true, []) else (true, []))) else
    (if b 8 = 0 then (if b 9 = 0 then (true, []) else (true, [])) else (if b 9 = 0 then (true,
    []) else (true, []))))) else (if b 6 = 0 then (if b 7 = 0 then (if b 8 = 0 then (if b 9 = 0
    then (true, []) else (true, [])) else (if b 9 = 0 then (true, []) else (true, []))) else
    (if b 8 = 0 then (if b 9 = 0 then (true, []) else (true, [])) else (if b 9 = 0 then (true,
    []) else (true, [])))) else (if b 7 = 0 then (if b 8 = 0 then (if b 9 = 0 then (true, [])
    else (true, [])) else (if b 9 = 0 then (true, []) else (true, []))) else (if b 8 = 0 then
    (if b 9 = 0 then (true, []) else (true, [])) else (if b 9 = 0 then (true, []) else (true,
    [])))))) else (if b 5 = 0 then (if b 6 = 0 then (if b 7 = 0 then (if b 8 = 0 then (if b 9 =
    0 then (true, []) else (true, [])) else (if b 9 = 0 then (true, []) else (true, []))) else
    (if b 8 = 0 then (if b 9 = 0 then (true, []) else (true, [])) else (if b 9 = 0 then (true,
    []) else (true, [])))) else (if b 7 = 0 then (if b 8 = 0 then (if b 9 = 0 then (true, [])
    else (true, [])) else (if b 9 = 0 then (true, []) else (true, []))) else (if b 8 = 0 then
    (if b 9 = 0 then (true, []) else (true, [])) else (if b 9 = 0 then (true, []) else (true,
    []))))) else (if b 6 = 0 then (if b 7 = 0 then (if b 8 = 0 then (if b 9 = 0 then (true, [])
    else (true, [])) else (if b 9 = 0 then (true, []) else (true, []))) else (if b 8 = 0 then
    (if b 9 = 0 then (true, []) else (true, [])) else (if b 9 = 0 then (true, []) else (true,
    [])))) else (if b 7 = 0 then (if b 8 = 0 then (if b 9 = 0 then (true, []) else (true, []))
    else (if b 9 = 0 then (true, []) else (true, []))) else (if b 8 = 0 then (if b 9 = 0 then
    (true, []) else (true, [])) else (if b 9 = 0 then (true, []) else (true, []))))))) else (if
    b 4 = 0 then (if b 5 = 0 then (if b 6 = 0 then (if b 7 = 0 then (if b 8 = 0 then (if b 9 =
    0 then (true, []) else (true, [])) else (if b 9 = 0 then (true, []) else (true, []))) else
    (if b 8 = 0 then (if b 9 = 0 then (true, []) else (true, [])) else (if b 9 = 0 then (true,
    []) else (true, [])))) else (if b 7 = 0 then (if b 8 = 0 then (if b 9 = 0 then (true, [])
    else (true, [])) else (if b 9 = 0 then (true, []) else (true, []))) else (if b 8 = 0 then
    (if b 9 = 0 then (true, []) else (true, [])) else (if b 9 = 0 then (true, []) else (true,
    []))))) else (if b 6 = 0 then (if b 7 = 0 then (if b 8 = 0 then (if b 9 = 0 then (true, [])
    else (true, [])) else (if b 9 = 0 then (true, []) else (true, []))) else (if b 8 = 0 then
    (if b 9 = 0 then (true, []) else (true, [])) else (if b 9 = 0 then (true, []) else (true,
    [])))) else (if b 7 = 0 then (if b 8 = 0 then (if b 9 = 0 then (true, []) else (true, []))
    else (if b 9 = 0 then (true, []) else (true, []))) else (if b 8 = 0 then (if b 9 = 0 then
    (true, []) else (true, [])) else (if b 9 = 0 then (true, []) else (true, [])))))) else (if
    b 5 = 0 then (if b 6 = 0 then (if b 7 = 0 then (if b 8 = 0 then (if b 9 = 0 then (true, [])
    else (true, [])) else (if b 9 = 0 then (true, []) else (true, []))) else (if b 8 = 0 then
    (if b 9 = 0 then (true, []) else (true, [])) else (if b 9 = 0 then (true, []) else (true,
    [])))) else (if b 7 = 0 then (if b 8 = 0 then (if b 9 = 0 then (true, []) else (true, []))
    else (if b 9 = 0 then (true, []) else (true, []))) else (if b 8 = 0 then (if b 9 = 0 then
    (true, []) else (true, [])) else (if b 9 = 0 then (true, []) else (true, []))))) else (if b
    6 = 0 then (if b 7 = 0 then (if b 8 = 0 then (if b 9 = 0 then (true, []) else (true, []))
    else (if b 9 = 0 then (true, []) else (true, []))) else (if b 8 = 0 then (if b 9 = 0 then
    (true, []) else (true, [])) else (if b 9 = 0 then (true, []) else (true, [])))) else (if b
    7 = 0 then (if b 8 = 0 then (if b 9 = 0 then (true, []) else (true, [])) else (if b 9 = 0
    then (true, []) else (true, []))) else (if b 8 = 0 then (if b 9 = 0 then (true, []) else
    (true, [])) else (if b 9 = 0 then (true, []) else (true, [])))))))) else (if b 3 = 0 then
    (if b 4 = 0 then (if b 5 = 0 then (if b 6 = 0 then (if b 7 = 0 then (if b 8 = 0 then (if b
    9 = 0 then (true, []) else (true, [])) else (if b 9 = 0 then (true, []) else (true, [])))
    else (if b 8 = 0 then (if b 9 = 0 then (true, []) else (true, [])) else (if b 9 = 0 then
    (true, []) else (true, [])))) else (if b 7 = 0 then (if b 8 = 0 then (if b 9 = 0 then
    (true, []) else (true, [])) else (if b 9 = 0 then (true, []) else (true, []))) else (if b 8
    = 0 then (if b 9 = 0 then (true, []) else (true, [])) else (if b 9 = 0 then (true, []) else
    (true, []))))) else (if b 6 = 0 then (if b 7 = 0 then (if b 8 = 0 then (if b 9 = 0 then
    (true, []) else (true, [])) else (if b 9 = 0 then (true, []) else (true, []))) else (if b 8
    = 0 then (if b 9 = 0 then (true, []) else (true, [])) else (if b 9 = 0 then (true, []) else
    (true, [])))) else (if b 7 = 0 then (if b 8 = 0 then (if b 9 = 0 then (true, []) else
    (true, [])) else (if b 9 = 0 then (true, []) else (true, []))) else (if b 8 = 0 then (if b
    9 = 0 then (true, []) else (true, [])) else (if b 9 = 0 then (true, []) else (true,
    [])))))) else (if b 5 = 0 then (if b 6 = 0 then (if b 7 = 0 then (if b 8 = 0 then (if b 9 =
    0 then (true, []) else (true, [])) else (if b 9 = 0 then (true, []) else (true, []))) else
    (if b 8 = 0 then (if b 9 = 0 then (true, []) else (true, [])) else (if b 9 = 0 then (true,
    []) else (true, [])))) else (if b 7 = 0 then (if b 8 = 0 then (if b 9 = 0 then (true, [])
    else (true, [])) else (if b 9 = 0 then (true, []) else (true, []))) else (if b 8 = 0 then
    (if b 9 = 0 then (true, []) else (true, [])) else (if b 9 = 0 then (true, []) else (true,
    []))))) else (if b 6 = 0 then (if b 7 = 0 then (if b 8 = 0 then (if b 9 = 0 then (true, [])
    else (true, [])) else (if b 9 = 0 then (true, []) else (true, []))) else (if b 8 = 0 then
    (if b 9 = 0 then (true, []) else (true, [])) else (if b 9 = 0 then (true, []) else (true,
    [])))) else (if b 7 = 0 then (if b 8 = 0 then (if b 9 = 0 then (true, []) else (true, []))
    else (if b 9 = 0 then (true, []) else (true, []))) else (if b 8 = 0 then (if b 9 = 0 then
    (true, []) else (true, [])) else (if b 9 = 0 then (true, []) else (true, []))))))) else (if
    b 4 = 0 then (if b 5 = 0 then (if b 6 = 0 then (if b 7 = 0 then (if b 8 = 0 then (if b 9 =
    0 then (true, []) else (true, [])) else (if b 9 = 0 then (true, []) else (true, []))) else
    (if b 8 = 0 then (if b 9 = 0 then (true, []) else (true, [])) else (if b 9 = 0 then (true,
    []) else (true, [])))) else (if b 7 = 0 then (if b 8 = 0 then (if b 9 = 0 then (true, [])
    else (true, [])) else (if b 9 = 0 then (true, []) else (true, []))) else (if b 8 = 0 then
    (if b 9 = 0 then (true, []) else (true, [])) else (if b 9 = 0 then (true, []) else (true,
    []))))) else (if b 6 = 0 then (if b 7 = 0 then (if b 8 = 0 then (if b 9 = 0 then (true, [])
    else (true, [])) else (if b 9 = 0 then (true, []) else (true, []))) else (if b 8 = 0 then
    (if b 9 = 0 then (true, []) else (true, [])) else (if b 9 = 0 then (true, []) else (true,
    [])))) else (if b 7 = 0 then (if b 8 = 0 then (if b 9 = 0 then (true, []) else (true, []))
    else (if b 9 = 0 then (true, []) else (true, []))) else (if b 8 = 0 then (if b 9 = 0 then
    (true, []) else (true, [])) else (if b 9 = 0 then (true, []) else (true, [])))))) else (if
    b 5 = 0 then (if b 6 = 0 then (if b 7 = 0 then (if b 8 = 0 then (if b 9 = 0 then (true, [])
    else (true, [])) else (if b 9 = 0 then (true, []) else (true, []))) else (if b 8 = 0 then
    (if b 9 = 0 then (true, []) else (true, [])) else (if b 9 = 0 then (true, []) else (true,
    [])))) else (if b 7 = 0 then (if b 8 = 0 then (if b 9 = 0 then (true, []) else (true, []))
    else (if b 9 = 0 then (true, []) else (true, []))) else (if b 8 = 0 then (if b 9 = 0 then
    (true, []) else (true, [])) else (if b 9 = 0 then (true, []) else (true, []))))) else (if b
    6 = 0 then (if b 7 = 0 then (if b 8 = 0 then (if b 9 = 0 then (true, []) else (true, []))
    else (if b 9 = 0 then (true, []) else (true, []))) else (if b 8 = 0 then (if b 9 = 0 then
    (true, []) else (true, [])) else (if b 9 = 0 then (true, []) else (true, [])))) else (if b
    7 = 0 then (if b 8 = 0 then (if b 9 = 0 then (true, []) else (true, [])) else (if b 9 = 0
    then (true, []) else (true, []))) else (if b 8 = 0 then (if b 9 = 0 then (true, []) else
    (true, [])) else (if b 9 = 0 then (true, []) else (true, [])))))))))) else (if b 1 = 0 then
    (if b 2 = 0 then (if b 3 = 0 then (if b 4 = 0 then (if b 5 = 0 then (if b 6 = 0 then (if b
    7 = 0 then (if b 8 = 0 then (if b 9 = 0 then (true, []) else (true, [])) else (if b 9 = 0
    then (true, []) else (true, []))) else (if b 8 = 0 then (if b 9 = 0 then (true, []) else
    (true, [])) else (if b 9 = 0 then (true, []) else (true, [])))) else (if b 7 = 0 then (if b
    8 = 0 then (if b 9 = 0 then (true, []) else (true, [])) else (if b 9 = 0 then (true, [])
    else (true, []))) else (if b 8 = 0 then (if b 9 = 0 then (true, []) else (true, [])) else
    (if b 9 = 0 then (true, []) else (true, []))))) else (if b 6 = 0 then (if b 7 = 0 then (if
    b 8 = 0 then (if b 9 = 0 then (true, []) else (true, [])) else (if b 9 = 0 then (true, [])
    else (true, []))) else (if b 8 = 0 then (if b 9 = 0 then (true, []) else (true, [])) else
    (if b 9 = 0 then (true, []) else (true, [])))) else (if b 7 = 0 then (if b 8 = 0 then (if b
    9 = 0 then (true, []) else (true, [])) else (if b 9 = 0 then (true, []) else (true, [])))
    else (if b 8 = 0 then (if b 9 = 0 then (true, []) else (true, [])) else (if b 9 = 0 then
    (true, []) else (true, [])))))) else (if b 5 = 0 then (if b 6 = 0 then (if b 7 = 0 then (if
    b 8 = 0 then (if b 9 = 0 then (true, []) else (true, [])) else (if b 9 = 0 then (true, [])
    else (true, []))) else (if b 8 = 0 then (if b 9 = 0 then (true, []) else (true, [])) else
    (if b 9 = 0 then (true, []) else (true, [])))) else (if b 7 = 0 then (if b 8 = 0 then (if b
    9 = 0 then (true, []) else (true, [])) else (if b 9 = 0 then (true, []) else (true, [])))
    else (if b 8 = 0 then (if b 9 = 0 then (true, []) else (true, [])) else (if b 9 = 0 then
    (true, []) else (true, []))))) else (if b 6 = 0 then (if b 7 = 0 then (if b 8 = 0 then (if
    b 9 = 0 then (true, []) else (true, [])) else (if b 9 = 0 then (true, []) else (true, [])))
    else (if b 8 = 0 then (if b 9 = 0 then (true, []) else (true, [])) else (if b 9 = 0 then
    (true, []) else (true, [])))) else (if b 7 = 0 then (if b 8 = 0 then (if b 9 = 0 then
    (true, []) else (true, [])) else (if b 9 = 0 then (true, []) else (true, []))) else (if b 8
    = 0 then (if b 9 = 0 then (true, []) else (true, [])) else (if b 9 = 0 then (true, []) else
    (true, []))))))) else (if b 4 = 0 then (if b 5 = 0 then (if b 6 = 0 then (if b 7 = 0 then
    (if b 8 = 0 then (if b 9 = 0 then (true, []) else (true, [])) else (if b 9 = 0 then (true,
    []) else (true, []))) else (if b 8 = 0 then (if b 9 = 0 then (true, []) else (true, []))
    else (if b 9 = 0 then (true, []) else (true, [])))) else (if b 7 = 0 then (if b 8 = 0 then
    (if b 9 = 0 then (true, []) else (true, [])) else (if b 9 = 0 then (true, []) else (true,
    []))) else (if b 8 = 0 then (if b 9 = 0 then (true, []) else (true, [])) else (if b 9 = 0
    then (true, []) else (true, []))))) else (if b 6 = 0 then (if b 7 = 0 then (if b 8 = 0 then
    (if b 9 = 0 then (true, []) else (true, [])) else (if b 9 = 0 then (true, []) else (true,
    []))) else (if b 8 = 0 then (if b 9 = 0 then (true, []) else (true, [])) else (if b 9 = 0
    then (true, []) else (true, [])))) else (if b 7 = 0 then (if b 8 = 0 then (if b 9 = 0 then
    (true, []) else (true, [])) else (if b 9 = 0 then (true, []) else (true, []))) else (if b 8
    = 0 then (if b 9 = 0 then (true, []) else (true, [])) else (if b 9 = 0 then (true, []) else
    (true, [])))))) else (if b 5 = 0 then (if b 6 = 0 then (if b 7 = 0 then (if b 8 = 0 then
    (if b 9 = 0 then (true, []) else (true, [])) else (if b 9 = 0 then (true, []) else (true,
    []))) else (if b 8 = 0 then (if b 9 = 0 then (true, []) else (true, [])) else (if b 9 = 0
    then (true, []) else (true, [])))) else (if b 7 = 0 then (if b 8 = 0 then (if b 9 = 0 then
    (true, []) else (true, [])) else (if b 9 = 0 then (true, []) else (true, []))) else (if b 8
    = 0 then (if b 9 = 0 then (true, []) else (true, [])) else (if b 9 = 0 then (true, []) else
    (true, []))))) else (if b 6 = 0 then (if b 7 = 0 then (if b 8 = 0 then (if b 9 = 0 then
    (true, []) else (true, [])) else (if b 9 = 0 then (true, []) else (true, []))) else (if b 8
    = 0 then (if b 9 = 0 then (true, []) else (true, [])) else (if b 9 = 0 then (true, []) else
    (true, [])))) else (if b 7 = 0 then (if b 8 = 0 then (if b 9 = 0 then (true, []) else
    (true, [])) else (if b 9 = 0 then (true, []) else (true, []))) else (if b 8 = 0 then (if b
    9 = 0 then (true, []) else (true, [])) else (if b 9 = 0 then (true, []) else (true,
    [])))))))) else (if b 3 = 0 then (if b 4 = 0 then (if b 5 = 0 then (if b 6 = 0 then (if b 7
    = 0 then (if b 8 = 0 then (if b 9 = 0 then (true, []) else (true, [])) else (if b 9 = 0
    then (true, []) else (true, []))) else (if b 8 = 0 then (if b 9 = 0 then (true, []) else
    (true, [])) else (if b 9 = 0 then (true, []) else (true, [])))) else (if b 7 = 0 then (if b
    8 = 0 then (if b 9 = 0 then (true, []) else (true, [])) else (if b 9 = 0 then (true, [])
    else (true, []))) else (if b 8 = 0 then (if b 9 = 0 then (true, []) else (true, [])) else
    (if b 9 = 0 then (true, []) else (true, []))))) else (if b 6 = 0 then (if b 7 = 0 then (if
    b 8 = 0 then (if b 9 = 0 then (true, []) else (true, [])) else (if b 9 = 0 then (true, [])
    else (true, []))) else (if b 8 = 0 then (if b 9 = 0 then (true, []) else (true, [])) else
    (if b 9 = 0 then (true, []) else (true, [])))) else (if b 7 = 0 then (if b 8 = 0 then (if b
    9 = 0 then (true, []) else (true, [])) else (if b 9 = 0 then (true, []) else (true, [])))
    else (if b 8 = 0 then (if b 9 = 0 then (true, []) else (true, [])) else (if b 9 = 0 then
    (true, []) else (true, [])))))) else (if b 5 = 0 then (if b 6 = 0 then (if b 7 = 0 then (if
    b 8 = 0 then (if b 9 = 0 then (true, []) else (true, [])) else (if b 9 = 0 then (true, [])
    else (true, []))) else (if b 8 = 0 then (if b 9 = 0 then (true, []) else (true, [])) else
    (if b 9 = 0 then (true, []) else (true, [])))) else (if b 7 = 0 then (if b 8 = 0 then (if b
    9 = 0 then (true, []) else (true, [])) else (if b 9 = 0 then (true, []) else (true, [])))
    else (if b 8 = 0 then (if b 9 = 0 then (true, []) else (true, [])) else (if b 9 = 0 then
    (true, []) else (true, []))))) else (if b 6 = 0 then (if b 7 = 0 then (if b 8 = 0 then (if
    b 9 = 0 then (true, []) else (true, [])) else (if b 9 = 0 then (true, []) else (true, [])))
    else (if b 8 = 0 then (if b 9 = 0 then (true, []) else (true, [])) else (if b 9 = 0 then
    (true, []) else (true, [])))) else (if b 7 = 0 then (if b 8 = 0 then (if b 9 = 0 then
    (true, []) else (true, [])) else (if b 9 = 0 then (true, []) else (true, []))) else (if b 8
    = 0 then (if b 9 = 0 then (true, []) else (true, [])) else (if b 9 = 0 then (true, []) else
    (true, []))))))) else (if b 4 = 0 then (if b 5 = 0 then (if b 6 = 0 then (if b 7 = 0 then
    (if b 8 = 0 then (if b 9 = 0 then (true, []) else (true, [])) else (if b 9 = 0 then (true,
    []) else (true, []))) else (if b 8 = 0 then (if b 9 = 0 then (true, []) else (true, []))
    else (if b 9 = 0 then (true, []) else (true, [])))) else (if b 7 = 0 then (if b 8 = 0 then
    (if b 9 = 0 then (true, []) else (true, [])) else (if b 9 = 0 then (true, []) else (true,
    []))) else (if b 8 = 0 then (if b 9 = 0 then (true, []) else (true, [])) else (if b 9 = 0
    then (true, []) else (true, []))))) else (if b 6 = 0 then (if b 7 = 0 then (if b 8 = 0 then
    (if b 9 = 0 then (true, []) else (true, [])) else (if b 9 = 0 then (true, []) else (true,
    []))) else (if b 8 = 0 then (if b 9 = 0 then (true, []) else (true, [])) else (if b 9 = 0
    then (true, []) else (true, [])))) else (if b 7 = 0 then (if b 8 = 0 then (if b 9 = 0 then
    (true, []) else (true, [])) else (if b 9 = 0 then (true, []) else (true, []))) else (if b 8
    = 0 then (if b 9 = 0 then (true, []) else (true, [])) else (if b 9 = 0 then (true, []) else
    (true, [])))))) else (if b 5 = 0 then (if b 6 = 0 then (if b 7 = 0 then (if b 8 = 0 then
    (if b 9 = 0 then (true, []) else (true, [])) else (if b 9 = 0 then (true, []) else (true,
    []))) else (if b 8 = 0 then (if b 9 = 0 then (true, []) else (true, [])) else (if b 9 = 0
    then (true, []) else (true, [])))) else (if b 7 = 0 then (if b 8 = 0 then (if b 9 = 0 then
    (true, []) else (true, [])) else (if b 9 = 0 then (true, []) else (true, []))) else (if b 8
    = 0 then (if b 9 = 0 then (true, []) else (true, [])) else (if b 9 = 0 then (true, []) else
    (true, []))))) else (if b 6 = 0 then (if b 7 = 0 then (if b 8 = 0 then (if b 9 = 0 then
    (true, []) else (true, [])) else (if b 9 = 0 then (true, []) else (true, []))) else (if b 8
    = 0 then (if b 9 = 0 then (true, []) else (true, [])) else (if b 9 = 0 then (true, []) else
    (true, [])))) else (if b 7 = 0 then (if b 8 = 0 then (if b 9 = 0 then (true, []) else
    (true, [])) else (if b 9 = 0 then (true, []) else (true, []))) else (if b 8 = 0 then (if b
    9 = 0 then (true, []) else (true, [])) else (if b 9 = 0 then (true, []) else (true,
    []))))))))) else (if b 2 = 0 then (if b 3 = 0 then (if b 4 = 0 then (if b 5 = 0 then (if b
    6 = 0 then (if b 7 = 0 then (if b 8 = 0 then (if b 9 = 0 then (true, []) else (true,
    [26,25,24,4,0])) else (if b 9 = 0 then (true, [26,25,24]) else (true, [26,25,24,0]))) else
    (if b 8 = 0 then (if b 9 = 0 then (true, [26,23,21]) else (true, [26,23,21,5])) else (if b
    9 = 0 then (true, [26,23,1,21]) else (true, [26,25,24,19,0])))) else (if b 7 = 0 then (if b
    8 = 0 then (if b 9 = 0 then (true, [26,20,17]) else (true, [26,20,17,11])) else (if b 9 = 0
    then (true, [26,20,7,17]) else (true, [26,25,24,16,0]))) else (if b 8 = 0 then (if b 9 = 0
    then (true, [26,20,2,17]) else (true, [26,23,21,12,5])) else (if b 9 = 0 then (true,
    [26,20,1,2,17]) else (true, [26,25,24,2,16,0]))))) else (if b 6 = 0 then (if b 7 = 0 then
    (if b 8 = 0 then (if b 9 = 0 then (true, [26,14,11]) else (true, [26,17,14,11])) else (if b
    9 = 0 then (true, [26,16,14,11]) else (true, [26,25,24,7,0]))) else (if b 8 = 0 then (if b
    9 = 0 then (true, [26,14,12,11]) else (true, [26,23,21,2,5])) else (if b 9 = 0 then (true,
    [26,14,1,12,11]) else (true, [26,25,24,12,7,0])))) else (if b 7 = 0 then (if b 8 = 0 then
    (if b 9 = 0 then (false, [26]) else (false, [26,11])) else (if b 9 = 0 then (false, [26,7])
    else (false, [26,0,7]))) else (if b 8 = 0 then (if b 9 = 0 then (false, [26,2]) else
    (false, [26,5,2])) else (if b 9 = 0 then (false, [26,1,2]) else (false, [26,0,1,2]))))))
    else (if b 5 = 0 then (if b 6 = 0 then (if b 7 = 0 then (if b 8 = 0 then (if b 9 = 0 then
    (true, [26,10,5]) else (true, [26,21,10,5])) else (if b 9 = 0 then (true, [26,19,10,5])
    else (true, [26,25,24,1,0]))) else (if b 8 = 0 then (if b 9 = 0 then (false, [26,2,8,2])
    else (false, [26,2,8,5,2])) else (if b 9 = 0 then (false, [26,2,8,1,2]) else (false,
    [26,2,8,0,1,2])))) else (if b 7 = 0 then (if b 8 = 0 then (if b 9 = 0 then (true,
    [26,12,10,5]) else (true, [26,20,17,2,5])) else (if b 9 = 0 then (true, [26,7,12,10,5])
    else (true, [26,25,24,12,1,0]))) else (if b 8 = 0 then (if b 9 = 0 then (false, [26,15,2])
    else (false, [26,15,5,2])) else (if b 9 = 0 then (false, [26,15,1,2]) else (false,
    [26,15,0,1,2]))))) else (if b 6 = 0 then (if b 7 = 0 then (if b 8 = 0 then (if b 9 = 0 then
    (true, [26,10,2,5]) else (true, [26,17,10,2,5])) else (if b 9 = 0 then (true,
    [26,16,10,2,5]) else (true, [26,25,24,2,1,0]))) else (if b 8 = 0 then (if b 9 = 0 then
    (false, [26,8,2]) else (false, [26,8,5,2])) else (if b 9 = 0 then (false, [26,8,1,2]) else
    (false, [26,8,0,1,2])))) else (if b 7 = 0 then (if b 8 = 0 then (if b 9 = 0 then (false,
    [26,8]) else (false, [26,11,8])) else (if b 9 = 0 then (false, [26,8,7]) else (false,
    [26,8,0,7]))) else (if b 8 = 0 then (if b 9 = 0 then (true, [26,12,10,2,5]) else (true,
    [26,10,17,2,5])) else (if b 9 = 0 then (true, [26,1,12,10,2,5]) else (true,
    [26,10,17,16,2,5]))))))) else (if b 4 = 0 then (if b 5 = 0 then (if b 6 = 0 then (if b 7 =
    0 then (if b 8 = 0 then (if b 9 = 0 then (true, [26,4,0]) else (true, [26,24,4,0])) else
    (if b 9 = 0 then (false, [26,7,13,7]) else (false, [26,7,13,0,7]))) else (if b 8 = 0 then
    (if b 9 = 0 then (true, [26,19,4,0]) else (true, [26,23,21,1,0])) else (if b 9 = 0 then
    (false, [26,7,13,1,2]) else (false, [26,7,13,0,1,2])))) else (if b 7 = 0 then (if b 8 = 0
    then (if b 9 = 0 then (true, [26,16,4,0]) else (true, [26,11,16,4,0])) else (if b 9 = 0
    then (false, [26,18,7]) else (false, [26,18,0,7]))) else (if b 8 = 0 then (if b 9 = 0 then
    (true, [26,2,16,4,0]) else (true, [26,23,21,12,1,0])) else (if b 9 = 0 then (false,
    [26,18,1,2]) else (false, [26,18,0,1,2]))))) else (if b 6 = 0 then (if b 7 = 0 then (if b 8
    = 0 then (if b 9 = 0 then (true, [26,7,4,0]) else (true, [26,17,7,4,0])) else (if b 9 = 0
    then (false, [26,13,7]) else (false, [26,13,0,7]))) else (if b 8 = 0 then (if b 9 = 0 then
    (true, [26,12,7,4,0]) else (true, [26,23,21,2,1,0])) else (if b 9 = 0 then (false,
    [26,13,1,2]) else (false, [26,13,0,1,2])))) else (if b 7 = 0 then (if b 8 = 0 then (if b 9
    = 0 then (false, [26,13]) else (false, [26,13,11])) else (if b 9 = 0 then (true,
    [26,16,7,4,0]) else (true, [26,4,17,7,0]))) else (if b 8 = 0 then (if b 9 = 0 then (false,
    [26,13,2]) else (false, [26,13,5,2])) else (if b 9 = 0 then (true, [26,16,12,7,4,0]) else
    (true, [26,4,17,12,7,0])))))) else (if b 5 = 0 then (if b 6 = 0 then (if b 7 = 0 then (if b
    8 = 0 then (if b 9 = 0 then (true, [26,4,1,0]) else (true, [26,21,4,1,0])) else (if b 9 = 0
    then (false, [26,2,13,8,7]) else (false, [26,2,13,8,0,7]))) else (if b 8 = 0 then (if b 9 =
    0 then (false, [26,6,2,8,2]) else (false, [26,6,2,8,5,2])) else (if b 9 = 0 then (true,
    [26,19,4,1,0]) else (true, [26,4,21,1,0])))) else (if b 7 = 0 then (if b 8 = 0 then (if b 9
    = 0 then (true, [26,12,4,1,0]) else (true, [26,20,17,2,1,0])) else (if b 9 = 0 then (false,
    [26,18,8,7]) else (false, [26,18,8,0,7]))) else (if b 8 = 0 then (if b 9 = 0 then (false,
    [26,15,13,2]) else (false, [26,15,13,5,2])) else (if b 9 = 0 then (true, [26,19,12,4,1,0])
    else (true, [26,4,21,12,1,0]))))) else (if b 6 = 0 then (if b 7 = 0 then (if b 8 = 0 then
    (if b 9 = 0 then (true, [26,4,2,1,0]) else (true, [26,17,4,2,1,0])) else (if b 9 = 0 then
    (false, [26,13,8,7]) else (false, [26,13,8,0,7]))) else (if b 8 = 0 then (if b 9 = 0 then
    (false, [26,6,8,2]) else (false, [26,6,8,5,2])) else (if b 9 = 0 then (true,
    [26,19,4,2,1,0]) else (true, [26,4,21,2,1,0])))) else (if b 7 = 0 then (if b 8 = 0 then (if
    b 9 = 0 then (false, [26,6,8]) else (false, [26,11,6,8])) else (if b 9 = 0 then (true,
    [26,16,4,2,1,0]) else (true, [26,4,17,2,1,0]))) else (if b 8 = 0 then (if b 9 = 0 then
    (true, [26,12,4,2,1,0]) else (true, [26,10,17,2,1,0])) else (if b 9 = 0 then (false,
    [26,22,1,2]) else (false, [26,22,0,1,2])))))))) else (if b 3 = 0 then (if b 4 = 0 then (if
    b 5 = 0 then (if b 6 = 0 then (if b 7 = 0 then (if b 8 = 0 then (if b 9 = 0 then (true,
    [26]) else (false, [26,11,14,11])) else (if b 9 = 0 then (true, [26,24]) else (false,
    [26,11,14,0,7]))) else (if b 8 = 0 then (if b 9 = 0 then (true, [26,21]) else (false,
    [26,11,14,5,2])) else (if b 9 = 0 then (true, [26,1,21]) else (false, [26,11,14,0,1,2]))))
    else (if b 7 = 0 then (if b 8 = 0 then (if b 9 = 0 then (true, [26,17]) else (false,
    [26,20,11])) else (if b 9 = 0 then (true, [26,7,17]) else (false, [26,20,0,7]))) else (if b
    8 = 0 then (if b 9 = 0 then (true, [26,2,17]) else (false, [26,20,5,2])) else (if b 9 = 0
    then (true, [26,1,2,17]) else (false, [26,20,0,1,2]))))) else (if b 6 = 0 then (if b 7 = 0
    then (if b 8 = 0 then (if b 9 = 0 then (true, [26,11]) else (false, [26,14,11])) else (if b
    9 = 0 then (true, [26,16,11]) else (false, [26,14,0,7]))) else (if b 8 = 0 then (if b 9 = 0
    then (true, [26,12,11]) else (false, [26,14,5,2])) else (if b 9 = 0 then (true,
    [26,1,12,11]) else (false, [26,14,0,1,2])))) else (if b 7 = 0 then (if b 8 = 0 then (if b 9
    = 0 then (false, [26,14]) else (true, [26,17,11])) else (if b 9 = 0 then (false, [26,14,7])
    else (true, [26,17,16,11]))) else (if b 8 = 0 then (if b 9 = 0 then (false, [26,14,2]) else
    (true, [26,17,12,11])) else (if b 9 = 0 then (false, [26,14,1,2]) else (true,
    [26,17,1,12,11])))))) else (if b 5 = 0 then (if b 6 = 0 then (if b 7 = 0 then (if b 8 = 0
    then (if b 9 = 0 then (true, [26,5]) else (false, [26,12,11,10,8])) else (if b 9 = 0 then
    (true, [26,19,5]) else (false, [26,2,14,8,0,7]))) else (if b 8 = 0 then (if b 9 = 0 then
    (false, [26,10,2,8,2]) else (true, [26,21,5])) else (if b 9 = 0 then (false,
    [26,10,2,8,1,2]) else (true, [26,21,19,5])))) else (if b 7 = 0 then (if b 8 = 0 then (if b
    9 = 0 then (true, [26,12,5]) else (false, [26,11,10,8])) else (if b 9 = 0 then (true,
    [26,7,12,5]) else (false, [26,20,8,0,7]))) else (if b 8 = 0 then (if b 9 = 0 then (false,
    [26,15,14,2]) else (true, [26,21,12,5])) else (if b 9 = 0 then (false, [26,15,14,1,2]) else
    (true, [26,21,7,12,5]))))) else (if b 6 = 0 then (if b 7 = 0 then (if b 8 = 0 then (if b 9
    = 0 then (true, [26,2,5]) else (false, [26,17,10,8])) else (if b 9 = 0 then (true,
    [26,16,2,5]) else (false, [26,14,8,0,7]))) else (if b 8 = 0 then (if b 9 = 0 then (false,
    [26,10,8,2]) else (true, [26,21,2,5])) else (if b 9 = 0 then (false, [26,10,8,1,2]) else
    (true, [26,21,16,2,5])))) else (if b 7 = 0 then (if b 8 = 0 then (if b 9 = 0 then (false,
    [26,10,8]) else (true, [26,17,2,5])) else (if b 9 = 0 then (false, [26,10,8,7]) else (true,
    [26,17,16,2,5]))) else (if b 8 = 0 then (if b 9 = 0 then (true, [26,12,2,5]) else (false,
    [26,23,5,2])) else (if b 9 = 0 then (true, [26,1,12,2,5]) else (false, [26,23,0,1,2])))))))
    else (if b 4 = 0 then (if b 5 = 0 then (if b 6 = 0 then (if b 7 = 0 then (if b 8 = 0 then
    (if b 9 = 0 then (true, [26,0]) else (false, [26,7,14,13,11])) else (if b 9 = 0 then
    (false, [26,7,4,13,7]) else (true, [26,24,0]))) else (if b 8 = 0 then (if b 9 = 0 then
    (true, [26,19,0]) else (false, [26,7,14,13,5,2])) else (if b 9 = 0 then (false,
    [26,7,4,13,1,2]) else (true, [26,24,19,0])))) else (if b 7 = 0 then (if b 8 = 0 then (if b
    9 = 0 then (true, [26,16,0]) else (false, [26,20,13,11])) else (if b 9 = 0 then (false,
    [26,18,14,7]) else (true, [26,24,16,0]))) else (if b 8 = 0 then (if b 9 = 0 then (true,
    [26,2,16,0]) else (false, [26,20,13,5,2])) else (if b 9 = 0 then (false, [26,18,14,1,2])
    else (true, [26,24,2,16,0]))))) else (if b 6 = 0 then (if b 7 = 0 then (if b 8 = 0 then (if
    b 9 = 0 then (true, [26,7,0]) else (false, [26,14,13,11])) else (if b 9 = 0 then (false,
    [26,4,13,7]) else (true, [26,24,7,0]))) else (if b 8 = 0 then (if b 9 = 0 then (true,
    [26,12,7,0]) else (false, [26,14,13,5,2])) else (if b 9 = 0 then (false, [26,4,13,1,2])
    else (true, [26,24,12,7,0])))) else (if b 7 = 0 then (if b 8 = 0 then (if b 9 = 0 then
    (false, [26,4,13]) else (true, [26,17,7,0])) else (if b 9 = 0 then (true, [26,16,7,0]) else
    (false, [26,25,0,7]))) else (if b 8 = 0 then (if b 9 = 0 then (false, [26,4,13,2]) else
    (true, [26,17,12,7,0])) else (if b 9 = 0 then (true, [26,16,12,7,0]) else (false,
    [26,25,0,1,2])))))) else (if b 5 = 0 then (if b 6 = 0 then (if b 7 = 0 then (if b 8 = 0
    then (if b 9 = 0 then (true, [26,1,0]) else (false, [26,12,11,4,6,8])) else (if b 9 = 0
    then (false, [26,2,13,10,8,7]) else (true, [26,24,1,0]))) else (if b 8 = 0 then (if b 9 = 0
    then (false, [26,4,6,2,8,2]) else (true, [26,21,1,0])) else (if b 9 = 0 then (true,
    [26,19,1,0]) else (false, [26,25,2,8,0,1,2])))) else (if b 7 = 0 then (if b 8 = 0 then (if
    b 9 = 0 then (true, [26,12,1,0]) else (false, [26,11,4,6,8])) else (if b 9 = 0 then (false,
    [26,18,10,8,7]) else (true, [26,24,12,1,0]))) else (if b 8 = 0 then (if b 9 = 0 then
    (false, [26,15,4,13,2]) else (true, [26,21,12,1,0])) else (if b 9 = 0 then (true,
    [26,19,12,1,0]) else (false, [26,25,15,0,1,2]))))) else (if b 6 = 0 then (if b 7 = 0 then
    (if b 8 = 0 then (if b 9 = 0 then (true, [26,2,1,0]) else (false, [26,17,4,6,8])) else (if
    b 9 = 0 then (false, [26,13,10,8,7]) else (true, [26,24,2,1,0]))) else (if b 8 = 0 then (if
    b 9 = 0 then (false, [26,4,6,8,2]) else (true, [26,21,2,1,0])) else (if b 9 = 0 then (true,
    [26,19,2,1,0]) else (false, [26,25,8,0,1,2])))) else (if b 7 = 0 then (if b 8 = 0 then (if
    b 9 = 0 then (false, [26,4,6,8]) else (true, [26,17,2,1,0])) else (if b 9 = 0 then (true,
    [26,16,2,1,0]) else (false, [26,25,8,0,7]))) else (if b 8 = 0 then (if b 9 = 0 then (true,
    [26,12,2,1,0]) else (false, [26,23,13,5,2])) else (if b 9 = 0 then (false, [26,22,14,1,2])
    else (true, [26,24,12,2,1,0])))))))))))

theorem yReach_flag : ∀ b : Fin 10 → Fin 2,
    yB (yOf2 b) yY = 0 → yOf2 b ≠ 0 → yOf2 b ≠ yY →
      (yWordOf b).1 = true ∨ (yWordOf b).1 = false := by
  decide +kernel

theorem yReach_check0 : ∀ b : Fin 10 → Fin 2,
    yB (yOf2 b) yY = 0 → yOf2 b ≠ 0 → yOf2 b ≠ yY →
      (yWordOf b).1 = true → yApply (yWordOf b).2 (yOf2 b) = yBase0 := by
  decide +kernel

theorem yReach_check1 : ∀ b : Fin 10 → Fin 2,
    yB (yOf2 b) yY = 0 → yOf2 b ≠ 0 → yOf2 b ≠ yY →
      (yWordOf b).1 = false → yApply (yWordOf b).2 (yOf2 b) = yBase1 := by
  decide +kernel

@[expose] def ySpanWords0 : List (List (Fin 27)) := [
  [],
  [0],
  [5],
  [11],
  [17],
  [21],
  [24],
  [26],
  [0, 24]]

@[expose] def ySpanWords1 : List (List (Fin 27)) := [
  [],
  [2],
  [7],
  [8],
  [11],
  [13],
  [14],
  [26],
  [2, 8]]

@[expose] def ySpanVecs0 : List (Fin 10 → ZMod 2) :=
  ySpanWords0.map fun w => yApply w yBase0

@[expose] def ySpanVecs1 : List (Fin 10 → ZMod 2) :=
  ySpanWords1.map fun w => yApply w yBase1

@[expose] def yLiftFun (u : Fin 8 → ZMod 2) : Fin 10 → ZMod 2 :=
  fun k => if h : (k : ℕ) < 2 then 0 else u ⟨(k : ℕ) - 2, by omega⟩

@[expose] def yProjFun (v : Fin 10 → ZMod 2) : Fin 8 → ZMod 2 :=
  fun j => v ⟨(j : ℕ) + 2, by omega⟩

theorem yProj_lift : ∀ u : Fin 8 → ZMod 2, yProjFun (yLiftFun u) = u := by
  decide +kernel

theorem yLift_mem_yPerp : ∀ u : Fin 8 → ZMod 2, yB (yLiftFun u) yY = 0 := by
  decide +kernel

theorem yProj_yY : yProjFun yY = 0 := by
  decide +kernel

theorem yLift_ne_yY (u : Fin 8 → ZMod 2) : yLiftFun u ≠ yY := by
  intro h
  have := congrFun h 0
  simp [yLiftFun, yY] at this

theorem yLift_ne_zero {u : Fin 8 → ZMod 2} (hu : u ≠ 0) : yLiftFun u ≠ 0 := by
  intro h
  apply hu
  rw [← yProj_lift u, h]
  rfl

theorem yLift_proj_check : ∀ b : Fin 10 → Fin 2, yB (yOf2 b) yY = 0 →
    yLiftFun (yProjFun (yOf2 b)) = yOf2 b + (yOf2 b 0) • yY := by
  decide +kernel

theorem yProj_kernel_check : ∀ b : Fin 10 → Fin 2, yB (yOf2 b) yY = 0 →
    yProjFun (yOf2 b) = 0 → yOf2 b = 0 ∨ yOf2 b = yY := by
  decide +kernel

theorem yAdd_self (v : Fin 10 → ZMod 2) : v + v = 0 := by
  rw [← two_smul (ZMod 2) v]
  have h2 : (2 : ZMod 2) = 0 := by decide
  rw [h2, zero_smul]

theorem yEq_of_add_eq_zero {a b : Fin 10 → ZMod 2} (h : a + b = 0) : a = b := by
  calc a = a + (b + b) := by rw [yAdd_self, add_zero]
    _ = (a + b) + b := by abel
    _ = b := by rw [h, zero_add]

theorem yEq_of_add_eq {a b c : Fin 10 → ZMod 2} (h : a + b = c) : a = b + c := by
  calc a = a + (b + b) := by rw [yAdd_self, add_zero]
    _ = (a + b) + b := by abel
    _ = c + b := by rw [h]
    _ = b + c := by abel

@[expose] def yMaskOf0 (b : Fin 10 → Fin 2) : List Bool :=
(if b 0 = 0 then (if b 1 = 0 then (if b 2 = 0 then (if b 3 = 0 then (if b 4 = 0 then (if b 5 =
    0 then (if b 6 = 0 then (if b 7 = 0 then (if b 8 = 0 then (if b 9 = 0 then [false, false,
    false, false, false, false, false, false, false] else [true, true, false, false, false,
    false, true, false, true]) else (if b 9 = 0 then [true, false, false, false, false, false,
    true, false, false] else [false, true, false, false, false, false, false, false, true]))
    else (if b 8 = 0 then (if b 9 = 0 then [true, false, false, false, false, true, false,
    false, false] else [false, true, false, false, false, true, true, false, true]) else (if b
    9 = 0 then [false, false, false, false, false, true, true, false, false] else [true, true,
    false, false, false, true, false, false, true]))) else (if b 7 = 0 then (if b 8 = 0 then
    (if b 9 = 0 then [true, false, false, false, true, false, false, false, false] else [false,
    true, false, false, true, false, true, false, true]) else (if b 9 = 0 then [false, false,
    false, false, true, false, true, false, false] else [true, true, false, false, true, false,
    false, false, true])) else (if b 8 = 0 then (if b 9 = 0 then [false, false, false, false,
    true, true, false, false, false] else [true, true, false, false, true, true, true, false,
    true]) else (if b 9 = 0 then [true, false, false, false, true, true, true, false, false]
    else [false, true, false, false, true, true, false, false, true])))) else (if b 6 = 0 then
    (if b 7 = 0 then (if b 8 = 0 then (if b 9 = 0 then [true, false, false, true, false, false,
    false, false, false] else [false, true, false, true, false, false, true, false, true]) else
    (if b 9 = 0 then [false, false, false, true, false, false, true, false, false] else [true,
    true, false, true, false, false, false, false, true])) else (if b 8 = 0 then (if b 9 = 0
    then [false, false, false, true, false, true, false, false, false] else [true, true, false,
    true, false, true, true, false, true]) else (if b 9 = 0 then [true, false, false, true,
    false, true, true, false, false] else [false, true, false, true, false, true, false, false,
    true]))) else (if b 7 = 0 then (if b 8 = 0 then (if b 9 = 0 then [false, false, false,
    true, true, false, false, false, false] else [true, true, false, true, true, false, true,
    false, true]) else (if b 9 = 0 then [true, false, false, true, true, false, true, false,
    false] else [false, true, false, true, true, false, false, false, true])) else (if b 8 = 0
    then (if b 9 = 0 then [true, false, false, true, true, true, false, false, false] else
    [false, true, false, true, true, true, true, false, true]) else (if b 9 = 0 then [false,
    false, false, true, true, true, true, false, false] else [true, true, false, true, true,
    true, false, false, true]))))) else (if b 5 = 0 then (if b 6 = 0 then (if b 7 = 0 then (if
    b 8 = 0 then (if b 9 = 0 then [true, false, true, false, false, false, false, false, false]
    else [false, true, true, false, false, false, true, false, true]) else (if b 9 = 0 then
    [false, false, true, false, false, false, true, false, false] else [true, true, true,
    false, false, false, false, false, true])) else (if b 8 = 0 then (if b 9 = 0 then [false,
    false, true, false, false, true, false, false, false] else [true, true, true, false, false,
    true, true, false, true]) else (if b 9 = 0 then [true, false, true, false, false, true,
    true, false, false] else [false, true, true, false, false, true, false, false, true])))
    else (if b 7 = 0 then (if b 8 = 0 then (if b 9 = 0 then [false, false, true, false, true,
    false, false, false, false] else [true, true, true, false, true, false, true, false, true])
    else (if b 9 = 0 then [true, false, true, false, true, false, true, false, false] else
    [false, true, true, false, true, false, false, false, true])) else (if b 8 = 0 then (if b 9
    = 0 then [true, false, true, false, true, true, false, false, false] else [false, true,
    true, false, true, true, true, false, true]) else (if b 9 = 0 then [false, false, true,
    false, true, true, true, false, false] else [true, true, true, false, true, true, false,
    false, true])))) else (if b 6 = 0 then (if b 7 = 0 then (if b 8 = 0 then (if b 9 = 0 then
    [false, false, true, true, false, false, false, false, false] else [true, true, true, true,
    false, false, true, false, true]) else (if b 9 = 0 then [true, false, true, true, false,
    false, true, false, false] else [false, true, true, true, false, false, false, false,
    true])) else (if b 8 = 0 then (if b 9 = 0 then [true, false, true, true, false, true,
    false, false, false] else [false, true, true, true, false, true, true, false, true]) else
    (if b 9 = 0 then [false, false, true, true, false, true, true, false, false] else [true,
    true, true, true, false, true, false, false, true]))) else (if b 7 = 0 then (if b 8 = 0
    then (if b 9 = 0 then [true, false, true, true, true, false, false, false, false] else
    [false, true, true, true, true, false, true, false, true]) else (if b 9 = 0 then [false,
    false, true, true, true, false, true, false, false] else [true, true, true, true, true,
    false, false, false, true])) else (if b 8 = 0 then (if b 9 = 0 then [false, false, true,
    true, true, true, false, false, false] else [true, true, true, true, true, true, true,
    false, true]) else (if b 9 = 0 then [true, false, true, true, true, true, true, false,
    false] else [false, true, true, true, true, true, false, false, true])))))) else (if b 4 =
    0 then (if b 5 = 0 then (if b 6 = 0 then (if b 7 = 0 then (if b 8 = 0 then (if b 9 = 0 then
    [true, true, false, false, false, false, false, false, false] else [false, false, false,
    false, false, false, true, false, true]) else (if b 9 = 0 then [false, true, false, false,
    false, false, true, false, false] else [true, false, false, false, false, false, false,
    false, true])) else (if b 8 = 0 then (if b 9 = 0 then [false, true, false, false, false,
    true, false, false, false] else [true, false, false, false, false, true, true, false,
    true]) else (if b 9 = 0 then [true, true, false, false, false, true, true, false, false]
    else [false, false, false, false, false, true, false, false, true]))) else (if b 7 = 0 then
    (if b 8 = 0 then (if b 9 = 0 then [false, true, false, false, true, false, false, false,
    false] else [true, false, false, false, true, false, true, false, true]) else (if b 9 = 0
    then [true, true, false, false, true, false, true, false, false] else [false, false, false,
    false, true, false, false, false, true])) else (if b 8 = 0 then (if b 9 = 0 then [true,
    true, false, false, true, true, false, false, false] else [false, false, false, false,
    true, true, true, false, true]) else (if b 9 = 0 then [false, true, false, false, true,
    true, true, false, false] else [true, false, false, false, true, true, false, false,
    true])))) else (if b 6 = 0 then (if b 7 = 0 then (if b 8 = 0 then (if b 9 = 0 then [false,
    true, false, true, false, false, false, false, false] else [true, false, false, true,
    false, false, true, false, true]) else (if b 9 = 0 then [true, true, false, true, false,
    false, true, false, false] else [false, false, false, true, false, false, false, false,
    true])) else (if b 8 = 0 then (if b 9 = 0 then [true, true, false, true, false, true,
    false, false, false] else [false, false, false, true, false, true, true, false, true]) else
    (if b 9 = 0 then [false, true, false, true, false, true, true, false, false] else [true,
    false, false, true, false, true, false, false, true]))) else (if b 7 = 0 then (if b 8 = 0
    then (if b 9 = 0 then [true, true, false, true, true, false, false, false, false] else
    [false, false, false, true, true, false, true, false, true]) else (if b 9 = 0 then [false,
    true, false, true, true, false, true, false, false] else [true, false, false, true, true,
    false, false, false, true])) else (if b 8 = 0 then (if b 9 = 0 then [false, true, false,
    true, true, true, false, false, false] else [true, false, false, true, true, true, true,
    false, true]) else (if b 9 = 0 then [true, true, false, true, true, true, true, false,
    false] else [false, false, false, true, true, true, false, false, true]))))) else (if b 5 =
    0 then (if b 6 = 0 then (if b 7 = 0 then (if b 8 = 0 then (if b 9 = 0 then [false, true,
    true, false, false, false, false, false, false] else [true, false, true, false, false,
    false, true, false, true]) else (if b 9 = 0 then [true, true, true, false, false, false,
    true, false, false] else [false, false, true, false, false, false, false, false, true]))
    else (if b 8 = 0 then (if b 9 = 0 then [true, true, true, false, false, true, false, false,
    false] else [false, false, true, false, false, true, true, false, true]) else (if b 9 = 0
    then [false, true, true, false, false, true, true, false, false] else [true, false, true,
    false, false, true, false, false, true]))) else (if b 7 = 0 then (if b 8 = 0 then (if b 9 =
    0 then [true, true, true, false, true, false, false, false, false] else [false, false,
    true, false, true, false, true, false, true]) else (if b 9 = 0 then [false, true, true,
    false, true, false, true, false, false] else [true, false, true, false, true, false, false,
    false, true])) else (if b 8 = 0 then (if b 9 = 0 then [false, true, true, false, true,
    true, false, false, false] else [true, false, true, false, true, true, true, false, true])
    else (if b 9 = 0 then [true, true, true, false, true, true, true, false, false] else
    [false, false, true, false, true, true, false, false, true])))) else (if b 6 = 0 then (if b
    7 = 0 then (if b 8 = 0 then (if b 9 = 0 then [true, true, true, true, false, false, false,
    false, false] else [false, false, true, true, false, false, true, false, true]) else (if b
    9 = 0 then [false, true, true, true, false, false, true, false, false] else [true, false,
    true, true, false, false, false, false, true])) else (if b 8 = 0 then (if b 9 = 0 then
    [false, true, true, true, false, true, false, false, false] else [true, false, true, true,
    false, true, true, false, true]) else (if b 9 = 0 then [true, true, true, true, false,
    true, true, false, false] else [false, false, true, true, false, true, false, false,
    true]))) else (if b 7 = 0 then (if b 8 = 0 then (if b 9 = 0 then [false, true, true, true,
    true, false, false, false, false] else [true, false, true, true, true, false, true, false,
    true]) else (if b 9 = 0 then [true, true, true, true, true, false, true, false, false] else
    [false, false, true, true, true, false, false, false, true])) else (if b 8 = 0 then (if b 9
    = 0 then [true, true, true, true, true, true, false, false, false] else [false, false,
    true, true, true, true, true, false, true]) else (if b 9 = 0 then [false, true, true, true,
    true, true, true, false, false] else [true, false, true, true, true, true, false, false,
    true]))))))) else (if b 3 = 0 then (if b 4 = 0 then (if b 5 = 0 then (if b 6 = 0 then (if b
    7 = 0 then (if b 8 = 0 then (if b 9 = 0 then [true, false, false, false, false, false,
    false, false, false] else [false, true, false, false, false, false, true, false, true])
    else (if b 9 = 0 then [false, false, false, false, false, false, true, false, false] else
    [true, true, false, false, false, false, false, false, true])) else (if b 8 = 0 then (if b
    9 = 0 then [false, false, false, false, false, true, false, false, false] else [true, true,
    false, false, false, true, true, false, true]) else (if b 9 = 0 then [true, false, false,
    false, false, true, true, false, false] else [false, true, false, false, false, true,
    false, false, true]))) else (if b 7 = 0 then (if b 8 = 0 then (if b 9 = 0 then [false,
    false, false, false, true, false, false, false, false] else [true, true, false, false,
    true, false, true, false, true]) else (if b 9 = 0 then [true, false, false, false, true,
    false, true, false, false] else [false, true, false, false, true, false, false, false,
    true])) else (if b 8 = 0 then (if b 9 = 0 then [true, false, false, false, true, true,
    false, false, false] else [false, true, false, false, true, true, true, false, true]) else
    (if b 9 = 0 then [false, false, false, false, true, true, true, false, false] else [true,
    true, false, false, true, true, false, false, true])))) else (if b 6 = 0 then (if b 7 = 0
    then (if b 8 = 0 then (if b 9 = 0 then [false, false, false, true, false, false, false,
    false, false] else [true, true, false, true, false, false, true, false, true]) else (if b 9
    = 0 then [true, false, false, true, false, false, true, false, false] else [false, true,
    false, true, false, false, false, false, true])) else (if b 8 = 0 then (if b 9 = 0 then
    [true, false, false, true, false, true, false, false, false] else [false, true, false,
    true, false, true, true, false, true]) else (if b 9 = 0 then [false, false, false, true,
    false, true, true, false, false] else [true, true, false, true, false, true, false, false,
    true]))) else (if b 7 = 0 then (if b 8 = 0 then (if b 9 = 0 then [true, false, false, true,
    true, false, false, false, false] else [false, true, false, true, true, false, true, false,
    true]) else (if b 9 = 0 then [false, false, false, true, true, false, true, false, false]
    else [true, true, false, true, true, false, false, false, true])) else (if b 8 = 0 then (if
    b 9 = 0 then [false, false, false, true, true, true, false, false, false] else [true, true,
    false, true, true, true, true, false, true]) else (if b 9 = 0 then [true, false, false,
    true, true, true, true, false, false] else [false, true, false, true, true, true, false,
    false, true]))))) else (if b 5 = 0 then (if b 6 = 0 then (if b 7 = 0 then (if b 8 = 0 then
    (if b 9 = 0 then [false, false, true, false, false, false, false, false, false] else [true,
    true, true, false, false, false, true, false, true]) else (if b 9 = 0 then [true, false,
    true, false, false, false, true, false, false] else [false, true, true, false, false,
    false, false, false, true])) else (if b 8 = 0 then (if b 9 = 0 then [true, false, true,
    false, false, true, false, false, false] else [false, true, true, false, false, true, true,
    false, true]) else (if b 9 = 0 then [false, false, true, false, false, true, true, false,
    false] else [true, true, true, false, false, true, false, false, true]))) else (if b 7 = 0
    then (if b 8 = 0 then (if b 9 = 0 then [true, false, true, false, true, false, false,
    false, false] else [false, true, true, false, true, false, true, false, true]) else (if b 9
    = 0 then [false, false, true, false, true, false, true, false, false] else [true, true,
    true, false, true, false, false, false, true])) else (if b 8 = 0 then (if b 9 = 0 then
    [false, false, true, false, true, true, false, false, false] else [true, true, true, false,
    true, true, true, false, true]) else (if b 9 = 0 then [true, false, true, false, true,
    true, true, false, false] else [false, true, true, false, true, true, false, false,
    true])))) else (if b 6 = 0 then (if b 7 = 0 then (if b 8 = 0 then (if b 9 = 0 then [true,
    false, true, true, false, false, false, false, false] else [false, true, true, true, false,
    false, true, false, true]) else (if b 9 = 0 then [false, false, true, true, false, false,
    true, false, false] else [true, true, true, true, false, false, false, false, true])) else
    (if b 8 = 0 then (if b 9 = 0 then [false, false, true, true, false, true, false, false,
    false] else [true, true, true, true, false, true, true, false, true]) else (if b 9 = 0 then
    [true, false, true, true, false, true, true, false, false] else [false, true, true, true,
    false, true, false, false, true]))) else (if b 7 = 0 then (if b 8 = 0 then (if b 9 = 0 then
    [false, false, true, true, true, false, false, false, false] else [true, true, true, true,
    true, false, true, false, true]) else (if b 9 = 0 then [true, false, true, true, true,
    false, true, false, false] else [false, true, true, true, true, false, false, false,
    true])) else (if b 8 = 0 then (if b 9 = 0 then [true, false, true, true, true, true, false,
    false, false] else [false, true, true, true, true, true, true, false, true]) else (if b 9 =
    0 then [false, false, true, true, true, true, true, false, false] else [true, true, true,
    true, true, true, false, false, true])))))) else (if b 4 = 0 then (if b 5 = 0 then (if b 6
    = 0 then (if b 7 = 0 then (if b 8 = 0 then (if b 9 = 0 then [false, true, false, false,
    false, false, false, false, false] else [true, false, false, false, false, false, true,
    false, true]) else (if b 9 = 0 then [true, true, false, false, false, false, true, false,
    false] else [false, false, false, false, false, false, false, false, true])) else (if b 8 =
    0 then (if b 9 = 0 then [true, true, false, false, false, true, false, false, false] else
    [false, false, false, false, false, true, true, false, true]) else (if b 9 = 0 then [false,
    true, false, false, false, true, true, false, false] else [true, false, false, false,
    false, true, false, false, true]))) else (if b 7 = 0 then (if b 8 = 0 then (if b 9 = 0 then
    [true, true, false, false, true, false, false, false, false] else [false, false, false,
    false, true, false, true, false, true]) else (if b 9 = 0 then [false, true, false, false,
    true, false, true, false, false] else [true, false, false, false, true, false, false,
    false, true])) else (if b 8 = 0 then (if b 9 = 0 then [false, true, false, false, true,
    true, false, false, false] else [true, false, false, false, true, true, true, false, true])
    else (if b 9 = 0 then [true, true, false, false, true, true, true, false, false] else
    [false, false, false, false, true, true, false, false, true])))) else (if b 6 = 0 then (if
    b 7 = 0 then (if b 8 = 0 then (if b 9 = 0 then [true, true, false, true, false, false,
    false, false, false] else [false, false, false, true, false, false, true, false, true])
    else (if b 9 = 0 then [false, true, false, true, false, false, true, false, false] else
    [true, false, false, true, false, false, false, false, true])) else (if b 8 = 0 then (if b
    9 = 0 then [false, true, false, true, false, true, false, false, false] else [true, false,
    false, true, false, true, true, false, true]) else (if b 9 = 0 then [true, true, false,
    true, false, true, true, false, false] else [false, false, false, true, false, true, false,
    false, true]))) else (if b 7 = 0 then (if b 8 = 0 then (if b 9 = 0 then [false, true,
    false, true, true, false, false, false, false] else [true, false, false, true, true, false,
    true, false, true]) else (if b 9 = 0 then [true, true, false, true, true, false, true,
    false, false] else [false, false, false, true, true, false, false, false, true])) else (if
    b 8 = 0 then (if b 9 = 0 then [true, true, false, true, true, true, false, false, false]
    else [false, false, false, true, true, true, true, false, true]) else (if b 9 = 0 then
    [false, true, false, true, true, true, true, false, false] else [true, false, false, true,
    true, true, false, false, true]))))) else (if b 5 = 0 then (if b 6 = 0 then (if b 7 = 0
    then (if b 8 = 0 then (if b 9 = 0 then [true, true, true, false, false, false, false,
    false, false] else [false, false, true, false, false, false, true, false, true]) else (if b
    9 = 0 then [false, true, true, false, false, false, true, false, false] else [true, false,
    true, false, false, false, false, false, true])) else (if b 8 = 0 then (if b 9 = 0 then
    [false, true, true, false, false, true, false, false, false] else [true, false, true,
    false, false, true, true, false, true]) else (if b 9 = 0 then [true, true, true, false,
    false, true, true, false, false] else [false, false, true, false, false, true, false,
    false, true]))) else (if b 7 = 0 then (if b 8 = 0 then (if b 9 = 0 then [false, true, true,
    false, true, false, false, false, false] else [true, false, true, false, true, false, true,
    false, true]) else (if b 9 = 0 then [true, true, true, false, true, false, true, false,
    false] else [false, false, true, false, true, false, false, false, true])) else (if b 8 = 0
    then (if b 9 = 0 then [true, true, true, false, true, true, false, false, false] else
    [false, false, true, false, true, true, true, false, true]) else (if b 9 = 0 then [false,
    true, true, false, true, true, true, false, false] else [true, false, true, false, true,
    true, false, false, true])))) else (if b 6 = 0 then (if b 7 = 0 then (if b 8 = 0 then (if b
    9 = 0 then [false, true, true, true, false, false, false, false, false] else [true, false,
    true, true, false, false, true, false, true]) else (if b 9 = 0 then [true, true, true,
    true, false, false, true, false, false] else [false, false, true, true, false, false,
    false, false, true])) else (if b 8 = 0 then (if b 9 = 0 then [true, true, true, true,
    false, true, false, false, false] else [false, false, true, true, false, true, true, false,
    true]) else (if b 9 = 0 then [false, true, true, true, false, true, true, false, false]
    else [true, false, true, true, false, true, false, false, true]))) else (if b 7 = 0 then
    (if b 8 = 0 then (if b 9 = 0 then [true, true, true, true, true, false, false, false,
    false] else [false, false, true, true, true, false, true, false, true]) else (if b 9 = 0
    then [false, true, true, true, true, false, true, false, false] else [true, false, true,
    true, true, false, false, false, true])) else (if b 8 = 0 then (if b 9 = 0 then [false,
    true, true, true, true, true, false, false, false] else [true, false, true, true, true,
    true, true, false, true]) else (if b 9 = 0 then [true, true, true, true, true, true, true,
    false, false] else [false, false, true, true, true, true, false, false, true])))))))) else
    (if b 2 = 0 then (if b 3 = 0 then (if b 4 = 0 then (if b 5 = 0 then (if b 6 = 0 then (if b
    7 = 0 then (if b 8 = 0 then (if b 9 = 0 then [false, false, false, false, false, false,
    false, false, false] else [false, false, false, false, false, false, false, false, false])
    else (if b 9 = 0 then [false, false, false, false, false, false, false, false, false] else
    [false, false, false, false, false, false, false, false, false])) else (if b 8 = 0 then (if
    b 9 = 0 then [false, false, false, false, false, false, false, false, false] else [false,
    false, false, false, false, false, false, false, false]) else (if b 9 = 0 then [false,
    false, false, false, false, false, false, false, false] else [false, false, false, false,
    false, false, false, false, false]))) else (if b 7 = 0 then (if b 8 = 0 then (if b 9 = 0
    then [false, false, false, false, false, false, false, false, false] else [false, false,
    false, false, false, false, false, false, false]) else (if b 9 = 0 then [false, false,
    false, false, false, false, false, false, false] else [false, false, false, false, false,
    false, false, false, false])) else (if b 8 = 0 then (if b 9 = 0 then [false, false, false,
    false, false, false, false, false, false] else [false, false, false, false, false, false,
    false, false, false]) else (if b 9 = 0 then [false, false, false, false, false, false,
    false, false, false] else [false, false, false, false, false, false, false, false,
    false])))) else (if b 6 = 0 then (if b 7 = 0 then (if b 8 = 0 then (if b 9 = 0 then [false,
    false, false, false, false, false, false, false, false] else [false, false, false, false,
    false, false, false, false, false]) else (if b 9 = 0 then [false, false, false, false,
    false, false, false, false, false] else [false, false, false, false, false, false, false,
    false, false])) else (if b 8 = 0 then (if b 9 = 0 then [false, false, false, false, false,
    false, false, false, false] else [false, false, false, false, false, false, false, false,
    false]) else (if b 9 = 0 then [false, false, false, false, false, false, false, false,
    false] else [false, false, false, false, false, false, false, false, false]))) else (if b 7
    = 0 then (if b 8 = 0 then (if b 9 = 0 then [false, false, false, false, false, false,
    false, false, false] else [false, false, false, false, false, false, false, false, false])
    else (if b 9 = 0 then [false, false, false, false, false, false, false, false, false] else
    [false, false, false, false, false, false, false, false, false])) else (if b 8 = 0 then (if
    b 9 = 0 then [false, false, false, false, false, false, false, false, false] else [false,
    false, false, false, false, false, false, false, false]) else (if b 9 = 0 then [false,
    false, false, false, false, false, false, false, false] else [false, false, false, false,
    false, false, false, false, false]))))) else (if b 5 = 0 then (if b 6 = 0 then (if b 7 = 0
    then (if b 8 = 0 then (if b 9 = 0 then [false, false, false, false, false, false, false,
    false, false] else [false, false, false, false, false, false, false, false, false]) else
    (if b 9 = 0 then [false, false, false, false, false, false, false, false, false] else
    [false, false, false, false, false, false, false, false, false])) else (if b 8 = 0 then (if
    b 9 = 0 then [false, false, false, false, false, false, false, false, false] else [false,
    false, false, false, false, false, false, false, false]) else (if b 9 = 0 then [false,
    false, false, false, false, false, false, false, false] else [false, false, false, false,
    false, false, false, false, false]))) else (if b 7 = 0 then (if b 8 = 0 then (if b 9 = 0
    then [false, false, false, false, false, false, false, false, false] else [false, false,
    false, false, false, false, false, false, false]) else (if b 9 = 0 then [false, false,
    false, false, false, false, false, false, false] else [false, false, false, false, false,
    false, false, false, false])) else (if b 8 = 0 then (if b 9 = 0 then [false, false, false,
    false, false, false, false, false, false] else [false, false, false, false, false, false,
    false, false, false]) else (if b 9 = 0 then [false, false, false, false, false, false,
    false, false, false] else [false, false, false, false, false, false, false, false,
    false])))) else (if b 6 = 0 then (if b 7 = 0 then (if b 8 = 0 then (if b 9 = 0 then [false,
    false, false, false, false, false, false, false, false] else [false, false, false, false,
    false, false, false, false, false]) else (if b 9 = 0 then [false, false, false, false,
    false, false, false, false, false] else [false, false, false, false, false, false, false,
    false, false])) else (if b 8 = 0 then (if b 9 = 0 then [false, false, false, false, false,
    false, false, false, false] else [false, false, false, false, false, false, false, false,
    false]) else (if b 9 = 0 then [false, false, false, false, false, false, false, false,
    false] else [false, false, false, false, false, false, false, false, false]))) else (if b 7
    = 0 then (if b 8 = 0 then (if b 9 = 0 then [false, false, false, false, false, false,
    false, false, false] else [false, false, false, false, false, false, false, false, false])
    else (if b 9 = 0 then [false, false, false, false, false, false, false, false, false] else
    [false, false, false, false, false, false, false, false, false])) else (if b 8 = 0 then (if
    b 9 = 0 then [false, false, false, false, false, false, false, false, false] else [false,
    false, false, false, false, false, false, false, false]) else (if b 9 = 0 then [false,
    false, false, false, false, false, false, false, false] else [false, false, false, false,
    false, false, false, false, false])))))) else (if b 4 = 0 then (if b 5 = 0 then (if b 6 = 0
    then (if b 7 = 0 then (if b 8 = 0 then (if b 9 = 0 then [false, false, false, false, false,
    false, false, false, false] else [false, false, false, false, false, false, false, false,
    false]) else (if b 9 = 0 then [false, false, false, false, false, false, false, false,
    false] else [false, false, false, false, false, false, false, false, false])) else (if b 8
    = 0 then (if b 9 = 0 then [false, false, false, false, false, false, false, false, false]
    else [false, false, false, false, false, false, false, false, false]) else (if b 9 = 0 then
    [false, false, false, false, false, false, false, false, false] else [false, false, false,
    false, false, false, false, false, false]))) else (if b 7 = 0 then (if b 8 = 0 then (if b 9
    = 0 then [false, false, false, false, false, false, false, false, false] else [false,
    false, false, false, false, false, false, false, false]) else (if b 9 = 0 then [false,
    false, false, false, false, false, false, false, false] else [false, false, false, false,
    false, false, false, false, false])) else (if b 8 = 0 then (if b 9 = 0 then [false, false,
    false, false, false, false, false, false, false] else [false, false, false, false, false,
    false, false, false, false]) else (if b 9 = 0 then [false, false, false, false, false,
    false, false, false, false] else [false, false, false, false, false, false, false, false,
    false])))) else (if b 6 = 0 then (if b 7 = 0 then (if b 8 = 0 then (if b 9 = 0 then [false,
    false, false, false, false, false, false, false, false] else [false, false, false, false,
    false, false, false, false, false]) else (if b 9 = 0 then [false, false, false, false,
    false, false, false, false, false] else [false, false, false, false, false, false, false,
    false, false])) else (if b 8 = 0 then (if b 9 = 0 then [false, false, false, false, false,
    false, false, false, false] else [false, false, false, false, false, false, false, false,
    false]) else (if b 9 = 0 then [false, false, false, false, false, false, false, false,
    false] else [false, false, false, false, false, false, false, false, false]))) else (if b 7
    = 0 then (if b 8 = 0 then (if b 9 = 0 then [false, false, false, false, false, false,
    false, false, false] else [false, false, false, false, false, false, false, false, false])
    else (if b 9 = 0 then [false, false, false, false, false, false, false, false, false] else
    [false, false, false, false, false, false, false, false, false])) else (if b 8 = 0 then (if
    b 9 = 0 then [false, false, false, false, false, false, false, false, false] else [false,
    false, false, false, false, false, false, false, false]) else (if b 9 = 0 then [false,
    false, false, false, false, false, false, false, false] else [false, false, false, false,
    false, false, false, false, false]))))) else (if b 5 = 0 then (if b 6 = 0 then (if b 7 = 0
    then (if b 8 = 0 then (if b 9 = 0 then [false, false, false, false, false, false, false,
    false, false] else [false, false, false, false, false, false, false, false, false]) else
    (if b 9 = 0 then [false, false, false, false, false, false, false, false, false] else
    [false, false, false, false, false, false, false, false, false])) else (if b 8 = 0 then (if
    b 9 = 0 then [false, false, false, false, false, false, false, false, false] else [false,
    false, false, false, false, false, false, false, false]) else (if b 9 = 0 then [false,
    false, false, false, false, false, false, false, false] else [false, false, false, false,
    false, false, false, false, false]))) else (if b 7 = 0 then (if b 8 = 0 then (if b 9 = 0
    then [false, false, false, false, false, false, false, false, false] else [false, false,
    false, false, false, false, false, false, false]) else (if b 9 = 0 then [false, false,
    false, false, false, false, false, false, false] else [false, false, false, false, false,
    false, false, false, false])) else (if b 8 = 0 then (if b 9 = 0 then [false, false, false,
    false, false, false, false, false, false] else [false, false, false, false, false, false,
    false, false, false]) else (if b 9 = 0 then [false, false, false, false, false, false,
    false, false, false] else [false, false, false, false, false, false, false, false,
    false])))) else (if b 6 = 0 then (if b 7 = 0 then (if b 8 = 0 then (if b 9 = 0 then [false,
    false, false, false, false, false, false, false, false] else [false, false, false, false,
    false, false, false, false, false]) else (if b 9 = 0 then [false, false, false, false,
    false, false, false, false, false] else [false, false, false, false, false, false, false,
    false, false])) else (if b 8 = 0 then (if b 9 = 0 then [false, false, false, false, false,
    false, false, false, false] else [false, false, false, false, false, false, false, false,
    false]) else (if b 9 = 0 then [false, false, false, false, false, false, false, false,
    false] else [false, false, false, false, false, false, false, false, false]))) else (if b 7
    = 0 then (if b 8 = 0 then (if b 9 = 0 then [false, false, false, false, false, false,
    false, false, false] else [false, false, false, false, false, false, false, false, false])
    else (if b 9 = 0 then [false, false, false, false, false, false, false, false, false] else
    [false, false, false, false, false, false, false, false, false])) else (if b 8 = 0 then (if
    b 9 = 0 then [false, false, false, false, false, false, false, false, false] else [false,
    false, false, false, false, false, false, false, false]) else (if b 9 = 0 then [false,
    false, false, false, false, false, false, false, false] else [false, false, false, false,
    false, false, false, false, false]))))))) else (if b 3 = 0 then (if b 4 = 0 then (if b 5 =
    0 then (if b 6 = 0 then (if b 7 = 0 then (if b 8 = 0 then (if b 9 = 0 then [false, false,
    false, false, false, false, false, false, false] else [false, false, false, false, false,
    false, false, false, false]) else (if b 9 = 0 then [false, false, false, false, false,
    false, false, false, false] else [false, false, false, false, false, false, false, false,
    false])) else (if b 8 = 0 then (if b 9 = 0 then [false, false, false, false, false, false,
    false, false, false] else [false, false, false, false, false, false, false, false, false])
    else (if b 9 = 0 then [false, false, false, false, false, false, false, false, false] else
    [false, false, false, false, false, false, false, false, false]))) else (if b 7 = 0 then
    (if b 8 = 0 then (if b 9 = 0 then [false, false, false, false, false, false, false, false,
    false] else [false, false, false, false, false, false, false, false, false]) else (if b 9 =
    0 then [false, false, false, false, false, false, false, false, false] else [false, false,
    false, false, false, false, false, false, false])) else (if b 8 = 0 then (if b 9 = 0 then
    [false, false, false, false, false, false, false, false, false] else [false, false, false,
    false, false, false, false, false, false]) else (if b 9 = 0 then [false, false, false,
    false, false, false, false, false, false] else [false, false, false, false, false, false,
    false, false, false])))) else (if b 6 = 0 then (if b 7 = 0 then (if b 8 = 0 then (if b 9 =
    0 then [false, false, false, false, false, false, false, false, false] else [false, false,
    false, false, false, false, false, false, false]) else (if b 9 = 0 then [false, false,
    false, false, false, false, false, false, false] else [false, false, false, false, false,
    false, false, false, false])) else (if b 8 = 0 then (if b 9 = 0 then [false, false, false,
    false, false, false, false, false, false] else [false, false, false, false, false, false,
    false, false, false]) else (if b 9 = 0 then [false, false, false, false, false, false,
    false, false, false] else [false, false, false, false, false, false, false, false,
    false]))) else (if b 7 = 0 then (if b 8 = 0 then (if b 9 = 0 then [false, false, false,
    false, false, false, false, false, false] else [false, false, false, false, false, false,
    false, false, false]) else (if b 9 = 0 then [false, false, false, false, false, false,
    false, false, false] else [false, false, false, false, false, false, false, false, false]))
    else (if b 8 = 0 then (if b 9 = 0 then [false, false, false, false, false, false, false,
    false, false] else [false, false, false, false, false, false, false, false, false]) else
    (if b 9 = 0 then [false, false, false, false, false, false, false, false, false] else
    [false, false, false, false, false, false, false, false, false]))))) else (if b 5 = 0 then
    (if b 6 = 0 then (if b 7 = 0 then (if b 8 = 0 then (if b 9 = 0 then [false, false, false,
    false, false, false, false, false, false] else [false, false, false, false, false, false,
    false, false, false]) else (if b 9 = 0 then [false, false, false, false, false, false,
    false, false, false] else [false, false, false, false, false, false, false, false, false]))
    else (if b 8 = 0 then (if b 9 = 0 then [false, false, false, false, false, false, false,
    false, false] else [false, false, false, false, false, false, false, false, false]) else
    (if b 9 = 0 then [false, false, false, false, false, false, false, false, false] else
    [false, false, false, false, false, false, false, false, false]))) else (if b 7 = 0 then
    (if b 8 = 0 then (if b 9 = 0 then [false, false, false, false, false, false, false, false,
    false] else [false, false, false, false, false, false, false, false, false]) else (if b 9 =
    0 then [false, false, false, false, false, false, false, false, false] else [false, false,
    false, false, false, false, false, false, false])) else (if b 8 = 0 then (if b 9 = 0 then
    [false, false, false, false, false, false, false, false, false] else [false, false, false,
    false, false, false, false, false, false]) else (if b 9 = 0 then [false, false, false,
    false, false, false, false, false, false] else [false, false, false, false, false, false,
    false, false, false])))) else (if b 6 = 0 then (if b 7 = 0 then (if b 8 = 0 then (if b 9 =
    0 then [false, false, false, false, false, false, false, false, false] else [false, false,
    false, false, false, false, false, false, false]) else (if b 9 = 0 then [false, false,
    false, false, false, false, false, false, false] else [false, false, false, false, false,
    false, false, false, false])) else (if b 8 = 0 then (if b 9 = 0 then [false, false, false,
    false, false, false, false, false, false] else [false, false, false, false, false, false,
    false, false, false]) else (if b 9 = 0 then [false, false, false, false, false, false,
    false, false, false] else [false, false, false, false, false, false, false, false,
    false]))) else (if b 7 = 0 then (if b 8 = 0 then (if b 9 = 0 then [false, false, false,
    false, false, false, false, false, false] else [false, false, false, false, false, false,
    false, false, false]) else (if b 9 = 0 then [false, false, false, false, false, false,
    false, false, false] else [false, false, false, false, false, false, false, false, false]))
    else (if b 8 = 0 then (if b 9 = 0 then [false, false, false, false, false, false, false,
    false, false] else [false, false, false, false, false, false, false, false, false]) else
    (if b 9 = 0 then [false, false, false, false, false, false, false, false, false] else
    [false, false, false, false, false, false, false, false, false])))))) else (if b 4 = 0 then
    (if b 5 = 0 then (if b 6 = 0 then (if b 7 = 0 then (if b 8 = 0 then (if b 9 = 0 then
    [false, false, false, false, false, false, false, false, false] else [false, false, false,
    false, false, false, false, false, false]) else (if b 9 = 0 then [false, false, false,
    false, false, false, false, false, false] else [false, false, false, false, false, false,
    false, false, false])) else (if b 8 = 0 then (if b 9 = 0 then [false, false, false, false,
    false, false, false, false, false] else [false, false, false, false, false, false, false,
    false, false]) else (if b 9 = 0 then [false, false, false, false, false, false, false,
    false, false] else [false, false, false, false, false, false, false, false, false]))) else
    (if b 7 = 0 then (if b 8 = 0 then (if b 9 = 0 then [false, false, false, false, false,
    false, false, false, false] else [false, false, false, false, false, false, false, false,
    false]) else (if b 9 = 0 then [false, false, false, false, false, false, false, false,
    false] else [false, false, false, false, false, false, false, false, false])) else (if b 8
    = 0 then (if b 9 = 0 then [false, false, false, false, false, false, false, false, false]
    else [false, false, false, false, false, false, false, false, false]) else (if b 9 = 0 then
    [false, false, false, false, false, false, false, false, false] else [false, false, false,
    false, false, false, false, false, false])))) else (if b 6 = 0 then (if b 7 = 0 then (if b
    8 = 0 then (if b 9 = 0 then [false, false, false, false, false, false, false, false, false]
    else [false, false, false, false, false, false, false, false, false]) else (if b 9 = 0 then
    [false, false, false, false, false, false, false, false, false] else [false, false, false,
    false, false, false, false, false, false])) else (if b 8 = 0 then (if b 9 = 0 then [false,
    false, false, false, false, false, false, false, false] else [false, false, false, false,
    false, false, false, false, false]) else (if b 9 = 0 then [false, false, false, false,
    false, false, false, false, false] else [false, false, false, false, false, false, false,
    false, false]))) else (if b 7 = 0 then (if b 8 = 0 then (if b 9 = 0 then [false, false,
    false, false, false, false, false, false, false] else [false, false, false, false, false,
    false, false, false, false]) else (if b 9 = 0 then [false, false, false, false, false,
    false, false, false, false] else [false, false, false, false, false, false, false, false,
    false])) else (if b 8 = 0 then (if b 9 = 0 then [false, false, false, false, false, false,
    false, false, false] else [false, false, false, false, false, false, false, false, false])
    else (if b 9 = 0 then [false, false, false, false, false, false, false, false, false] else
    [false, false, false, false, false, false, false, false, false]))))) else (if b 5 = 0 then
    (if b 6 = 0 then (if b 7 = 0 then (if b 8 = 0 then (if b 9 = 0 then [false, false, false,
    false, false, false, false, false, false] else [false, false, false, false, false, false,
    false, false, false]) else (if b 9 = 0 then [false, false, false, false, false, false,
    false, false, false] else [false, false, false, false, false, false, false, false, false]))
    else (if b 8 = 0 then (if b 9 = 0 then [false, false, false, false, false, false, false,
    false, false] else [false, false, false, false, false, false, false, false, false]) else
    (if b 9 = 0 then [false, false, false, false, false, false, false, false, false] else
    [false, false, false, false, false, false, false, false, false]))) else (if b 7 = 0 then
    (if b 8 = 0 then (if b 9 = 0 then [false, false, false, false, false, false, false, false,
    false] else [false, false, false, false, false, false, false, false, false]) else (if b 9 =
    0 then [false, false, false, false, false, false, false, false, false] else [false, false,
    false, false, false, false, false, false, false])) else (if b 8 = 0 then (if b 9 = 0 then
    [false, false, false, false, false, false, false, false, false] else [false, false, false,
    false, false, false, false, false, false]) else (if b 9 = 0 then [false, false, false,
    false, false, false, false, false, false] else [false, false, false, false, false, false,
    false, false, false])))) else (if b 6 = 0 then (if b 7 = 0 then (if b 8 = 0 then (if b 9 =
    0 then [false, false, false, false, false, false, false, false, false] else [false, false,
    false, false, false, false, false, false, false]) else (if b 9 = 0 then [false, false,
    false, false, false, false, false, false, false] else [false, false, false, false, false,
    false, false, false, false])) else (if b 8 = 0 then (if b 9 = 0 then [false, false, false,
    false, false, false, false, false, false] else [false, false, false, false, false, false,
    false, false, false]) else (if b 9 = 0 then [false, false, false, false, false, false,
    false, false, false] else [false, false, false, false, false, false, false, false,
    false]))) else (if b 7 = 0 then (if b 8 = 0 then (if b 9 = 0 then [false, false, false,
    false, false, false, false, false, false] else [false, false, false, false, false, false,
    false, false, false]) else (if b 9 = 0 then [false, false, false, false, false, false,
    false, false, false] else [false, false, false, false, false, false, false, false, false]))
    else (if b 8 = 0 then (if b 9 = 0 then [false, false, false, false, false, false, false,
    false, false] else [false, false, false, false, false, false, false, false, false]) else
    (if b 9 = 0 then [false, false, false, false, false, false, false, false, false] else
    [false, false, false, false, false, false, false, false, false]))))))))) else (if b 1 = 0
    then (if b 2 = 0 then (if b 3 = 0 then (if b 4 = 0 then (if b 5 = 0 then (if b 6 = 0 then
    (if b 7 = 0 then (if b 8 = 0 then (if b 9 = 0 then [false, false, false, false, false,
    false, false, false, false] else [false, false, false, false, false, false, false, false,
    false]) else (if b 9 = 0 then [false, false, false, false, false, false, false, false,
    false] else [false, false, false, false, false, false, false, false, false])) else (if b 8
    = 0 then (if b 9 = 0 then [false, false, false, false, false, false, false, false, false]
    else [false, false, false, false, false, false, false, false, false]) else (if b 9 = 0 then
    [false, false, false, false, false, false, false, false, false] else [false, false, false,
    false, false, false, false, false, false]))) else (if b 7 = 0 then (if b 8 = 0 then (if b 9
    = 0 then [false, false, false, false, false, false, false, false, false] else [false,
    false, false, false, false, false, false, false, false]) else (if b 9 = 0 then [false,
    false, false, false, false, false, false, false, false] else [false, false, false, false,
    false, false, false, false, false])) else (if b 8 = 0 then (if b 9 = 0 then [false, false,
    false, false, false, false, false, false, false] else [false, false, false, false, false,
    false, false, false, false]) else (if b 9 = 0 then [false, false, false, false, false,
    false, false, false, false] else [false, false, false, false, false, false, false, false,
    false])))) else (if b 6 = 0 then (if b 7 = 0 then (if b 8 = 0 then (if b 9 = 0 then [false,
    false, false, false, false, false, false, false, false] else [false, false, false, false,
    false, false, false, false, false]) else (if b 9 = 0 then [false, false, false, false,
    false, false, false, false, false] else [false, false, false, false, false, false, false,
    false, false])) else (if b 8 = 0 then (if b 9 = 0 then [false, false, false, false, false,
    false, false, false, false] else [false, false, false, false, false, false, false, false,
    false]) else (if b 9 = 0 then [false, false, false, false, false, false, false, false,
    false] else [false, false, false, false, false, false, false, false, false]))) else (if b 7
    = 0 then (if b 8 = 0 then (if b 9 = 0 then [false, false, false, false, false, false,
    false, false, false] else [false, false, false, false, false, false, false, false, false])
    else (if b 9 = 0 then [false, false, false, false, false, false, false, false, false] else
    [false, false, false, false, false, false, false, false, false])) else (if b 8 = 0 then (if
    b 9 = 0 then [false, false, false, false, false, false, false, false, false] else [false,
    false, false, false, false, false, false, false, false]) else (if b 9 = 0 then [false,
    false, false, false, false, false, false, false, false] else [false, false, false, false,
    false, false, false, false, false]))))) else (if b 5 = 0 then (if b 6 = 0 then (if b 7 = 0
    then (if b 8 = 0 then (if b 9 = 0 then [false, false, false, false, false, false, false,
    false, false] else [false, false, false, false, false, false, false, false, false]) else
    (if b 9 = 0 then [false, false, false, false, false, false, false, false, false] else
    [false, false, false, false, false, false, false, false, false])) else (if b 8 = 0 then (if
    b 9 = 0 then [false, false, false, false, false, false, false, false, false] else [false,
    false, false, false, false, false, false, false, false]) else (if b 9 = 0 then [false,
    false, false, false, false, false, false, false, false] else [false, false, false, false,
    false, false, false, false, false]))) else (if b 7 = 0 then (if b 8 = 0 then (if b 9 = 0
    then [false, false, false, false, false, false, false, false, false] else [false, false,
    false, false, false, false, false, false, false]) else (if b 9 = 0 then [false, false,
    false, false, false, false, false, false, false] else [false, false, false, false, false,
    false, false, false, false])) else (if b 8 = 0 then (if b 9 = 0 then [false, false, false,
    false, false, false, false, false, false] else [false, false, false, false, false, false,
    false, false, false]) else (if b 9 = 0 then [false, false, false, false, false, false,
    false, false, false] else [false, false, false, false, false, false, false, false,
    false])))) else (if b 6 = 0 then (if b 7 = 0 then (if b 8 = 0 then (if b 9 = 0 then [false,
    false, false, false, false, false, false, false, false] else [false, false, false, false,
    false, false, false, false, false]) else (if b 9 = 0 then [false, false, false, false,
    false, false, false, false, false] else [false, false, false, false, false, false, false,
    false, false])) else (if b 8 = 0 then (if b 9 = 0 then [false, false, false, false, false,
    false, false, false, false] else [false, false, false, false, false, false, false, false,
    false]) else (if b 9 = 0 then [false, false, false, false, false, false, false, false,
    false] else [false, false, false, false, false, false, false, false, false]))) else (if b 7
    = 0 then (if b 8 = 0 then (if b 9 = 0 then [false, false, false, false, false, false,
    false, false, false] else [false, false, false, false, false, false, false, false, false])
    else (if b 9 = 0 then [false, false, false, false, false, false, false, false, false] else
    [false, false, false, false, false, false, false, false, false])) else (if b 8 = 0 then (if
    b 9 = 0 then [false, false, false, false, false, false, false, false, false] else [false,
    false, false, false, false, false, false, false, false]) else (if b 9 = 0 then [false,
    false, false, false, false, false, false, false, false] else [false, false, false, false,
    false, false, false, false, false])))))) else (if b 4 = 0 then (if b 5 = 0 then (if b 6 = 0
    then (if b 7 = 0 then (if b 8 = 0 then (if b 9 = 0 then [false, false, false, false, false,
    false, false, false, false] else [false, false, false, false, false, false, false, false,
    false]) else (if b 9 = 0 then [false, false, false, false, false, false, false, false,
    false] else [false, false, false, false, false, false, false, false, false])) else (if b 8
    = 0 then (if b 9 = 0 then [false, false, false, false, false, false, false, false, false]
    else [false, false, false, false, false, false, false, false, false]) else (if b 9 = 0 then
    [false, false, false, false, false, false, false, false, false] else [false, false, false,
    false, false, false, false, false, false]))) else (if b 7 = 0 then (if b 8 = 0 then (if b 9
    = 0 then [false, false, false, false, false, false, false, false, false] else [false,
    false, false, false, false, false, false, false, false]) else (if b 9 = 0 then [false,
    false, false, false, false, false, false, false, false] else [false, false, false, false,
    false, false, false, false, false])) else (if b 8 = 0 then (if b 9 = 0 then [false, false,
    false, false, false, false, false, false, false] else [false, false, false, false, false,
    false, false, false, false]) else (if b 9 = 0 then [false, false, false, false, false,
    false, false, false, false] else [false, false, false, false, false, false, false, false,
    false])))) else (if b 6 = 0 then (if b 7 = 0 then (if b 8 = 0 then (if b 9 = 0 then [false,
    false, false, false, false, false, false, false, false] else [false, false, false, false,
    false, false, false, false, false]) else (if b 9 = 0 then [false, false, false, false,
    false, false, false, false, false] else [false, false, false, false, false, false, false,
    false, false])) else (if b 8 = 0 then (if b 9 = 0 then [false, false, false, false, false,
    false, false, false, false] else [false, false, false, false, false, false, false, false,
    false]) else (if b 9 = 0 then [false, false, false, false, false, false, false, false,
    false] else [false, false, false, false, false, false, false, false, false]))) else (if b 7
    = 0 then (if b 8 = 0 then (if b 9 = 0 then [false, false, false, false, false, false,
    false, false, false] else [false, false, false, false, false, false, false, false, false])
    else (if b 9 = 0 then [false, false, false, false, false, false, false, false, false] else
    [false, false, false, false, false, false, false, false, false])) else (if b 8 = 0 then (if
    b 9 = 0 then [false, false, false, false, false, false, false, false, false] else [false,
    false, false, false, false, false, false, false, false]) else (if b 9 = 0 then [false,
    false, false, false, false, false, false, false, false] else [false, false, false, false,
    false, false, false, false, false]))))) else (if b 5 = 0 then (if b 6 = 0 then (if b 7 = 0
    then (if b 8 = 0 then (if b 9 = 0 then [false, false, false, false, false, false, false,
    false, false] else [false, false, false, false, false, false, false, false, false]) else
    (if b 9 = 0 then [false, false, false, false, false, false, false, false, false] else
    [false, false, false, false, false, false, false, false, false])) else (if b 8 = 0 then (if
    b 9 = 0 then [false, false, false, false, false, false, false, false, false] else [false,
    false, false, false, false, false, false, false, false]) else (if b 9 = 0 then [false,
    false, false, false, false, false, false, false, false] else [false, false, false, false,
    false, false, false, false, false]))) else (if b 7 = 0 then (if b 8 = 0 then (if b 9 = 0
    then [false, false, false, false, false, false, false, false, false] else [false, false,
    false, false, false, false, false, false, false]) else (if b 9 = 0 then [false, false,
    false, false, false, false, false, false, false] else [false, false, false, false, false,
    false, false, false, false])) else (if b 8 = 0 then (if b 9 = 0 then [false, false, false,
    false, false, false, false, false, false] else [false, false, false, false, false, false,
    false, false, false]) else (if b 9 = 0 then [false, false, false, false, false, false,
    false, false, false] else [false, false, false, false, false, false, false, false,
    false])))) else (if b 6 = 0 then (if b 7 = 0 then (if b 8 = 0 then (if b 9 = 0 then [false,
    false, false, false, false, false, false, false, false] else [false, false, false, false,
    false, false, false, false, false]) else (if b 9 = 0 then [false, false, false, false,
    false, false, false, false, false] else [false, false, false, false, false, false, false,
    false, false])) else (if b 8 = 0 then (if b 9 = 0 then [false, false, false, false, false,
    false, false, false, false] else [false, false, false, false, false, false, false, false,
    false]) else (if b 9 = 0 then [false, false, false, false, false, false, false, false,
    false] else [false, false, false, false, false, false, false, false, false]))) else (if b 7
    = 0 then (if b 8 = 0 then (if b 9 = 0 then [false, false, false, false, false, false,
    false, false, false] else [false, false, false, false, false, false, false, false, false])
    else (if b 9 = 0 then [false, false, false, false, false, false, false, false, false] else
    [false, false, false, false, false, false, false, false, false])) else (if b 8 = 0 then (if
    b 9 = 0 then [false, false, false, false, false, false, false, false, false] else [false,
    false, false, false, false, false, false, false, false]) else (if b 9 = 0 then [false,
    false, false, false, false, false, false, false, false] else [false, false, false, false,
    false, false, false, false, false]))))))) else (if b 3 = 0 then (if b 4 = 0 then (if b 5 =
    0 then (if b 6 = 0 then (if b 7 = 0 then (if b 8 = 0 then (if b 9 = 0 then [false, false,
    false, false, false, false, false, false, false] else [false, false, false, false, false,
    false, false, false, false]) else (if b 9 = 0 then [false, false, false, false, false,
    false, false, false, false] else [false, false, false, false, false, false, false, false,
    false])) else (if b 8 = 0 then (if b 9 = 0 then [false, false, false, false, false, false,
    false, false, false] else [false, false, false, false, false, false, false, false, false])
    else (if b 9 = 0 then [false, false, false, false, false, false, false, false, false] else
    [false, false, false, false, false, false, false, false, false]))) else (if b 7 = 0 then
    (if b 8 = 0 then (if b 9 = 0 then [false, false, false, false, false, false, false, false,
    false] else [false, false, false, false, false, false, false, false, false]) else (if b 9 =
    0 then [false, false, false, false, false, false, false, false, false] else [false, false,
    false, false, false, false, false, false, false])) else (if b 8 = 0 then (if b 9 = 0 then
    [false, false, false, false, false, false, false, false, false] else [false, false, false,
    false, false, false, false, false, false]) else (if b 9 = 0 then [false, false, false,
    false, false, false, false, false, false] else [false, false, false, false, false, false,
    false, false, false])))) else (if b 6 = 0 then (if b 7 = 0 then (if b 8 = 0 then (if b 9 =
    0 then [false, false, false, false, false, false, false, false, false] else [false, false,
    false, false, false, false, false, false, false]) else (if b 9 = 0 then [false, false,
    false, false, false, false, false, false, false] else [false, false, false, false, false,
    false, false, false, false])) else (if b 8 = 0 then (if b 9 = 0 then [false, false, false,
    false, false, false, false, false, false] else [false, false, false, false, false, false,
    false, false, false]) else (if b 9 = 0 then [false, false, false, false, false, false,
    false, false, false] else [false, false, false, false, false, false, false, false,
    false]))) else (if b 7 = 0 then (if b 8 = 0 then (if b 9 = 0 then [false, false, false,
    false, false, false, false, false, false] else [false, false, false, false, false, false,
    false, false, false]) else (if b 9 = 0 then [false, false, false, false, false, false,
    false, false, false] else [false, false, false, false, false, false, false, false, false]))
    else (if b 8 = 0 then (if b 9 = 0 then [false, false, false, false, false, false, false,
    false, false] else [false, false, false, false, false, false, false, false, false]) else
    (if b 9 = 0 then [false, false, false, false, false, false, false, false, false] else
    [false, false, false, false, false, false, false, false, false]))))) else (if b 5 = 0 then
    (if b 6 = 0 then (if b 7 = 0 then (if b 8 = 0 then (if b 9 = 0 then [false, false, false,
    false, false, false, false, false, false] else [false, false, false, false, false, false,
    false, false, false]) else (if b 9 = 0 then [false, false, false, false, false, false,
    false, false, false] else [false, false, false, false, false, false, false, false, false]))
    else (if b 8 = 0 then (if b 9 = 0 then [false, false, false, false, false, false, false,
    false, false] else [false, false, false, false, false, false, false, false, false]) else
    (if b 9 = 0 then [false, false, false, false, false, false, false, false, false] else
    [false, false, false, false, false, false, false, false, false]))) else (if b 7 = 0 then
    (if b 8 = 0 then (if b 9 = 0 then [false, false, false, false, false, false, false, false,
    false] else [false, false, false, false, false, false, false, false, false]) else (if b 9 =
    0 then [false, false, false, false, false, false, false, false, false] else [false, false,
    false, false, false, false, false, false, false])) else (if b 8 = 0 then (if b 9 = 0 then
    [false, false, false, false, false, false, false, false, false] else [false, false, false,
    false, false, false, false, false, false]) else (if b 9 = 0 then [false, false, false,
    false, false, false, false, false, false] else [false, false, false, false, false, false,
    false, false, false])))) else (if b 6 = 0 then (if b 7 = 0 then (if b 8 = 0 then (if b 9 =
    0 then [false, false, false, false, false, false, false, false, false] else [false, false,
    false, false, false, false, false, false, false]) else (if b 9 = 0 then [false, false,
    false, false, false, false, false, false, false] else [false, false, false, false, false,
    false, false, false, false])) else (if b 8 = 0 then (if b 9 = 0 then [false, false, false,
    false, false, false, false, false, false] else [false, false, false, false, false, false,
    false, false, false]) else (if b 9 = 0 then [false, false, false, false, false, false,
    false, false, false] else [false, false, false, false, false, false, false, false,
    false]))) else (if b 7 = 0 then (if b 8 = 0 then (if b 9 = 0 then [false, false, false,
    false, false, false, false, false, false] else [false, false, false, false, false, false,
    false, false, false]) else (if b 9 = 0 then [false, false, false, false, false, false,
    false, false, false] else [false, false, false, false, false, false, false, false, false]))
    else (if b 8 = 0 then (if b 9 = 0 then [false, false, false, false, false, false, false,
    false, false] else [false, false, false, false, false, false, false, false, false]) else
    (if b 9 = 0 then [false, false, false, false, false, false, false, false, false] else
    [false, false, false, false, false, false, false, false, false])))))) else (if b 4 = 0 then
    (if b 5 = 0 then (if b 6 = 0 then (if b 7 = 0 then (if b 8 = 0 then (if b 9 = 0 then
    [false, false, false, false, false, false, false, false, false] else [false, false, false,
    false, false, false, false, false, false]) else (if b 9 = 0 then [false, false, false,
    false, false, false, false, false, false] else [false, false, false, false, false, false,
    false, false, false])) else (if b 8 = 0 then (if b 9 = 0 then [false, false, false, false,
    false, false, false, false, false] else [false, false, false, false, false, false, false,
    false, false]) else (if b 9 = 0 then [false, false, false, false, false, false, false,
    false, false] else [false, false, false, false, false, false, false, false, false]))) else
    (if b 7 = 0 then (if b 8 = 0 then (if b 9 = 0 then [false, false, false, false, false,
    false, false, false, false] else [false, false, false, false, false, false, false, false,
    false]) else (if b 9 = 0 then [false, false, false, false, false, false, false, false,
    false] else [false, false, false, false, false, false, false, false, false])) else (if b 8
    = 0 then (if b 9 = 0 then [false, false, false, false, false, false, false, false, false]
    else [false, false, false, false, false, false, false, false, false]) else (if b 9 = 0 then
    [false, false, false, false, false, false, false, false, false] else [false, false, false,
    false, false, false, false, false, false])))) else (if b 6 = 0 then (if b 7 = 0 then (if b
    8 = 0 then (if b 9 = 0 then [false, false, false, false, false, false, false, false, false]
    else [false, false, false, false, false, false, false, false, false]) else (if b 9 = 0 then
    [false, false, false, false, false, false, false, false, false] else [false, false, false,
    false, false, false, false, false, false])) else (if b 8 = 0 then (if b 9 = 0 then [false,
    false, false, false, false, false, false, false, false] else [false, false, false, false,
    false, false, false, false, false]) else (if b 9 = 0 then [false, false, false, false,
    false, false, false, false, false] else [false, false, false, false, false, false, false,
    false, false]))) else (if b 7 = 0 then (if b 8 = 0 then (if b 9 = 0 then [false, false,
    false, false, false, false, false, false, false] else [false, false, false, false, false,
    false, false, false, false]) else (if b 9 = 0 then [false, false, false, false, false,
    false, false, false, false] else [false, false, false, false, false, false, false, false,
    false])) else (if b 8 = 0 then (if b 9 = 0 then [false, false, false, false, false, false,
    false, false, false] else [false, false, false, false, false, false, false, false, false])
    else (if b 9 = 0 then [false, false, false, false, false, false, false, false, false] else
    [false, false, false, false, false, false, false, false, false]))))) else (if b 5 = 0 then
    (if b 6 = 0 then (if b 7 = 0 then (if b 8 = 0 then (if b 9 = 0 then [false, false, false,
    false, false, false, false, false, false] else [false, false, false, false, false, false,
    false, false, false]) else (if b 9 = 0 then [false, false, false, false, false, false,
    false, false, false] else [false, false, false, false, false, false, false, false, false]))
    else (if b 8 = 0 then (if b 9 = 0 then [false, false, false, false, false, false, false,
    false, false] else [false, false, false, false, false, false, false, false, false]) else
    (if b 9 = 0 then [false, false, false, false, false, false, false, false, false] else
    [false, false, false, false, false, false, false, false, false]))) else (if b 7 = 0 then
    (if b 8 = 0 then (if b 9 = 0 then [false, false, false, false, false, false, false, false,
    false] else [false, false, false, false, false, false, false, false, false]) else (if b 9 =
    0 then [false, false, false, false, false, false, false, false, false] else [false, false,
    false, false, false, false, false, false, false])) else (if b 8 = 0 then (if b 9 = 0 then
    [false, false, false, false, false, false, false, false, false] else [false, false, false,
    false, false, false, false, false, false]) else (if b 9 = 0 then [false, false, false,
    false, false, false, false, false, false] else [false, false, false, false, false, false,
    false, false, false])))) else (if b 6 = 0 then (if b 7 = 0 then (if b 8 = 0 then (if b 9 =
    0 then [false, false, false, false, false, false, false, false, false] else [false, false,
    false, false, false, false, false, false, false]) else (if b 9 = 0 then [false, false,
    false, false, false, false, false, false, false] else [false, false, false, false, false,
    false, false, false, false])) else (if b 8 = 0 then (if b 9 = 0 then [false, false, false,
    false, false, false, false, false, false] else [false, false, false, false, false, false,
    false, false, false]) else (if b 9 = 0 then [false, false, false, false, false, false,
    false, false, false] else [false, false, false, false, false, false, false, false,
    false]))) else (if b 7 = 0 then (if b 8 = 0 then (if b 9 = 0 then [false, false, false,
    false, false, false, false, false, false] else [false, false, false, false, false, false,
    false, false, false]) else (if b 9 = 0 then [false, false, false, false, false, false,
    false, false, false] else [false, false, false, false, false, false, false, false, false]))
    else (if b 8 = 0 then (if b 9 = 0 then [false, false, false, false, false, false, false,
    false, false] else [false, false, false, false, false, false, false, false, false]) else
    (if b 9 = 0 then [false, false, false, false, false, false, false, false, false] else
    [false, false, false, false, false, false, false, false, false])))))))) else (if b 2 = 0
    then (if b 3 = 0 then (if b 4 = 0 then (if b 5 = 0 then (if b 6 = 0 then (if b 7 = 0 then
    (if b 8 = 0 then (if b 9 = 0 then [true, false, false, false, false, false, false, true,
    false] else [false, true, false, false, false, false, true, true, true]) else (if b 9 = 0
    then [false, false, false, false, false, false, true, true, false] else [true, true, false,
    false, false, false, false, true, true])) else (if b 8 = 0 then (if b 9 = 0 then [false,
    false, false, false, false, true, false, true, false] else [true, true, false, false,
    false, true, true, true, true]) else (if b 9 = 0 then [true, false, false, false, false,
    true, true, true, false] else [false, true, false, false, false, true, false, true,
    true]))) else (if b 7 = 0 then (if b 8 = 0 then (if b 9 = 0 then [false, false, false,
    false, true, false, false, true, false] else [true, true, false, false, true, false, true,
    true, true]) else (if b 9 = 0 then [true, false, false, false, true, false, true, true,
    false] else [false, true, false, false, true, false, false, true, true])) else (if b 8 = 0
    then (if b 9 = 0 then [true, false, false, false, true, true, false, true, false] else
    [false, true, false, false, true, true, true, true, true]) else (if b 9 = 0 then [false,
    false, false, false, true, true, true, true, false] else [true, true, false, false, true,
    true, false, true, true])))) else (if b 6 = 0 then (if b 7 = 0 then (if b 8 = 0 then (if b
    9 = 0 then [false, false, false, true, false, false, false, true, false] else [true, true,
    false, true, false, false, true, true, true]) else (if b 9 = 0 then [true, false, false,
    true, false, false, true, true, false] else [false, true, false, true, false, false, false,
    true, true])) else (if b 8 = 0 then (if b 9 = 0 then [true, false, false, true, false,
    true, false, true, false] else [false, true, false, true, false, true, true, true, true])
    else (if b 9 = 0 then [false, false, false, true, false, true, true, true, false] else
    [true, true, false, true, false, true, false, true, true]))) else (if b 7 = 0 then (if b 8
    = 0 then (if b 9 = 0 then [true, false, false, true, true, false, false, true, false] else
    [false, true, false, true, true, false, true, true, true]) else (if b 9 = 0 then [false,
    false, false, true, true, false, true, true, false] else [true, true, false, true, true,
    false, false, true, true])) else (if b 8 = 0 then (if b 9 = 0 then [false, false, false,
    true, true, true, false, true, false] else [true, true, false, true, true, true, true,
    true, true]) else (if b 9 = 0 then [true, false, false, true, true, true, true, true,
    false] else [false, true, false, true, true, true, false, true, true]))))) else (if b 5 = 0
    then (if b 6 = 0 then (if b 7 = 0 then (if b 8 = 0 then (if b 9 = 0 then [false, false,
    true, false, false, false, false, true, false] else [true, true, true, false, false, false,
    true, true, true]) else (if b 9 = 0 then [true, false, true, false, false, false, true,
    true, false] else [false, true, true, false, false, false, false, true, true])) else (if b
    8 = 0 then (if b 9 = 0 then [true, false, true, false, false, true, false, true, false]
    else [false, true, true, false, false, true, true, true, true]) else (if b 9 = 0 then
    [false, false, true, false, false, true, true, true, false] else [true, true, true, false,
    false, true, false, true, true]))) else (if b 7 = 0 then (if b 8 = 0 then (if b 9 = 0 then
    [true, false, true, false, true, false, false, true, false] else [false, true, true, false,
    true, false, true, true, true]) else (if b 9 = 0 then [false, false, true, false, true,
    false, true, true, false] else [true, true, true, false, true, false, false, true, true]))
    else (if b 8 = 0 then (if b 9 = 0 then [false, false, true, false, true, true, false, true,
    false] else [true, true, true, false, true, true, true, true, true]) else (if b 9 = 0 then
    [true, false, true, false, true, true, true, true, false] else [false, true, true, false,
    true, true, false, true, true])))) else (if b 6 = 0 then (if b 7 = 0 then (if b 8 = 0 then
    (if b 9 = 0 then [true, false, true, true, false, false, false, true, false] else [false,
    true, true, true, false, false, true, true, true]) else (if b 9 = 0 then [false, false,
    true, true, false, false, true, true, false] else [true, true, true, true, false, false,
    false, true, true])) else (if b 8 = 0 then (if b 9 = 0 then [false, false, true, true,
    false, true, false, true, false] else [true, true, true, true, false, true, true, true,
    true]) else (if b 9 = 0 then [true, false, true, true, false, true, true, true, false] else
    [false, true, true, true, false, true, false, true, true]))) else (if b 7 = 0 then (if b 8
    = 0 then (if b 9 = 0 then [false, false, true, true, true, false, false, true, false] else
    [true, true, true, true, true, false, true, true, true]) else (if b 9 = 0 then [true,
    false, true, true, true, false, true, true, false] else [false, true, true, true, true,
    false, false, true, true])) else (if b 8 = 0 then (if b 9 = 0 then [true, false, true,
    true, true, true, false, true, false] else [false, true, true, true, true, true, true,
    true, true]) else (if b 9 = 0 then [false, false, true, true, true, true, true, true,
    false] else [true, true, true, true, true, true, false, true, true])))))) else (if b 4 = 0
    then (if b 5 = 0 then (if b 6 = 0 then (if b 7 = 0 then (if b 8 = 0 then (if b 9 = 0 then
    [false, true, false, false, false, false, false, true, false] else [true, false, false,
    false, false, false, true, true, true]) else (if b 9 = 0 then [true, true, false, false,
    false, false, true, true, false] else [false, false, false, false, false, false, false,
    true, true])) else (if b 8 = 0 then (if b 9 = 0 then [true, true, false, false, false,
    true, false, true, false] else [false, false, false, false, false, true, true, true, true])
    else (if b 9 = 0 then [false, true, false, false, false, true, true, true, false] else
    [true, false, false, false, false, true, false, true, true]))) else (if b 7 = 0 then (if b
    8 = 0 then (if b 9 = 0 then [true, true, false, false, true, false, false, true, false]
    else [false, false, false, false, true, false, true, true, true]) else (if b 9 = 0 then
    [false, true, false, false, true, false, true, true, false] else [true, false, false,
    false, true, false, false, true, true])) else (if b 8 = 0 then (if b 9 = 0 then [false,
    true, false, false, true, true, false, true, false] else [true, false, false, false, true,
    true, true, true, true]) else (if b 9 = 0 then [true, true, false, false, true, true, true,
    true, false] else [false, false, false, false, true, true, false, true, true])))) else (if
    b 6 = 0 then (if b 7 = 0 then (if b 8 = 0 then (if b 9 = 0 then [true, true, false, true,
    false, false, false, true, false] else [false, false, false, true, false, false, true,
    true, true]) else (if b 9 = 0 then [false, true, false, true, false, false, true, true,
    false] else [true, false, false, true, false, false, false, true, true])) else (if b 8 = 0
    then (if b 9 = 0 then [false, true, false, true, false, true, false, true, false] else
    [true, false, false, true, false, true, true, true, true]) else (if b 9 = 0 then [true,
    true, false, true, false, true, true, true, false] else [false, false, false, true, false,
    true, false, true, true]))) else (if b 7 = 0 then (if b 8 = 0 then (if b 9 = 0 then [false,
    true, false, true, true, false, false, true, false] else [true, false, false, true, true,
    false, true, true, true]) else (if b 9 = 0 then [true, true, false, true, true, false,
    true, true, false] else [false, false, false, true, true, false, false, true, true])) else
    (if b 8 = 0 then (if b 9 = 0 then [true, true, false, true, true, true, false, true, false]
    else [false, false, false, true, true, true, true, true, true]) else (if b 9 = 0 then
    [false, true, false, true, true, true, true, true, false] else [true, false, false, true,
    true, true, false, true, true]))))) else (if b 5 = 0 then (if b 6 = 0 then (if b 7 = 0 then
    (if b 8 = 0 then (if b 9 = 0 then [true, true, true, false, false, false, false, true,
    false] else [false, false, true, false, false, false, true, true, true]) else (if b 9 = 0
    then [false, true, true, false, false, false, true, true, false] else [true, false, true,
    false, false, false, false, true, true])) else (if b 8 = 0 then (if b 9 = 0 then [false,
    true, true, false, false, true, false, true, false] else [true, false, true, false, false,
    true, true, true, true]) else (if b 9 = 0 then [true, true, true, false, false, true, true,
    true, false] else [false, false, true, false, false, true, false, true, true]))) else (if b
    7 = 0 then (if b 8 = 0 then (if b 9 = 0 then [false, true, true, false, true, false, false,
    true, false] else [true, false, true, false, true, false, true, true, true]) else (if b 9 =
    0 then [true, true, true, false, true, false, true, true, false] else [false, false, true,
    false, true, false, false, true, true])) else (if b 8 = 0 then (if b 9 = 0 then [true,
    true, true, false, true, true, false, true, false] else [false, false, true, false, true,
    true, true, true, true]) else (if b 9 = 0 then [false, true, true, false, true, true, true,
    true, false] else [true, false, true, false, true, true, false, true, true])))) else (if b
    6 = 0 then (if b 7 = 0 then (if b 8 = 0 then (if b 9 = 0 then [false, true, true, true,
    false, false, false, true, false] else [true, false, true, true, false, false, true, true,
    true]) else (if b 9 = 0 then [true, true, true, true, false, false, true, true, false] else
    [false, false, true, true, false, false, false, true, true])) else (if b 8 = 0 then (if b 9
    = 0 then [true, true, true, true, false, true, false, true, false] else [false, false,
    true, true, false, true, true, true, true]) else (if b 9 = 0 then [false, true, true, true,
    false, true, true, true, false] else [true, false, true, true, false, true, false, true,
    true]))) else (if b 7 = 0 then (if b 8 = 0 then (if b 9 = 0 then [true, true, true, true,
    true, false, false, true, false] else [false, false, true, true, true, false, true, true,
    true]) else (if b 9 = 0 then [false, true, true, true, true, false, true, true, false] else
    [true, false, true, true, true, false, false, true, true])) else (if b 8 = 0 then (if b 9 =
    0 then [false, true, true, true, true, true, false, true, false] else [true, false, true,
    true, true, true, true, true, true]) else (if b 9 = 0 then [true, true, true, true, true,
    true, true, true, false] else [false, false, true, true, true, true, false, true,
    true]))))))) else (if b 3 = 0 then (if b 4 = 0 then (if b 5 = 0 then (if b 6 = 0 then (if b
    7 = 0 then (if b 8 = 0 then (if b 9 = 0 then [false, false, false, false, false, false,
    false, true, false] else [true, true, false, false, false, false, true, true, true]) else
    (if b 9 = 0 then [true, false, false, false, false, false, true, true, false] else [false,
    true, false, false, false, false, false, true, true])) else (if b 8 = 0 then (if b 9 = 0
    then [true, false, false, false, false, true, false, true, false] else [false, true, false,
    false, false, true, true, true, true]) else (if b 9 = 0 then [false, false, false, false,
    false, true, true, true, false] else [true, true, false, false, false, true, false, true,
    true]))) else (if b 7 = 0 then (if b 8 = 0 then (if b 9 = 0 then [true, false, false,
    false, true, false, false, true, false] else [false, true, false, false, true, false, true,
    true, true]) else (if b 9 = 0 then [false, false, false, false, true, false, true, true,
    false] else [true, true, false, false, true, false, false, true, true])) else (if b 8 = 0
    then (if b 9 = 0 then [false, false, false, false, true, true, false, true, false] else
    [true, true, false, false, true, true, true, true, true]) else (if b 9 = 0 then [true,
    false, false, false, true, true, true, true, false] else [false, true, false, false, true,
    true, false, true, true])))) else (if b 6 = 0 then (if b 7 = 0 then (if b 8 = 0 then (if b
    9 = 0 then [true, false, false, true, false, false, false, true, false] else [false, true,
    false, true, false, false, true, true, true]) else (if b 9 = 0 then [false, false, false,
    true, false, false, true, true, false] else [true, true, false, true, false, false, false,
    true, true])) else (if b 8 = 0 then (if b 9 = 0 then [false, false, false, true, false,
    true, false, true, false] else [true, true, false, true, false, true, true, true, true])
    else (if b 9 = 0 then [true, false, false, true, false, true, true, true, false] else
    [false, true, false, true, false, true, false, true, true]))) else (if b 7 = 0 then (if b 8
    = 0 then (if b 9 = 0 then [false, false, false, true, true, false, false, true, false] else
    [true, true, false, true, true, false, true, true, true]) else (if b 9 = 0 then [true,
    false, false, true, true, false, true, true, false] else [false, true, false, true, true,
    false, false, true, true])) else (if b 8 = 0 then (if b 9 = 0 then [true, false, false,
    true, true, true, false, true, false] else [false, true, false, true, true, true, true,
    true, true]) else (if b 9 = 0 then [false, false, false, true, true, true, true, true,
    false] else [true, true, false, true, true, true, false, true, true]))))) else (if b 5 = 0
    then (if b 6 = 0 then (if b 7 = 0 then (if b 8 = 0 then (if b 9 = 0 then [true, false,
    true, false, false, false, false, true, false] else [false, true, true, false, false,
    false, true, true, true]) else (if b 9 = 0 then [false, false, true, false, false, false,
    true, true, false] else [true, true, true, false, false, false, false, true, true])) else
    (if b 8 = 0 then (if b 9 = 0 then [false, false, true, false, false, true, false, true,
    false] else [true, true, true, false, false, true, true, true, true]) else (if b 9 = 0 then
    [true, false, true, false, false, true, true, true, false] else [false, true, true, false,
    false, true, false, true, true]))) else (if b 7 = 0 then (if b 8 = 0 then (if b 9 = 0 then
    [false, false, true, false, true, false, false, true, false] else [true, true, true, false,
    true, false, true, true, true]) else (if b 9 = 0 then [true, false, true, false, true,
    false, true, true, false] else [false, true, true, false, true, false, false, true, true]))
    else (if b 8 = 0 then (if b 9 = 0 then [true, false, true, false, true, true, false, true,
    false] else [false, true, true, false, true, true, true, true, true]) else (if b 9 = 0 then
    [false, false, true, false, true, true, true, true, false] else [true, true, true, false,
    true, true, false, true, true])))) else (if b 6 = 0 then (if b 7 = 0 then (if b 8 = 0 then
    (if b 9 = 0 then [false, false, true, true, false, false, false, true, false] else [true,
    true, true, true, false, false, true, true, true]) else (if b 9 = 0 then [true, false,
    true, true, false, false, true, true, false] else [false, true, true, true, false, false,
    false, true, true])) else (if b 8 = 0 then (if b 9 = 0 then [true, false, true, true,
    false, true, false, true, false] else [false, true, true, true, false, true, true, true,
    true]) else (if b 9 = 0 then [false, false, true, true, false, true, true, true, false]
    else [true, true, true, true, false, true, false, true, true]))) else (if b 7 = 0 then (if
    b 8 = 0 then (if b 9 = 0 then [true, false, true, true, true, false, false, true, false]
    else [false, true, true, true, true, false, true, true, true]) else (if b 9 = 0 then
    [false, false, true, true, true, false, true, true, false] else [true, true, true, true,
    true, false, false, true, true])) else (if b 8 = 0 then (if b 9 = 0 then [false, false,
    true, true, true, true, false, true, false] else [true, true, true, true, true, true, true,
    true, true]) else (if b 9 = 0 then [true, false, true, true, true, true, true, true, false]
    else [false, true, true, true, true, true, false, true, true])))))) else (if b 4 = 0 then
    (if b 5 = 0 then (if b 6 = 0 then (if b 7 = 0 then (if b 8 = 0 then (if b 9 = 0 then [true,
    true, false, false, false, false, false, true, false] else [false, false, false, false,
    false, false, true, true, true]) else (if b 9 = 0 then [false, true, false, false, false,
    false, true, true, false] else [true, false, false, false, false, false, false, true,
    true])) else (if b 8 = 0 then (if b 9 = 0 then [false, true, false, false, false, true,
    false, true, false] else [true, false, false, false, false, true, true, true, true]) else
    (if b 9 = 0 then [true, true, false, false, false, true, true, true, false] else [false,
    false, false, false, false, true, false, true, true]))) else (if b 7 = 0 then (if b 8 = 0
    then (if b 9 = 0 then [false, true, false, false, true, false, false, true, false] else
    [true, false, false, false, true, false, true, true, true]) else (if b 9 = 0 then [true,
    true, false, false, true, false, true, true, false] else [false, false, false, false, true,
    false, false, true, true])) else (if b 8 = 0 then (if b 9 = 0 then [true, true, false,
    false, true, true, false, true, false] else [false, false, false, false, true, true, true,
    true, true]) else (if b 9 = 0 then [false, true, false, false, true, true, true, true,
    false] else [true, false, false, false, true, true, false, true, true])))) else (if b 6 = 0
    then (if b 7 = 0 then (if b 8 = 0 then (if b 9 = 0 then [false, true, false, true, false,
    false, false, true, false] else [true, false, false, true, false, false, true, true, true])
    else (if b 9 = 0 then [true, true, false, true, false, false, true, true, false] else
    [false, false, false, true, false, false, false, true, true])) else (if b 8 = 0 then (if b
    9 = 0 then [true, true, false, true, false, true, false, true, false] else [false, false,
    false, true, false, true, true, true, true]) else (if b 9 = 0 then [false, true, false,
    true, false, true, true, true, false] else [true, false, false, true, false, true, false,
    true, true]))) else (if b 7 = 0 then (if b 8 = 0 then (if b 9 = 0 then [true, true, false,
    true, true, false, false, true, false] else [false, false, false, true, true, false, true,
    true, true]) else (if b 9 = 0 then [false, true, false, true, true, false, true, true,
    false] else [true, false, false, true, true, false, false, true, true])) else (if b 8 = 0
    then (if b 9 = 0 then [false, true, false, true, true, true, false, true, false] else
    [true, false, false, true, true, true, true, true, true]) else (if b 9 = 0 then [true,
    true, false, true, true, true, true, true, false] else [false, false, false, true, true,
    true, false, true, true]))))) else (if b 5 = 0 then (if b 6 = 0 then (if b 7 = 0 then (if b
    8 = 0 then (if b 9 = 0 then [false, true, true, false, false, false, false, true, false]
    else [true, false, true, false, false, false, true, true, true]) else (if b 9 = 0 then
    [true, true, true, false, false, false, true, true, false] else [false, false, true, false,
    false, false, false, true, true])) else (if b 8 = 0 then (if b 9 = 0 then [true, true,
    true, false, false, true, false, true, false] else [false, false, true, false, false, true,
    true, true, true]) else (if b 9 = 0 then [false, true, true, false, false, true, true,
    true, false] else [true, false, true, false, false, true, false, true, true]))) else (if b
    7 = 0 then (if b 8 = 0 then (if b 9 = 0 then [true, true, true, false, true, false, false,
    true, false] else [false, false, true, false, true, false, true, true, true]) else (if b 9
    = 0 then [false, true, true, false, true, false, true, true, false] else [true, false,
    true, false, true, false, false, true, true])) else (if b 8 = 0 then (if b 9 = 0 then
    [false, true, true, false, true, true, false, true, false] else [true, false, true, false,
    true, true, true, true, true]) else (if b 9 = 0 then [true, true, true, false, true, true,
    true, true, false] else [false, false, true, false, true, true, false, true, true])))) else
    (if b 6 = 0 then (if b 7 = 0 then (if b 8 = 0 then (if b 9 = 0 then [true, true, true,
    true, false, false, false, true, false] else [false, false, true, true, false, false, true,
    true, true]) else (if b 9 = 0 then [false, true, true, true, false, false, true, true,
    false] else [true, false, true, true, false, false, false, true, true])) else (if b 8 = 0
    then (if b 9 = 0 then [false, true, true, true, false, true, false, true, false] else
    [true, false, true, true, false, true, true, true, true]) else (if b 9 = 0 then [true,
    true, true, true, false, true, true, true, false] else [false, false, true, true, false,
    true, false, true, true]))) else (if b 7 = 0 then (if b 8 = 0 then (if b 9 = 0 then [false,
    true, true, true, true, false, false, true, false] else [true, false, true, true, true,
    false, true, true, true]) else (if b 9 = 0 then [true, true, true, true, true, false, true,
    true, false] else [false, false, true, true, true, false, false, true, true])) else (if b 8
    = 0 then (if b 9 = 0 then [true, true, true, true, true, true, false, true, false] else
    [false, false, true, true, true, true, true, true, true]) else (if b 9 = 0 then [false,
    true, true, true, true, true, true, true, false] else [true, false, true, true, true, true,
    false, true, true]))))))))))

@[expose] def yMaskOf1 (b : Fin 10 → Fin 2) : List Bool :=
(if b 0 = 0 then (if b 1 = 0 then (if b 2 = 0 then (if b 3 = 0 then (if b 4 = 0 then (if b 5 =
    0 then (if b 6 = 0 then (if b 7 = 0 then (if b 8 = 0 then (if b 9 = 0 then [false, false,
    false, false, false, false, false, false, false] else [true, false, false, false, true,
    false, false, false, false]) else (if b 9 = 0 then [true, false, true, false, false, false,
    false, false, false] else [false, false, true, false, true, false, false, false, false]))
    else (if b 8 = 0 then (if b 9 = 0 then [true, true, false, false, false, false, false,
    false, false] else [false, true, false, false, true, false, false, false, false]) else (if
    b 9 = 0 then [false, true, true, false, false, false, false, false, false] else [true,
    true, true, false, true, false, false, false, false]))) else (if b 7 = 0 then (if b 8 = 0
    then (if b 9 = 0 then [true, true, false, true, false, false, false, false, true] else
    [false, true, false, true, true, false, false, false, true]) else (if b 9 = 0 then [false,
    true, true, true, false, false, false, false, true] else [true, true, true, true, true,
    false, false, false, true])) else (if b 8 = 0 then (if b 9 = 0 then [false, false, false,
    true, false, false, false, false, true] else [true, false, false, true, true, false, false,
    false, true]) else (if b 9 = 0 then [true, false, true, true, false, false, false, false,
    true] else [false, false, true, true, true, false, false, false, true])))) else (if b 6 = 0
    then (if b 7 = 0 then (if b 8 = 0 then (if b 9 = 0 then [false, true, false, true, false,
    false, false, false, true] else [true, true, false, true, true, false, false, false, true])
    else (if b 9 = 0 then [true, true, true, true, false, false, false, false, true] else
    [false, true, true, true, true, false, false, false, true])) else (if b 8 = 0 then (if b 9
    = 0 then [true, false, false, true, false, false, false, false, true] else [false, false,
    false, true, true, false, false, false, true]) else (if b 9 = 0 then [false, false, true,
    true, false, false, false, false, true] else [true, false, true, true, true, false, false,
    false, true]))) else (if b 7 = 0 then (if b 8 = 0 then (if b 9 = 0 then [true, false,
    false, false, false, false, false, false, false] else [false, false, false, false, true,
    false, false, false, false]) else (if b 9 = 0 then [false, false, true, false, false,
    false, false, false, false] else [true, false, true, false, true, false, false, false,
    false])) else (if b 8 = 0 then (if b 9 = 0 then [false, true, false, false, false, false,
    false, false, false] else [true, true, false, false, true, false, false, false, false])
    else (if b 9 = 0 then [true, true, true, false, false, false, false, false, false] else
    [false, true, true, false, true, false, false, false, false]))))) else (if b 5 = 0 then (if
    b 6 = 0 then (if b 7 = 0 then (if b 8 = 0 then (if b 9 = 0 then [true, false, false, true,
    false, false, false, false, false] else [false, false, false, true, true, false, false,
    false, false]) else (if b 9 = 0 then [false, false, true, true, false, false, false, false,
    false] else [true, false, true, true, true, false, false, false, false])) else (if b 8 = 0
    then (if b 9 = 0 then [false, true, false, true, false, false, false, false, false] else
    [true, true, false, true, true, false, false, false, false]) else (if b 9 = 0 then [true,
    true, true, true, false, false, false, false, false] else [false, true, true, true, true,
    false, false, false, false]))) else (if b 7 = 0 then (if b 8 = 0 then (if b 9 = 0 then
    [false, true, false, false, false, false, false, false, true] else [true, true, false,
    false, true, false, false, false, true]) else (if b 9 = 0 then [true, true, true, false,
    false, false, false, false, true] else [false, true, true, false, true, false, false,
    false, true])) else (if b 8 = 0 then (if b 9 = 0 then [true, false, false, false, false,
    false, false, false, true] else [false, false, false, false, true, false, false, false,
    true]) else (if b 9 = 0 then [false, false, true, false, false, false, false, false, true]
    else [true, false, true, false, true, false, false, false, true])))) else (if b 6 = 0 then
    (if b 7 = 0 then (if b 8 = 0 then (if b 9 = 0 then [true, true, false, false, false, false,
    false, false, true] else [false, true, false, false, true, false, false, false, true]) else
    (if b 9 = 0 then [false, true, true, false, false, false, false, false, true] else [true,
    true, true, false, true, false, false, false, true])) else (if b 8 = 0 then (if b 9 = 0
    then [false, false, false, false, false, false, false, false, true] else [true, false,
    false, false, true, false, false, false, true]) else (if b 9 = 0 then [true, false, true,
    false, false, false, false, false, true] else [false, false, true, false, true, false,
    false, false, true]))) else (if b 7 = 0 then (if b 8 = 0 then (if b 9 = 0 then [false,
    false, false, true, false, false, false, false, false] else [true, false, false, true,
    true, false, false, false, false]) else (if b 9 = 0 then [true, false, true, true, false,
    false, false, false, false] else [false, false, true, true, true, false, false, false,
    false])) else (if b 8 = 0 then (if b 9 = 0 then [true, true, false, true, false, false,
    false, false, false] else [false, true, false, true, true, false, false, false, false])
    else (if b 9 = 0 then [false, true, true, true, false, false, false, false, false] else
    [true, true, true, true, true, false, false, false, false])))))) else (if b 4 = 0 then (if
    b 5 = 0 then (if b 6 = 0 then (if b 7 = 0 then (if b 8 = 0 then (if b 9 = 0 then [true,
    false, false, false, false, true, false, false, false] else [false, false, false, false,
    true, true, false, false, false]) else (if b 9 = 0 then [false, false, true, false, false,
    true, false, false, false] else [true, false, true, false, true, true, false, false,
    false])) else (if b 8 = 0 then (if b 9 = 0 then [false, true, false, false, false, true,
    false, false, false] else [true, true, false, false, true, true, false, false, false]) else
    (if b 9 = 0 then [true, true, true, false, false, true, false, false, false] else [false,
    true, true, false, true, true, false, false, false]))) else (if b 7 = 0 then (if b 8 = 0
    then (if b 9 = 0 then [false, true, false, true, false, true, false, false, true] else
    [true, true, false, true, true, true, false, false, true]) else (if b 9 = 0 then [true,
    true, true, true, false, true, false, false, true] else [false, true, true, true, true,
    true, false, false, true])) else (if b 8 = 0 then (if b 9 = 0 then [true, false, false,
    true, false, true, false, false, true] else [false, false, false, true, true, true, false,
    false, true]) else (if b 9 = 0 then [false, false, true, true, false, true, false, false,
    true] else [true, false, true, true, true, true, false, false, true])))) else (if b 6 = 0
    then (if b 7 = 0 then (if b 8 = 0 then (if b 9 = 0 then [true, true, false, true, false,
    true, false, false, true] else [false, true, false, true, true, true, false, false, true])
    else (if b 9 = 0 then [false, true, true, true, false, true, false, false, true] else
    [true, true, true, true, true, true, false, false, true])) else (if b 8 = 0 then (if b 9 =
    0 then [false, false, false, true, false, true, false, false, true] else [true, false,
    false, true, true, true, false, false, true]) else (if b 9 = 0 then [true, false, true,
    true, false, true, false, false, true] else [false, false, true, true, true, true, false,
    false, true]))) else (if b 7 = 0 then (if b 8 = 0 then (if b 9 = 0 then [false, false,
    false, false, false, true, false, false, false] else [true, false, false, false, true,
    true, false, false, false]) else (if b 9 = 0 then [true, false, true, false, false, true,
    false, false, false] else [false, false, true, false, true, true, false, false, false]))
    else (if b 8 = 0 then (if b 9 = 0 then [true, true, false, false, false, true, false,
    false, false] else [false, true, false, false, true, true, false, false, false]) else (if b
    9 = 0 then [false, true, true, false, false, true, false, false, false] else [true, true,
    true, false, true, true, false, false, false]))))) else (if b 5 = 0 then (if b 6 = 0 then
    (if b 7 = 0 then (if b 8 = 0 then (if b 9 = 0 then [false, false, false, true, false, true,
    false, false, false] else [true, false, false, true, true, true, false, false, false]) else
    (if b 9 = 0 then [true, false, true, true, false, true, false, false, false] else [false,
    false, true, true, true, true, false, false, false])) else (if b 8 = 0 then (if b 9 = 0
    then [true, true, false, true, false, true, false, false, false] else [false, true, false,
    true, true, true, false, false, false]) else (if b 9 = 0 then [false, true, true, true,
    false, true, false, false, false] else [true, true, true, true, true, true, false, false,
    false]))) else (if b 7 = 0 then (if b 8 = 0 then (if b 9 = 0 then [true, true, false,
    false, false, true, false, false, true] else [false, true, false, false, true, true, false,
    false, true]) else (if b 9 = 0 then [false, true, true, false, false, true, false, false,
    true] else [true, true, true, false, true, true, false, false, true])) else (if b 8 = 0
    then (if b 9 = 0 then [false, false, false, false, false, true, false, false, true] else
    [true, false, false, false, true, true, false, false, true]) else (if b 9 = 0 then [true,
    false, true, false, false, true, false, false, true] else [false, false, true, false, true,
    true, false, false, true])))) else (if b 6 = 0 then (if b 7 = 0 then (if b 8 = 0 then (if b
    9 = 0 then [false, true, false, false, false, true, false, false, true] else [true, true,
    false, false, true, true, false, false, true]) else (if b 9 = 0 then [true, true, true,
    false, false, true, false, false, true] else [false, true, true, false, true, true, false,
    false, true])) else (if b 8 = 0 then (if b 9 = 0 then [true, false, false, false, false,
    true, false, false, true] else [false, false, false, false, true, true, false, false,
    true]) else (if b 9 = 0 then [false, false, true, false, false, true, false, false, true]
    else [true, false, true, false, true, true, false, false, true]))) else (if b 7 = 0 then
    (if b 8 = 0 then (if b 9 = 0 then [true, false, false, true, false, true, false, false,
    false] else [false, false, false, true, true, true, false, false, false]) else (if b 9 = 0
    then [false, false, true, true, false, true, false, false, false] else [true, false, true,
    true, true, true, false, false, false])) else (if b 8 = 0 then (if b 9 = 0 then [false,
    true, false, true, false, true, false, false, false] else [true, true, false, true, true,
    true, false, false, false]) else (if b 9 = 0 then [true, true, true, true, false, true,
    false, false, false] else [false, true, true, true, true, true, false, false, false])))))))
    else (if b 3 = 0 then (if b 4 = 0 then (if b 5 = 0 then (if b 6 = 0 then (if b 7 = 0 then
    (if b 8 = 0 then (if b 9 = 0 then [true, false, false, false, false, false, true, false,
    false] else [false, false, false, false, true, false, true, false, false]) else (if b 9 = 0
    then [false, false, true, false, false, false, true, false, false] else [true, false, true,
    false, true, false, true, false, false])) else (if b 8 = 0 then (if b 9 = 0 then [false,
    true, false, false, false, false, true, false, false] else [true, true, false, false, true,
    false, true, false, false]) else (if b 9 = 0 then [true, true, true, false, false, false,
    true, false, false] else [false, true, true, false, true, false, true, false, false])))
    else (if b 7 = 0 then (if b 8 = 0 then (if b 9 = 0 then [false, true, false, true, false,
    false, true, false, true] else [true, true, false, true, true, false, true, false, true])
    else (if b 9 = 0 then [true, true, true, true, false, false, true, false, true] else
    [false, true, true, true, true, false, true, false, true])) else (if b 8 = 0 then (if b 9 =
    0 then [true, false, false, true, false, false, true, false, true] else [false, false,
    false, true, true, false, true, false, true]) else (if b 9 = 0 then [false, false, true,
    true, false, false, true, false, true] else [true, false, true, true, true, false, true,
    false, true])))) else (if b 6 = 0 then (if b 7 = 0 then (if b 8 = 0 then (if b 9 = 0 then
    [true, true, false, true, false, false, true, false, true] else [false, true, false, true,
    true, false, true, false, true]) else (if b 9 = 0 then [false, true, true, true, false,
    false, true, false, true] else [true, true, true, true, true, false, true, false, true]))
    else (if b 8 = 0 then (if b 9 = 0 then [false, false, false, true, false, false, true,
    false, true] else [true, false, false, true, true, false, true, false, true]) else (if b 9
    = 0 then [true, false, true, true, false, false, true, false, true] else [false, false,
    true, true, true, false, true, false, true]))) else (if b 7 = 0 then (if b 8 = 0 then (if b
    9 = 0 then [false, false, false, false, false, false, true, false, false] else [true,
    false, false, false, true, false, true, false, false]) else (if b 9 = 0 then [true, false,
    true, false, false, false, true, false, false] else [false, false, true, false, true,
    false, true, false, false])) else (if b 8 = 0 then (if b 9 = 0 then [true, true, false,
    false, false, false, true, false, false] else [false, true, false, false, true, false,
    true, false, false]) else (if b 9 = 0 then [false, true, true, false, false, false, true,
    false, false] else [true, true, true, false, true, false, true, false, false]))))) else (if
    b 5 = 0 then (if b 6 = 0 then (if b 7 = 0 then (if b 8 = 0 then (if b 9 = 0 then [false,
    false, false, true, false, false, true, false, false] else [true, false, false, true, true,
    false, true, false, false]) else (if b 9 = 0 then [true, false, true, true, false, false,
    true, false, false] else [false, false, true, true, true, false, true, false, false])) else
    (if b 8 = 0 then (if b 9 = 0 then [true, true, false, true, false, false, true, false,
    false] else [false, true, false, true, true, false, true, false, false]) else (if b 9 = 0
    then [false, true, true, true, false, false, true, false, false] else [true, true, true,
    true, true, false, true, false, false]))) else (if b 7 = 0 then (if b 8 = 0 then (if b 9 =
    0 then [true, true, false, false, false, false, true, false, true] else [false, true,
    false, false, true, false, true, false, true]) else (if b 9 = 0 then [false, true, true,
    false, false, false, true, false, true] else [true, true, true, false, true, false, true,
    false, true])) else (if b 8 = 0 then (if b 9 = 0 then [false, false, false, false, false,
    false, true, false, true] else [true, false, false, false, true, false, true, false, true])
    else (if b 9 = 0 then [true, false, true, false, false, false, true, false, true] else
    [false, false, true, false, true, false, true, false, true])))) else (if b 6 = 0 then (if b
    7 = 0 then (if b 8 = 0 then (if b 9 = 0 then [false, true, false, false, false, false,
    true, false, true] else [true, true, false, false, true, false, true, false, true]) else
    (if b 9 = 0 then [true, true, true, false, false, false, true, false, true] else [false,
    true, true, false, true, false, true, false, true])) else (if b 8 = 0 then (if b 9 = 0 then
    [true, false, false, false, false, false, true, false, true] else [false, false, false,
    false, true, false, true, false, true]) else (if b 9 = 0 then [false, false, true, false,
    false, false, true, false, true] else [true, false, true, false, true, false, true, false,
    true]))) else (if b 7 = 0 then (if b 8 = 0 then (if b 9 = 0 then [true, false, false, true,
    false, false, true, false, false] else [false, false, false, true, true, false, true,
    false, false]) else (if b 9 = 0 then [false, false, true, true, false, false, true, false,
    false] else [true, false, true, true, true, false, true, false, false])) else (if b 8 = 0
    then (if b 9 = 0 then [false, true, false, true, false, false, true, false, false] else
    [true, true, false, true, true, false, true, false, false]) else (if b 9 = 0 then [true,
    true, true, true, false, false, true, false, false] else [false, true, true, true, true,
    false, true, false, false])))))) else (if b 4 = 0 then (if b 5 = 0 then (if b 6 = 0 then
    (if b 7 = 0 then (if b 8 = 0 then (if b 9 = 0 then [false, false, false, false, false,
    true, true, false, false] else [true, false, false, false, true, true, true, false, false])
    else (if b 9 = 0 then [true, false, true, false, false, true, true, false, false] else
    [false, false, true, false, true, true, true, false, false])) else (if b 8 = 0 then (if b 9
    = 0 then [true, true, false, false, false, true, true, false, false] else [false, true,
    false, false, true, true, true, false, false]) else (if b 9 = 0 then [false, true, true,
    false, false, true, true, false, false] else [true, true, true, false, true, true, true,
    false, false]))) else (if b 7 = 0 then (if b 8 = 0 then (if b 9 = 0 then [true, true,
    false, true, false, true, true, false, true] else [false, true, false, true, true, true,
    true, false, true]) else (if b 9 = 0 then [false, true, true, true, false, true, true,
    false, true] else [true, true, true, true, true, true, true, false, true])) else (if b 8 =
    0 then (if b 9 = 0 then [false, false, false, true, false, true, true, false, true] else
    [true, false, false, true, true, true, true, false, true]) else (if b 9 = 0 then [true,
    false, true, true, false, true, true, false, true] else [false, false, true, true, true,
    true, true, false, true])))) else (if b 6 = 0 then (if b 7 = 0 then (if b 8 = 0 then (if b
    9 = 0 then [false, true, false, true, false, true, true, false, true] else [true, true,
    false, true, true, true, true, false, true]) else (if b 9 = 0 then [true, true, true, true,
    false, true, true, false, true] else [false, true, true, true, true, true, true, false,
    true])) else (if b 8 = 0 then (if b 9 = 0 then [true, false, false, true, false, true,
    true, false, true] else [false, false, false, true, true, true, true, false, true]) else
    (if b 9 = 0 then [false, false, true, true, false, true, true, false, true] else [true,
    false, true, true, true, true, true, false, true]))) else (if b 7 = 0 then (if b 8 = 0 then
    (if b 9 = 0 then [true, false, false, false, false, true, true, false, false] else [false,
    false, false, false, true, true, true, false, false]) else (if b 9 = 0 then [false, false,
    true, false, false, true, true, false, false] else [true, false, true, false, true, true,
    true, false, false])) else (if b 8 = 0 then (if b 9 = 0 then [false, true, false, false,
    false, true, true, false, false] else [true, true, false, false, true, true, true, false,
    false]) else (if b 9 = 0 then [true, true, true, false, false, true, true, false, false]
    else [false, true, true, false, true, true, true, false, false]))))) else (if b 5 = 0 then
    (if b 6 = 0 then (if b 7 = 0 then (if b 8 = 0 then (if b 9 = 0 then [true, false, false,
    true, false, true, true, false, false] else [false, false, false, true, true, true, true,
    false, false]) else (if b 9 = 0 then [false, false, true, true, false, true, true, false,
    false] else [true, false, true, true, true, true, true, false, false])) else (if b 8 = 0
    then (if b 9 = 0 then [false, true, false, true, false, true, true, false, false] else
    [true, true, false, true, true, true, true, false, false]) else (if b 9 = 0 then [true,
    true, true, true, false, true, true, false, false] else [false, true, true, true, true,
    true, true, false, false]))) else (if b 7 = 0 then (if b 8 = 0 then (if b 9 = 0 then
    [false, true, false, false, false, true, true, false, true] else [true, true, false, false,
    true, true, true, false, true]) else (if b 9 = 0 then [true, true, true, false, false,
    true, true, false, true] else [false, true, true, false, true, true, true, false, true]))
    else (if b 8 = 0 then (if b 9 = 0 then [true, false, false, false, false, true, true,
    false, true] else [false, false, false, false, true, true, true, false, true]) else (if b 9
    = 0 then [false, false, true, false, false, true, true, false, true] else [true, false,
    true, false, true, true, true, false, true])))) else (if b 6 = 0 then (if b 7 = 0 then (if
    b 8 = 0 then (if b 9 = 0 then [true, true, false, false, false, true, true, false, true]
    else [false, true, false, false, true, true, true, false, true]) else (if b 9 = 0 then
    [false, true, true, false, false, true, true, false, true] else [true, true, true, false,
    true, true, true, false, true])) else (if b 8 = 0 then (if b 9 = 0 then [false, false,
    false, false, false, true, true, false, true] else [true, false, false, false, true, true,
    true, false, true]) else (if b 9 = 0 then [true, false, true, false, false, true, true,
    false, true] else [false, false, true, false, true, true, true, false, true]))) else (if b
    7 = 0 then (if b 8 = 0 then (if b 9 = 0 then [false, false, false, true, false, true, true,
    false, false] else [true, false, false, true, true, true, true, false, false]) else (if b 9
    = 0 then [true, false, true, true, false, true, true, false, false] else [false, false,
    true, true, true, true, true, false, false])) else (if b 8 = 0 then (if b 9 = 0 then [true,
    true, false, true, false, true, true, false, false] else [false, true, false, true, true,
    true, true, false, false]) else (if b 9 = 0 then [false, true, true, true, false, true,
    true, false, false] else [true, true, true, true, true, true, true, false, false]))))))))
    else (if b 2 = 0 then (if b 3 = 0 then (if b 4 = 0 then (if b 5 = 0 then (if b 6 = 0 then
    (if b 7 = 0 then (if b 8 = 0 then (if b 9 = 0 then [false, false, false, false, false,
    false, false, false, false] else [false, false, false, false, false, false, false, false,
    false]) else (if b 9 = 0 then [false, false, false, false, false, false, false, false,
    false] else [false, false, false, false, false, false, false, false, false])) else (if b 8
    = 0 then (if b 9 = 0 then [false, false, false, false, false, false, false, false, false]
    else [false, false, false, false, false, false, false, false, false]) else (if b 9 = 0 then
    [false, false, false, false, false, false, false, false, false] else [false, false, false,
    false, false, false, false, false, false]))) else (if b 7 = 0 then (if b 8 = 0 then (if b 9
    = 0 then [false, false, false, false, false, false, false, false, false] else [false,
    false, false, false, false, false, false, false, false]) else (if b 9 = 0 then [false,
    false, false, false, false, false, false, false, false] else [false, false, false, false,
    false, false, false, false, false])) else (if b 8 = 0 then (if b 9 = 0 then [false, false,
    false, false, false, false, false, false, false] else [false, false, false, false, false,
    false, false, false, false]) else (if b 9 = 0 then [false, false, false, false, false,
    false, false, false, false] else [false, false, false, false, false, false, false, false,
    false])))) else (if b 6 = 0 then (if b 7 = 0 then (if b 8 = 0 then (if b 9 = 0 then [false,
    false, false, false, false, false, false, false, false] else [false, false, false, false,
    false, false, false, false, false]) else (if b 9 = 0 then [false, false, false, false,
    false, false, false, false, false] else [false, false, false, false, false, false, false,
    false, false])) else (if b 8 = 0 then (if b 9 = 0 then [false, false, false, false, false,
    false, false, false, false] else [false, false, false, false, false, false, false, false,
    false]) else (if b 9 = 0 then [false, false, false, false, false, false, false, false,
    false] else [false, false, false, false, false, false, false, false, false]))) else (if b 7
    = 0 then (if b 8 = 0 then (if b 9 = 0 then [false, false, false, false, false, false,
    false, false, false] else [false, false, false, false, false, false, false, false, false])
    else (if b 9 = 0 then [false, false, false, false, false, false, false, false, false] else
    [false, false, false, false, false, false, false, false, false])) else (if b 8 = 0 then (if
    b 9 = 0 then [false, false, false, false, false, false, false, false, false] else [false,
    false, false, false, false, false, false, false, false]) else (if b 9 = 0 then [false,
    false, false, false, false, false, false, false, false] else [false, false, false, false,
    false, false, false, false, false]))))) else (if b 5 = 0 then (if b 6 = 0 then (if b 7 = 0
    then (if b 8 = 0 then (if b 9 = 0 then [false, false, false, false, false, false, false,
    false, false] else [false, false, false, false, false, false, false, false, false]) else
    (if b 9 = 0 then [false, false, false, false, false, false, false, false, false] else
    [false, false, false, false, false, false, false, false, false])) else (if b 8 = 0 then (if
    b 9 = 0 then [false, false, false, false, false, false, false, false, false] else [false,
    false, false, false, false, false, false, false, false]) else (if b 9 = 0 then [false,
    false, false, false, false, false, false, false, false] else [false, false, false, false,
    false, false, false, false, false]))) else (if b 7 = 0 then (if b 8 = 0 then (if b 9 = 0
    then [false, false, false, false, false, false, false, false, false] else [false, false,
    false, false, false, false, false, false, false]) else (if b 9 = 0 then [false, false,
    false, false, false, false, false, false, false] else [false, false, false, false, false,
    false, false, false, false])) else (if b 8 = 0 then (if b 9 = 0 then [false, false, false,
    false, false, false, false, false, false] else [false, false, false, false, false, false,
    false, false, false]) else (if b 9 = 0 then [false, false, false, false, false, false,
    false, false, false] else [false, false, false, false, false, false, false, false,
    false])))) else (if b 6 = 0 then (if b 7 = 0 then (if b 8 = 0 then (if b 9 = 0 then [false,
    false, false, false, false, false, false, false, false] else [false, false, false, false,
    false, false, false, false, false]) else (if b 9 = 0 then [false, false, false, false,
    false, false, false, false, false] else [false, false, false, false, false, false, false,
    false, false])) else (if b 8 = 0 then (if b 9 = 0 then [false, false, false, false, false,
    false, false, false, false] else [false, false, false, false, false, false, false, false,
    false]) else (if b 9 = 0 then [false, false, false, false, false, false, false, false,
    false] else [false, false, false, false, false, false, false, false, false]))) else (if b 7
    = 0 then (if b 8 = 0 then (if b 9 = 0 then [false, false, false, false, false, false,
    false, false, false] else [false, false, false, false, false, false, false, false, false])
    else (if b 9 = 0 then [false, false, false, false, false, false, false, false, false] else
    [false, false, false, false, false, false, false, false, false])) else (if b 8 = 0 then (if
    b 9 = 0 then [false, false, false, false, false, false, false, false, false] else [false,
    false, false, false, false, false, false, false, false]) else (if b 9 = 0 then [false,
    false, false, false, false, false, false, false, false] else [false, false, false, false,
    false, false, false, false, false])))))) else (if b 4 = 0 then (if b 5 = 0 then (if b 6 = 0
    then (if b 7 = 0 then (if b 8 = 0 then (if b 9 = 0 then [false, false, false, false, false,
    false, false, false, false] else [false, false, false, false, false, false, false, false,
    false]) else (if b 9 = 0 then [false, false, false, false, false, false, false, false,
    false] else [false, false, false, false, false, false, false, false, false])) else (if b 8
    = 0 then (if b 9 = 0 then [false, false, false, false, false, false, false, false, false]
    else [false, false, false, false, false, false, false, false, false]) else (if b 9 = 0 then
    [false, false, false, false, false, false, false, false, false] else [false, false, false,
    false, false, false, false, false, false]))) else (if b 7 = 0 then (if b 8 = 0 then (if b 9
    = 0 then [false, false, false, false, false, false, false, false, false] else [false,
    false, false, false, false, false, false, false, false]) else (if b 9 = 0 then [false,
    false, false, false, false, false, false, false, false] else [false, false, false, false,
    false, false, false, false, false])) else (if b 8 = 0 then (if b 9 = 0 then [false, false,
    false, false, false, false, false, false, false] else [false, false, false, false, false,
    false, false, false, false]) else (if b 9 = 0 then [false, false, false, false, false,
    false, false, false, false] else [false, false, false, false, false, false, false, false,
    false])))) else (if b 6 = 0 then (if b 7 = 0 then (if b 8 = 0 then (if b 9 = 0 then [false,
    false, false, false, false, false, false, false, false] else [false, false, false, false,
    false, false, false, false, false]) else (if b 9 = 0 then [false, false, false, false,
    false, false, false, false, false] else [false, false, false, false, false, false, false,
    false, false])) else (if b 8 = 0 then (if b 9 = 0 then [false, false, false, false, false,
    false, false, false, false] else [false, false, false, false, false, false, false, false,
    false]) else (if b 9 = 0 then [false, false, false, false, false, false, false, false,
    false] else [false, false, false, false, false, false, false, false, false]))) else (if b 7
    = 0 then (if b 8 = 0 then (if b 9 = 0 then [false, false, false, false, false, false,
    false, false, false] else [false, false, false, false, false, false, false, false, false])
    else (if b 9 = 0 then [false, false, false, false, false, false, false, false, false] else
    [false, false, false, false, false, false, false, false, false])) else (if b 8 = 0 then (if
    b 9 = 0 then [false, false, false, false, false, false, false, false, false] else [false,
    false, false, false, false, false, false, false, false]) else (if b 9 = 0 then [false,
    false, false, false, false, false, false, false, false] else [false, false, false, false,
    false, false, false, false, false]))))) else (if b 5 = 0 then (if b 6 = 0 then (if b 7 = 0
    then (if b 8 = 0 then (if b 9 = 0 then [false, false, false, false, false, false, false,
    false, false] else [false, false, false, false, false, false, false, false, false]) else
    (if b 9 = 0 then [false, false, false, false, false, false, false, false, false] else
    [false, false, false, false, false, false, false, false, false])) else (if b 8 = 0 then (if
    b 9 = 0 then [false, false, false, false, false, false, false, false, false] else [false,
    false, false, false, false, false, false, false, false]) else (if b 9 = 0 then [false,
    false, false, false, false, false, false, false, false] else [false, false, false, false,
    false, false, false, false, false]))) else (if b 7 = 0 then (if b 8 = 0 then (if b 9 = 0
    then [false, false, false, false, false, false, false, false, false] else [false, false,
    false, false, false, false, false, false, false]) else (if b 9 = 0 then [false, false,
    false, false, false, false, false, false, false] else [false, false, false, false, false,
    false, false, false, false])) else (if b 8 = 0 then (if b 9 = 0 then [false, false, false,
    false, false, false, false, false, false] else [false, false, false, false, false, false,
    false, false, false]) else (if b 9 = 0 then [false, false, false, false, false, false,
    false, false, false] else [false, false, false, false, false, false, false, false,
    false])))) else (if b 6 = 0 then (if b 7 = 0 then (if b 8 = 0 then (if b 9 = 0 then [false,
    false, false, false, false, false, false, false, false] else [false, false, false, false,
    false, false, false, false, false]) else (if b 9 = 0 then [false, false, false, false,
    false, false, false, false, false] else [false, false, false, false, false, false, false,
    false, false])) else (if b 8 = 0 then (if b 9 = 0 then [false, false, false, false, false,
    false, false, false, false] else [false, false, false, false, false, false, false, false,
    false]) else (if b 9 = 0 then [false, false, false, false, false, false, false, false,
    false] else [false, false, false, false, false, false, false, false, false]))) else (if b 7
    = 0 then (if b 8 = 0 then (if b 9 = 0 then [false, false, false, false, false, false,
    false, false, false] else [false, false, false, false, false, false, false, false, false])
    else (if b 9 = 0 then [false, false, false, false, false, false, false, false, false] else
    [false, false, false, false, false, false, false, false, false])) else (if b 8 = 0 then (if
    b 9 = 0 then [false, false, false, false, false, false, false, false, false] else [false,
    false, false, false, false, false, false, false, false]) else (if b 9 = 0 then [false,
    false, false, false, false, false, false, false, false] else [false, false, false, false,
    false, false, false, false, false]))))))) else (if b 3 = 0 then (if b 4 = 0 then (if b 5 =
    0 then (if b 6 = 0 then (if b 7 = 0 then (if b 8 = 0 then (if b 9 = 0 then [false, false,
    false, false, false, false, false, false, false] else [false, false, false, false, false,
    false, false, false, false]) else (if b 9 = 0 then [false, false, false, false, false,
    false, false, false, false] else [false, false, false, false, false, false, false, false,
    false])) else (if b 8 = 0 then (if b 9 = 0 then [false, false, false, false, false, false,
    false, false, false] else [false, false, false, false, false, false, false, false, false])
    else (if b 9 = 0 then [false, false, false, false, false, false, false, false, false] else
    [false, false, false, false, false, false, false, false, false]))) else (if b 7 = 0 then
    (if b 8 = 0 then (if b 9 = 0 then [false, false, false, false, false, false, false, false,
    false] else [false, false, false, false, false, false, false, false, false]) else (if b 9 =
    0 then [false, false, false, false, false, false, false, false, false] else [false, false,
    false, false, false, false, false, false, false])) else (if b 8 = 0 then (if b 9 = 0 then
    [false, false, false, false, false, false, false, false, false] else [false, false, false,
    false, false, false, false, false, false]) else (if b 9 = 0 then [false, false, false,
    false, false, false, false, false, false] else [false, false, false, false, false, false,
    false, false, false])))) else (if b 6 = 0 then (if b 7 = 0 then (if b 8 = 0 then (if b 9 =
    0 then [false, false, false, false, false, false, false, false, false] else [false, false,
    false, false, false, false, false, false, false]) else (if b 9 = 0 then [false, false,
    false, false, false, false, false, false, false] else [false, false, false, false, false,
    false, false, false, false])) else (if b 8 = 0 then (if b 9 = 0 then [false, false, false,
    false, false, false, false, false, false] else [false, false, false, false, false, false,
    false, false, false]) else (if b 9 = 0 then [false, false, false, false, false, false,
    false, false, false] else [false, false, false, false, false, false, false, false,
    false]))) else (if b 7 = 0 then (if b 8 = 0 then (if b 9 = 0 then [false, false, false,
    false, false, false, false, false, false] else [false, false, false, false, false, false,
    false, false, false]) else (if b 9 = 0 then [false, false, false, false, false, false,
    false, false, false] else [false, false, false, false, false, false, false, false, false]))
    else (if b 8 = 0 then (if b 9 = 0 then [false, false, false, false, false, false, false,
    false, false] else [false, false, false, false, false, false, false, false, false]) else
    (if b 9 = 0 then [false, false, false, false, false, false, false, false, false] else
    [false, false, false, false, false, false, false, false, false]))))) else (if b 5 = 0 then
    (if b 6 = 0 then (if b 7 = 0 then (if b 8 = 0 then (if b 9 = 0 then [false, false, false,
    false, false, false, false, false, false] else [false, false, false, false, false, false,
    false, false, false]) else (if b 9 = 0 then [false, false, false, false, false, false,
    false, false, false] else [false, false, false, false, false, false, false, false, false]))
    else (if b 8 = 0 then (if b 9 = 0 then [false, false, false, false, false, false, false,
    false, false] else [false, false, false, false, false, false, false, false, false]) else
    (if b 9 = 0 then [false, false, false, false, false, false, false, false, false] else
    [false, false, false, false, false, false, false, false, false]))) else (if b 7 = 0 then
    (if b 8 = 0 then (if b 9 = 0 then [false, false, false, false, false, false, false, false,
    false] else [false, false, false, false, false, false, false, false, false]) else (if b 9 =
    0 then [false, false, false, false, false, false, false, false, false] else [false, false,
    false, false, false, false, false, false, false])) else (if b 8 = 0 then (if b 9 = 0 then
    [false, false, false, false, false, false, false, false, false] else [false, false, false,
    false, false, false, false, false, false]) else (if b 9 = 0 then [false, false, false,
    false, false, false, false, false, false] else [false, false, false, false, false, false,
    false, false, false])))) else (if b 6 = 0 then (if b 7 = 0 then (if b 8 = 0 then (if b 9 =
    0 then [false, false, false, false, false, false, false, false, false] else [false, false,
    false, false, false, false, false, false, false]) else (if b 9 = 0 then [false, false,
    false, false, false, false, false, false, false] else [false, false, false, false, false,
    false, false, false, false])) else (if b 8 = 0 then (if b 9 = 0 then [false, false, false,
    false, false, false, false, false, false] else [false, false, false, false, false, false,
    false, false, false]) else (if b 9 = 0 then [false, false, false, false, false, false,
    false, false, false] else [false, false, false, false, false, false, false, false,
    false]))) else (if b 7 = 0 then (if b 8 = 0 then (if b 9 = 0 then [false, false, false,
    false, false, false, false, false, false] else [false, false, false, false, false, false,
    false, false, false]) else (if b 9 = 0 then [false, false, false, false, false, false,
    false, false, false] else [false, false, false, false, false, false, false, false, false]))
    else (if b 8 = 0 then (if b 9 = 0 then [false, false, false, false, false, false, false,
    false, false] else [false, false, false, false, false, false, false, false, false]) else
    (if b 9 = 0 then [false, false, false, false, false, false, false, false, false] else
    [false, false, false, false, false, false, false, false, false])))))) else (if b 4 = 0 then
    (if b 5 = 0 then (if b 6 = 0 then (if b 7 = 0 then (if b 8 = 0 then (if b 9 = 0 then
    [false, false, false, false, false, false, false, false, false] else [false, false, false,
    false, false, false, false, false, false]) else (if b 9 = 0 then [false, false, false,
    false, false, false, false, false, false] else [false, false, false, false, false, false,
    false, false, false])) else (if b 8 = 0 then (if b 9 = 0 then [false, false, false, false,
    false, false, false, false, false] else [false, false, false, false, false, false, false,
    false, false]) else (if b 9 = 0 then [false, false, false, false, false, false, false,
    false, false] else [false, false, false, false, false, false, false, false, false]))) else
    (if b 7 = 0 then (if b 8 = 0 then (if b 9 = 0 then [false, false, false, false, false,
    false, false, false, false] else [false, false, false, false, false, false, false, false,
    false]) else (if b 9 = 0 then [false, false, false, false, false, false, false, false,
    false] else [false, false, false, false, false, false, false, false, false])) else (if b 8
    = 0 then (if b 9 = 0 then [false, false, false, false, false, false, false, false, false]
    else [false, false, false, false, false, false, false, false, false]) else (if b 9 = 0 then
    [false, false, false, false, false, false, false, false, false] else [false, false, false,
    false, false, false, false, false, false])))) else (if b 6 = 0 then (if b 7 = 0 then (if b
    8 = 0 then (if b 9 = 0 then [false, false, false, false, false, false, false, false, false]
    else [false, false, false, false, false, false, false, false, false]) else (if b 9 = 0 then
    [false, false, false, false, false, false, false, false, false] else [false, false, false,
    false, false, false, false, false, false])) else (if b 8 = 0 then (if b 9 = 0 then [false,
    false, false, false, false, false, false, false, false] else [false, false, false, false,
    false, false, false, false, false]) else (if b 9 = 0 then [false, false, false, false,
    false, false, false, false, false] else [false, false, false, false, false, false, false,
    false, false]))) else (if b 7 = 0 then (if b 8 = 0 then (if b 9 = 0 then [false, false,
    false, false, false, false, false, false, false] else [false, false, false, false, false,
    false, false, false, false]) else (if b 9 = 0 then [false, false, false, false, false,
    false, false, false, false] else [false, false, false, false, false, false, false, false,
    false])) else (if b 8 = 0 then (if b 9 = 0 then [false, false, false, false, false, false,
    false, false, false] else [false, false, false, false, false, false, false, false, false])
    else (if b 9 = 0 then [false, false, false, false, false, false, false, false, false] else
    [false, false, false, false, false, false, false, false, false]))))) else (if b 5 = 0 then
    (if b 6 = 0 then (if b 7 = 0 then (if b 8 = 0 then (if b 9 = 0 then [false, false, false,
    false, false, false, false, false, false] else [false, false, false, false, false, false,
    false, false, false]) else (if b 9 = 0 then [false, false, false, false, false, false,
    false, false, false] else [false, false, false, false, false, false, false, false, false]))
    else (if b 8 = 0 then (if b 9 = 0 then [false, false, false, false, false, false, false,
    false, false] else [false, false, false, false, false, false, false, false, false]) else
    (if b 9 = 0 then [false, false, false, false, false, false, false, false, false] else
    [false, false, false, false, false, false, false, false, false]))) else (if b 7 = 0 then
    (if b 8 = 0 then (if b 9 = 0 then [false, false, false, false, false, false, false, false,
    false] else [false, false, false, false, false, false, false, false, false]) else (if b 9 =
    0 then [false, false, false, false, false, false, false, false, false] else [false, false,
    false, false, false, false, false, false, false])) else (if b 8 = 0 then (if b 9 = 0 then
    [false, false, false, false, false, false, false, false, false] else [false, false, false,
    false, false, false, false, false, false]) else (if b 9 = 0 then [false, false, false,
    false, false, false, false, false, false] else [false, false, false, false, false, false,
    false, false, false])))) else (if b 6 = 0 then (if b 7 = 0 then (if b 8 = 0 then (if b 9 =
    0 then [false, false, false, false, false, false, false, false, false] else [false, false,
    false, false, false, false, false, false, false]) else (if b 9 = 0 then [false, false,
    false, false, false, false, false, false, false] else [false, false, false, false, false,
    false, false, false, false])) else (if b 8 = 0 then (if b 9 = 0 then [false, false, false,
    false, false, false, false, false, false] else [false, false, false, false, false, false,
    false, false, false]) else (if b 9 = 0 then [false, false, false, false, false, false,
    false, false, false] else [false, false, false, false, false, false, false, false,
    false]))) else (if b 7 = 0 then (if b 8 = 0 then (if b 9 = 0 then [false, false, false,
    false, false, false, false, false, false] else [false, false, false, false, false, false,
    false, false, false]) else (if b 9 = 0 then [false, false, false, false, false, false,
    false, false, false] else [false, false, false, false, false, false, false, false, false]))
    else (if b 8 = 0 then (if b 9 = 0 then [false, false, false, false, false, false, false,
    false, false] else [false, false, false, false, false, false, false, false, false]) else
    (if b 9 = 0 then [false, false, false, false, false, false, false, false, false] else
    [false, false, false, false, false, false, false, false, false]))))))))) else (if b 1 = 0
    then (if b 2 = 0 then (if b 3 = 0 then (if b 4 = 0 then (if b 5 = 0 then (if b 6 = 0 then
    (if b 7 = 0 then (if b 8 = 0 then (if b 9 = 0 then [false, false, false, false, false,
    false, false, false, false] else [false, false, false, false, false, false, false, false,
    false]) else (if b 9 = 0 then [false, false, false, false, false, false, false, false,
    false] else [false, false, false, false, false, false, false, false, false])) else (if b 8
    = 0 then (if b 9 = 0 then [false, false, false, false, false, false, false, false, false]
    else [false, false, false, false, false, false, false, false, false]) else (if b 9 = 0 then
    [false, false, false, false, false, false, false, false, false] else [false, false, false,
    false, false, false, false, false, false]))) else (if b 7 = 0 then (if b 8 = 0 then (if b 9
    = 0 then [false, false, false, false, false, false, false, false, false] else [false,
    false, false, false, false, false, false, false, false]) else (if b 9 = 0 then [false,
    false, false, false, false, false, false, false, false] else [false, false, false, false,
    false, false, false, false, false])) else (if b 8 = 0 then (if b 9 = 0 then [false, false,
    false, false, false, false, false, false, false] else [false, false, false, false, false,
    false, false, false, false]) else (if b 9 = 0 then [false, false, false, false, false,
    false, false, false, false] else [false, false, false, false, false, false, false, false,
    false])))) else (if b 6 = 0 then (if b 7 = 0 then (if b 8 = 0 then (if b 9 = 0 then [false,
    false, false, false, false, false, false, false, false] else [false, false, false, false,
    false, false, false, false, false]) else (if b 9 = 0 then [false, false, false, false,
    false, false, false, false, false] else [false, false, false, false, false, false, false,
    false, false])) else (if b 8 = 0 then (if b 9 = 0 then [false, false, false, false, false,
    false, false, false, false] else [false, false, false, false, false, false, false, false,
    false]) else (if b 9 = 0 then [false, false, false, false, false, false, false, false,
    false] else [false, false, false, false, false, false, false, false, false]))) else (if b 7
    = 0 then (if b 8 = 0 then (if b 9 = 0 then [false, false, false, false, false, false,
    false, false, false] else [false, false, false, false, false, false, false, false, false])
    else (if b 9 = 0 then [false, false, false, false, false, false, false, false, false] else
    [false, false, false, false, false, false, false, false, false])) else (if b 8 = 0 then (if
    b 9 = 0 then [false, false, false, false, false, false, false, false, false] else [false,
    false, false, false, false, false, false, false, false]) else (if b 9 = 0 then [false,
    false, false, false, false, false, false, false, false] else [false, false, false, false,
    false, false, false, false, false]))))) else (if b 5 = 0 then (if b 6 = 0 then (if b 7 = 0
    then (if b 8 = 0 then (if b 9 = 0 then [false, false, false, false, false, false, false,
    false, false] else [false, false, false, false, false, false, false, false, false]) else
    (if b 9 = 0 then [false, false, false, false, false, false, false, false, false] else
    [false, false, false, false, false, false, false, false, false])) else (if b 8 = 0 then (if
    b 9 = 0 then [false, false, false, false, false, false, false, false, false] else [false,
    false, false, false, false, false, false, false, false]) else (if b 9 = 0 then [false,
    false, false, false, false, false, false, false, false] else [false, false, false, false,
    false, false, false, false, false]))) else (if b 7 = 0 then (if b 8 = 0 then (if b 9 = 0
    then [false, false, false, false, false, false, false, false, false] else [false, false,
    false, false, false, false, false, false, false]) else (if b 9 = 0 then [false, false,
    false, false, false, false, false, false, false] else [false, false, false, false, false,
    false, false, false, false])) else (if b 8 = 0 then (if b 9 = 0 then [false, false, false,
    false, false, false, false, false, false] else [false, false, false, false, false, false,
    false, false, false]) else (if b 9 = 0 then [false, false, false, false, false, false,
    false, false, false] else [false, false, false, false, false, false, false, false,
    false])))) else (if b 6 = 0 then (if b 7 = 0 then (if b 8 = 0 then (if b 9 = 0 then [false,
    false, false, false, false, false, false, false, false] else [false, false, false, false,
    false, false, false, false, false]) else (if b 9 = 0 then [false, false, false, false,
    false, false, false, false, false] else [false, false, false, false, false, false, false,
    false, false])) else (if b 8 = 0 then (if b 9 = 0 then [false, false, false, false, false,
    false, false, false, false] else [false, false, false, false, false, false, false, false,
    false]) else (if b 9 = 0 then [false, false, false, false, false, false, false, false,
    false] else [false, false, false, false, false, false, false, false, false]))) else (if b 7
    = 0 then (if b 8 = 0 then (if b 9 = 0 then [false, false, false, false, false, false,
    false, false, false] else [false, false, false, false, false, false, false, false, false])
    else (if b 9 = 0 then [false, false, false, false, false, false, false, false, false] else
    [false, false, false, false, false, false, false, false, false])) else (if b 8 = 0 then (if
    b 9 = 0 then [false, false, false, false, false, false, false, false, false] else [false,
    false, false, false, false, false, false, false, false]) else (if b 9 = 0 then [false,
    false, false, false, false, false, false, false, false] else [false, false, false, false,
    false, false, false, false, false])))))) else (if b 4 = 0 then (if b 5 = 0 then (if b 6 = 0
    then (if b 7 = 0 then (if b 8 = 0 then (if b 9 = 0 then [false, false, false, false, false,
    false, false, false, false] else [false, false, false, false, false, false, false, false,
    false]) else (if b 9 = 0 then [false, false, false, false, false, false, false, false,
    false] else [false, false, false, false, false, false, false, false, false])) else (if b 8
    = 0 then (if b 9 = 0 then [false, false, false, false, false, false, false, false, false]
    else [false, false, false, false, false, false, false, false, false]) else (if b 9 = 0 then
    [false, false, false, false, false, false, false, false, false] else [false, false, false,
    false, false, false, false, false, false]))) else (if b 7 = 0 then (if b 8 = 0 then (if b 9
    = 0 then [false, false, false, false, false, false, false, false, false] else [false,
    false, false, false, false, false, false, false, false]) else (if b 9 = 0 then [false,
    false, false, false, false, false, false, false, false] else [false, false, false, false,
    false, false, false, false, false])) else (if b 8 = 0 then (if b 9 = 0 then [false, false,
    false, false, false, false, false, false, false] else [false, false, false, false, false,
    false, false, false, false]) else (if b 9 = 0 then [false, false, false, false, false,
    false, false, false, false] else [false, false, false, false, false, false, false, false,
    false])))) else (if b 6 = 0 then (if b 7 = 0 then (if b 8 = 0 then (if b 9 = 0 then [false,
    false, false, false, false, false, false, false, false] else [false, false, false, false,
    false, false, false, false, false]) else (if b 9 = 0 then [false, false, false, false,
    false, false, false, false, false] else [false, false, false, false, false, false, false,
    false, false])) else (if b 8 = 0 then (if b 9 = 0 then [false, false, false, false, false,
    false, false, false, false] else [false, false, false, false, false, false, false, false,
    false]) else (if b 9 = 0 then [false, false, false, false, false, false, false, false,
    false] else [false, false, false, false, false, false, false, false, false]))) else (if b 7
    = 0 then (if b 8 = 0 then (if b 9 = 0 then [false, false, false, false, false, false,
    false, false, false] else [false, false, false, false, false, false, false, false, false])
    else (if b 9 = 0 then [false, false, false, false, false, false, false, false, false] else
    [false, false, false, false, false, false, false, false, false])) else (if b 8 = 0 then (if
    b 9 = 0 then [false, false, false, false, false, false, false, false, false] else [false,
    false, false, false, false, false, false, false, false]) else (if b 9 = 0 then [false,
    false, false, false, false, false, false, false, false] else [false, false, false, false,
    false, false, false, false, false]))))) else (if b 5 = 0 then (if b 6 = 0 then (if b 7 = 0
    then (if b 8 = 0 then (if b 9 = 0 then [false, false, false, false, false, false, false,
    false, false] else [false, false, false, false, false, false, false, false, false]) else
    (if b 9 = 0 then [false, false, false, false, false, false, false, false, false] else
    [false, false, false, false, false, false, false, false, false])) else (if b 8 = 0 then (if
    b 9 = 0 then [false, false, false, false, false, false, false, false, false] else [false,
    false, false, false, false, false, false, false, false]) else (if b 9 = 0 then [false,
    false, false, false, false, false, false, false, false] else [false, false, false, false,
    false, false, false, false, false]))) else (if b 7 = 0 then (if b 8 = 0 then (if b 9 = 0
    then [false, false, false, false, false, false, false, false, false] else [false, false,
    false, false, false, false, false, false, false]) else (if b 9 = 0 then [false, false,
    false, false, false, false, false, false, false] else [false, false, false, false, false,
    false, false, false, false])) else (if b 8 = 0 then (if b 9 = 0 then [false, false, false,
    false, false, false, false, false, false] else [false, false, false, false, false, false,
    false, false, false]) else (if b 9 = 0 then [false, false, false, false, false, false,
    false, false, false] else [false, false, false, false, false, false, false, false,
    false])))) else (if b 6 = 0 then (if b 7 = 0 then (if b 8 = 0 then (if b 9 = 0 then [false,
    false, false, false, false, false, false, false, false] else [false, false, false, false,
    false, false, false, false, false]) else (if b 9 = 0 then [false, false, false, false,
    false, false, false, false, false] else [false, false, false, false, false, false, false,
    false, false])) else (if b 8 = 0 then (if b 9 = 0 then [false, false, false, false, false,
    false, false, false, false] else [false, false, false, false, false, false, false, false,
    false]) else (if b 9 = 0 then [false, false, false, false, false, false, false, false,
    false] else [false, false, false, false, false, false, false, false, false]))) else (if b 7
    = 0 then (if b 8 = 0 then (if b 9 = 0 then [false, false, false, false, false, false,
    false, false, false] else [false, false, false, false, false, false, false, false, false])
    else (if b 9 = 0 then [false, false, false, false, false, false, false, false, false] else
    [false, false, false, false, false, false, false, false, false])) else (if b 8 = 0 then (if
    b 9 = 0 then [false, false, false, false, false, false, false, false, false] else [false,
    false, false, false, false, false, false, false, false]) else (if b 9 = 0 then [false,
    false, false, false, false, false, false, false, false] else [false, false, false, false,
    false, false, false, false, false]))))))) else (if b 3 = 0 then (if b 4 = 0 then (if b 5 =
    0 then (if b 6 = 0 then (if b 7 = 0 then (if b 8 = 0 then (if b 9 = 0 then [false, false,
    false, false, false, false, false, false, false] else [false, false, false, false, false,
    false, false, false, false]) else (if b 9 = 0 then [false, false, false, false, false,
    false, false, false, false] else [false, false, false, false, false, false, false, false,
    false])) else (if b 8 = 0 then (if b 9 = 0 then [false, false, false, false, false, false,
    false, false, false] else [false, false, false, false, false, false, false, false, false])
    else (if b 9 = 0 then [false, false, false, false, false, false, false, false, false] else
    [false, false, false, false, false, false, false, false, false]))) else (if b 7 = 0 then
    (if b 8 = 0 then (if b 9 = 0 then [false, false, false, false, false, false, false, false,
    false] else [false, false, false, false, false, false, false, false, false]) else (if b 9 =
    0 then [false, false, false, false, false, false, false, false, false] else [false, false,
    false, false, false, false, false, false, false])) else (if b 8 = 0 then (if b 9 = 0 then
    [false, false, false, false, false, false, false, false, false] else [false, false, false,
    false, false, false, false, false, false]) else (if b 9 = 0 then [false, false, false,
    false, false, false, false, false, false] else [false, false, false, false, false, false,
    false, false, false])))) else (if b 6 = 0 then (if b 7 = 0 then (if b 8 = 0 then (if b 9 =
    0 then [false, false, false, false, false, false, false, false, false] else [false, false,
    false, false, false, false, false, false, false]) else (if b 9 = 0 then [false, false,
    false, false, false, false, false, false, false] else [false, false, false, false, false,
    false, false, false, false])) else (if b 8 = 0 then (if b 9 = 0 then [false, false, false,
    false, false, false, false, false, false] else [false, false, false, false, false, false,
    false, false, false]) else (if b 9 = 0 then [false, false, false, false, false, false,
    false, false, false] else [false, false, false, false, false, false, false, false,
    false]))) else (if b 7 = 0 then (if b 8 = 0 then (if b 9 = 0 then [false, false, false,
    false, false, false, false, false, false] else [false, false, false, false, false, false,
    false, false, false]) else (if b 9 = 0 then [false, false, false, false, false, false,
    false, false, false] else [false, false, false, false, false, false, false, false, false]))
    else (if b 8 = 0 then (if b 9 = 0 then [false, false, false, false, false, false, false,
    false, false] else [false, false, false, false, false, false, false, false, false]) else
    (if b 9 = 0 then [false, false, false, false, false, false, false, false, false] else
    [false, false, false, false, false, false, false, false, false]))))) else (if b 5 = 0 then
    (if b 6 = 0 then (if b 7 = 0 then (if b 8 = 0 then (if b 9 = 0 then [false, false, false,
    false, false, false, false, false, false] else [false, false, false, false, false, false,
    false, false, false]) else (if b 9 = 0 then [false, false, false, false, false, false,
    false, false, false] else [false, false, false, false, false, false, false, false, false]))
    else (if b 8 = 0 then (if b 9 = 0 then [false, false, false, false, false, false, false,
    false, false] else [false, false, false, false, false, false, false, false, false]) else
    (if b 9 = 0 then [false, false, false, false, false, false, false, false, false] else
    [false, false, false, false, false, false, false, false, false]))) else (if b 7 = 0 then
    (if b 8 = 0 then (if b 9 = 0 then [false, false, false, false, false, false, false, false,
    false] else [false, false, false, false, false, false, false, false, false]) else (if b 9 =
    0 then [false, false, false, false, false, false, false, false, false] else [false, false,
    false, false, false, false, false, false, false])) else (if b 8 = 0 then (if b 9 = 0 then
    [false, false, false, false, false, false, false, false, false] else [false, false, false,
    false, false, false, false, false, false]) else (if b 9 = 0 then [false, false, false,
    false, false, false, false, false, false] else [false, false, false, false, false, false,
    false, false, false])))) else (if b 6 = 0 then (if b 7 = 0 then (if b 8 = 0 then (if b 9 =
    0 then [false, false, false, false, false, false, false, false, false] else [false, false,
    false, false, false, false, false, false, false]) else (if b 9 = 0 then [false, false,
    false, false, false, false, false, false, false] else [false, false, false, false, false,
    false, false, false, false])) else (if b 8 = 0 then (if b 9 = 0 then [false, false, false,
    false, false, false, false, false, false] else [false, false, false, false, false, false,
    false, false, false]) else (if b 9 = 0 then [false, false, false, false, false, false,
    false, false, false] else [false, false, false, false, false, false, false, false,
    false]))) else (if b 7 = 0 then (if b 8 = 0 then (if b 9 = 0 then [false, false, false,
    false, false, false, false, false, false] else [false, false, false, false, false, false,
    false, false, false]) else (if b 9 = 0 then [false, false, false, false, false, false,
    false, false, false] else [false, false, false, false, false, false, false, false, false]))
    else (if b 8 = 0 then (if b 9 = 0 then [false, false, false, false, false, false, false,
    false, false] else [false, false, false, false, false, false, false, false, false]) else
    (if b 9 = 0 then [false, false, false, false, false, false, false, false, false] else
    [false, false, false, false, false, false, false, false, false])))))) else (if b 4 = 0 then
    (if b 5 = 0 then (if b 6 = 0 then (if b 7 = 0 then (if b 8 = 0 then (if b 9 = 0 then
    [false, false, false, false, false, false, false, false, false] else [false, false, false,
    false, false, false, false, false, false]) else (if b 9 = 0 then [false, false, false,
    false, false, false, false, false, false] else [false, false, false, false, false, false,
    false, false, false])) else (if b 8 = 0 then (if b 9 = 0 then [false, false, false, false,
    false, false, false, false, false] else [false, false, false, false, false, false, false,
    false, false]) else (if b 9 = 0 then [false, false, false, false, false, false, false,
    false, false] else [false, false, false, false, false, false, false, false, false]))) else
    (if b 7 = 0 then (if b 8 = 0 then (if b 9 = 0 then [false, false, false, false, false,
    false, false, false, false] else [false, false, false, false, false, false, false, false,
    false]) else (if b 9 = 0 then [false, false, false, false, false, false, false, false,
    false] else [false, false, false, false, false, false, false, false, false])) else (if b 8
    = 0 then (if b 9 = 0 then [false, false, false, false, false, false, false, false, false]
    else [false, false, false, false, false, false, false, false, false]) else (if b 9 = 0 then
    [false, false, false, false, false, false, false, false, false] else [false, false, false,
    false, false, false, false, false, false])))) else (if b 6 = 0 then (if b 7 = 0 then (if b
    8 = 0 then (if b 9 = 0 then [false, false, false, false, false, false, false, false, false]
    else [false, false, false, false, false, false, false, false, false]) else (if b 9 = 0 then
    [false, false, false, false, false, false, false, false, false] else [false, false, false,
    false, false, false, false, false, false])) else (if b 8 = 0 then (if b 9 = 0 then [false,
    false, false, false, false, false, false, false, false] else [false, false, false, false,
    false, false, false, false, false]) else (if b 9 = 0 then [false, false, false, false,
    false, false, false, false, false] else [false, false, false, false, false, false, false,
    false, false]))) else (if b 7 = 0 then (if b 8 = 0 then (if b 9 = 0 then [false, false,
    false, false, false, false, false, false, false] else [false, false, false, false, false,
    false, false, false, false]) else (if b 9 = 0 then [false, false, false, false, false,
    false, false, false, false] else [false, false, false, false, false, false, false, false,
    false])) else (if b 8 = 0 then (if b 9 = 0 then [false, false, false, false, false, false,
    false, false, false] else [false, false, false, false, false, false, false, false, false])
    else (if b 9 = 0 then [false, false, false, false, false, false, false, false, false] else
    [false, false, false, false, false, false, false, false, false]))))) else (if b 5 = 0 then
    (if b 6 = 0 then (if b 7 = 0 then (if b 8 = 0 then (if b 9 = 0 then [false, false, false,
    false, false, false, false, false, false] else [false, false, false, false, false, false,
    false, false, false]) else (if b 9 = 0 then [false, false, false, false, false, false,
    false, false, false] else [false, false, false, false, false, false, false, false, false]))
    else (if b 8 = 0 then (if b 9 = 0 then [false, false, false, false, false, false, false,
    false, false] else [false, false, false, false, false, false, false, false, false]) else
    (if b 9 = 0 then [false, false, false, false, false, false, false, false, false] else
    [false, false, false, false, false, false, false, false, false]))) else (if b 7 = 0 then
    (if b 8 = 0 then (if b 9 = 0 then [false, false, false, false, false, false, false, false,
    false] else [false, false, false, false, false, false, false, false, false]) else (if b 9 =
    0 then [false, false, false, false, false, false, false, false, false] else [false, false,
    false, false, false, false, false, false, false])) else (if b 8 = 0 then (if b 9 = 0 then
    [false, false, false, false, false, false, false, false, false] else [false, false, false,
    false, false, false, false, false, false]) else (if b 9 = 0 then [false, false, false,
    false, false, false, false, false, false] else [false, false, false, false, false, false,
    false, false, false])))) else (if b 6 = 0 then (if b 7 = 0 then (if b 8 = 0 then (if b 9 =
    0 then [false, false, false, false, false, false, false, false, false] else [false, false,
    false, false, false, false, false, false, false]) else (if b 9 = 0 then [false, false,
    false, false, false, false, false, false, false] else [false, false, false, false, false,
    false, false, false, false])) else (if b 8 = 0 then (if b 9 = 0 then [false, false, false,
    false, false, false, false, false, false] else [false, false, false, false, false, false,
    false, false, false]) else (if b 9 = 0 then [false, false, false, false, false, false,
    false, false, false] else [false, false, false, false, false, false, false, false,
    false]))) else (if b 7 = 0 then (if b 8 = 0 then (if b 9 = 0 then [false, false, false,
    false, false, false, false, false, false] else [false, false, false, false, false, false,
    false, false, false]) else (if b 9 = 0 then [false, false, false, false, false, false,
    false, false, false] else [false, false, false, false, false, false, false, false, false]))
    else (if b 8 = 0 then (if b 9 = 0 then [false, false, false, false, false, false, false,
    false, false] else [false, false, false, false, false, false, false, false, false]) else
    (if b 9 = 0 then [false, false, false, false, false, false, false, false, false] else
    [false, false, false, false, false, false, false, false, false])))))))) else (if b 2 = 0
    then (if b 3 = 0 then (if b 4 = 0 then (if b 5 = 0 then (if b 6 = 0 then (if b 7 = 0 then
    (if b 8 = 0 then (if b 9 = 0 then [true, false, false, false, false, false, false, true,
    false] else [false, false, false, false, true, false, false, true, false]) else (if b 9 = 0
    then [false, false, true, false, false, false, false, true, false] else [true, false, true,
    false, true, false, false, true, false])) else (if b 8 = 0 then (if b 9 = 0 then [false,
    true, false, false, false, false, false, true, false] else [true, true, false, false, true,
    false, false, true, false]) else (if b 9 = 0 then [true, true, true, false, false, false,
    false, true, false] else [false, true, true, false, true, false, false, true, false])))
    else (if b 7 = 0 then (if b 8 = 0 then (if b 9 = 0 then [false, true, false, true, false,
    false, false, true, true] else [true, true, false, true, true, false, false, true, true])
    else (if b 9 = 0 then [true, true, true, true, false, false, false, true, true] else
    [false, true, true, true, true, false, false, true, true])) else (if b 8 = 0 then (if b 9 =
    0 then [true, false, false, true, false, false, false, true, true] else [false, false,
    false, true, true, false, false, true, true]) else (if b 9 = 0 then [false, false, true,
    true, false, false, false, true, true] else [true, false, true, true, true, false, false,
    true, true])))) else (if b 6 = 0 then (if b 7 = 0 then (if b 8 = 0 then (if b 9 = 0 then
    [true, true, false, true, false, false, false, true, true] else [false, true, false, true,
    true, false, false, true, true]) else (if b 9 = 0 then [false, true, true, true, false,
    false, false, true, true] else [true, true, true, true, true, false, false, true, true]))
    else (if b 8 = 0 then (if b 9 = 0 then [false, false, false, true, false, false, false,
    true, true] else [true, false, false, true, true, false, false, true, true]) else (if b 9 =
    0 then [true, false, true, true, false, false, false, true, true] else [false, false, true,
    true, true, false, false, true, true]))) else (if b 7 = 0 then (if b 8 = 0 then (if b 9 = 0
    then [false, false, false, false, false, false, false, true, false] else [true, false,
    false, false, true, false, false, true, false]) else (if b 9 = 0 then [true, false, true,
    false, false, false, false, true, false] else [false, false, true, false, true, false,
    false, true, false])) else (if b 8 = 0 then (if b 9 = 0 then [true, true, false, false,
    false, false, false, true, false] else [false, true, false, false, true, false, false,
    true, false]) else (if b 9 = 0 then [false, true, true, false, false, false, false, true,
    false] else [true, true, true, false, true, false, false, true, false]))))) else (if b 5 =
    0 then (if b 6 = 0 then (if b 7 = 0 then (if b 8 = 0 then (if b 9 = 0 then [false, false,
    false, true, false, false, false, true, false] else [true, false, false, true, true, false,
    false, true, false]) else (if b 9 = 0 then [true, false, true, true, false, false, false,
    true, false] else [false, false, true, true, true, false, false, true, false])) else (if b
    8 = 0 then (if b 9 = 0 then [true, true, false, true, false, false, false, true, false]
    else [false, true, false, true, true, false, false, true, false]) else (if b 9 = 0 then
    [false, true, true, true, false, false, false, true, false] else [true, true, true, true,
    true, false, false, true, false]))) else (if b 7 = 0 then (if b 8 = 0 then (if b 9 = 0 then
    [true, true, false, false, false, false, false, true, true] else [false, true, false,
    false, true, false, false, true, true]) else (if b 9 = 0 then [false, true, true, false,
    false, false, false, true, true] else [true, true, true, false, true, false, false, true,
    true])) else (if b 8 = 0 then (if b 9 = 0 then [false, false, false, false, false, false,
    false, true, true] else [true, false, false, false, true, false, false, true, true]) else
    (if b 9 = 0 then [true, false, true, false, false, false, false, true, true] else [false,
    false, true, false, true, false, false, true, true])))) else (if b 6 = 0 then (if b 7 = 0
    then (if b 8 = 0 then (if b 9 = 0 then [false, true, false, false, false, false, false,
    true, true] else [true, true, false, false, true, false, false, true, true]) else (if b 9 =
    0 then [true, true, true, false, false, false, false, true, true] else [false, true, true,
    false, true, false, false, true, true])) else (if b 8 = 0 then (if b 9 = 0 then [true,
    false, false, false, false, false, false, true, true] else [false, false, false, false,
    true, false, false, true, true]) else (if b 9 = 0 then [false, false, true, false, false,
    false, false, true, true] else [true, false, true, false, true, false, false, true,
    true]))) else (if b 7 = 0 then (if b 8 = 0 then (if b 9 = 0 then [true, false, false, true,
    false, false, false, true, false] else [false, false, false, true, true, false, false,
    true, false]) else (if b 9 = 0 then [false, false, true, true, false, false, false, true,
    false] else [true, false, true, true, true, false, false, true, false])) else (if b 8 = 0
    then (if b 9 = 0 then [false, true, false, true, false, false, false, true, false] else
    [true, true, false, true, true, false, false, true, false]) else (if b 9 = 0 then [true,
    true, true, true, false, false, false, true, false] else [false, true, true, true, true,
    false, false, true, false])))))) else (if b 4 = 0 then (if b 5 = 0 then (if b 6 = 0 then
    (if b 7 = 0 then (if b 8 = 0 then (if b 9 = 0 then [false, false, false, false, false,
    true, false, true, false] else [true, false, false, false, true, true, false, true, false])
    else (if b 9 = 0 then [true, false, true, false, false, true, false, true, false] else
    [false, false, true, false, true, true, false, true, false])) else (if b 8 = 0 then (if b 9
    = 0 then [true, true, false, false, false, true, false, true, false] else [false, true,
    false, false, true, true, false, true, false]) else (if b 9 = 0 then [false, true, true,
    false, false, true, false, true, false] else [true, true, true, false, true, true, false,
    true, false]))) else (if b 7 = 0 then (if b 8 = 0 then (if b 9 = 0 then [true, true, false,
    true, false, true, false, true, true] else [false, true, false, true, true, true, false,
    true, true]) else (if b 9 = 0 then [false, true, true, true, false, true, false, true,
    true] else [true, true, true, true, true, true, false, true, true])) else (if b 8 = 0 then
    (if b 9 = 0 then [false, false, false, true, false, true, false, true, true] else [true,
    false, false, true, true, true, false, true, true]) else (if b 9 = 0 then [true, false,
    true, true, false, true, false, true, true] else [false, false, true, true, true, true,
    false, true, true])))) else (if b 6 = 0 then (if b 7 = 0 then (if b 8 = 0 then (if b 9 = 0
    then [false, true, false, true, false, true, false, true, true] else [true, true, false,
    true, true, true, false, true, true]) else (if b 9 = 0 then [true, true, true, true, false,
    true, false, true, true] else [false, true, true, true, true, true, false, true, true]))
    else (if b 8 = 0 then (if b 9 = 0 then [true, false, false, true, false, true, false, true,
    true] else [false, false, false, true, true, true, false, true, true]) else (if b 9 = 0
    then [false, false, true, true, false, true, false, true, true] else [true, false, true,
    true, true, true, false, true, true]))) else (if b 7 = 0 then (if b 8 = 0 then (if b 9 = 0
    then [true, false, false, false, false, true, false, true, false] else [false, false,
    false, false, true, true, false, true, false]) else (if b 9 = 0 then [false, false, true,
    false, false, true, false, true, false] else [true, false, true, false, true, true, false,
    true, false])) else (if b 8 = 0 then (if b 9 = 0 then [false, true, false, false, false,
    true, false, true, false] else [true, true, false, false, true, true, false, true, false])
    else (if b 9 = 0 then [true, true, true, false, false, true, false, true, false] else
    [false, true, true, false, true, true, false, true, false]))))) else (if b 5 = 0 then (if b
    6 = 0 then (if b 7 = 0 then (if b 8 = 0 then (if b 9 = 0 then [true, false, false, true,
    false, true, false, true, false] else [false, false, false, true, true, true, false, true,
    false]) else (if b 9 = 0 then [false, false, true, true, false, true, false, true, false]
    else [true, false, true, true, true, true, false, true, false])) else (if b 8 = 0 then (if
    b 9 = 0 then [false, true, false, true, false, true, false, true, false] else [true, true,
    false, true, true, true, false, true, false]) else (if b 9 = 0 then [true, true, true,
    true, false, true, false, true, false] else [false, true, true, true, true, true, false,
    true, false]))) else (if b 7 = 0 then (if b 8 = 0 then (if b 9 = 0 then [false, true,
    false, false, false, true, false, true, true] else [true, true, false, false, true, true,
    false, true, true]) else (if b 9 = 0 then [true, true, true, false, false, true, false,
    true, true] else [false, true, true, false, true, true, false, true, true])) else (if b 8 =
    0 then (if b 9 = 0 then [true, false, false, false, false, true, false, true, true] else
    [false, false, false, false, true, true, false, true, true]) else (if b 9 = 0 then [false,
    false, true, false, false, true, false, true, true] else [true, false, true, false, true,
    true, false, true, true])))) else (if b 6 = 0 then (if b 7 = 0 then (if b 8 = 0 then (if b
    9 = 0 then [true, true, false, false, false, true, false, true, true] else [false, true,
    false, false, true, true, false, true, true]) else (if b 9 = 0 then [false, true, true,
    false, false, true, false, true, true] else [true, true, true, false, true, true, false,
    true, true])) else (if b 8 = 0 then (if b 9 = 0 then [false, false, false, false, false,
    true, false, true, true] else [true, false, false, false, true, true, false, true, true])
    else (if b 9 = 0 then [true, false, true, false, false, true, false, true, true] else
    [false, false, true, false, true, true, false, true, true]))) else (if b 7 = 0 then (if b 8
    = 0 then (if b 9 = 0 then [false, false, false, true, false, true, false, true, false] else
    [true, false, false, true, true, true, false, true, false]) else (if b 9 = 0 then [true,
    false, true, true, false, true, false, true, false] else [false, false, true, true, true,
    true, false, true, false])) else (if b 8 = 0 then (if b 9 = 0 then [true, true, false,
    true, false, true, false, true, false] else [false, true, false, true, true, true, false,
    true, false]) else (if b 9 = 0 then [false, true, true, true, false, true, false, true,
    false] else [true, true, true, true, true, true, false, true, false]))))))) else (if b 3 =
    0 then (if b 4 = 0 then (if b 5 = 0 then (if b 6 = 0 then (if b 7 = 0 then (if b 8 = 0 then
    (if b 9 = 0 then [false, false, false, false, false, false, true, true, false] else [true,
    false, false, false, true, false, true, true, false]) else (if b 9 = 0 then [true, false,
    true, false, false, false, true, true, false] else [false, false, true, false, true, false,
    true, true, false])) else (if b 8 = 0 then (if b 9 = 0 then [true, true, false, false,
    false, false, true, true, false] else [false, true, false, false, true, false, true, true,
    false]) else (if b 9 = 0 then [false, true, true, false, false, false, true, true, false]
    else [true, true, true, false, true, false, true, true, false]))) else (if b 7 = 0 then (if
    b 8 = 0 then (if b 9 = 0 then [true, true, false, true, false, false, true, true, true]
    else [false, true, false, true, true, false, true, true, true]) else (if b 9 = 0 then
    [false, true, true, true, false, false, true, true, true] else [true, true, true, true,
    true, false, true, true, true])) else (if b 8 = 0 then (if b 9 = 0 then [false, false,
    false, true, false, false, true, true, true] else [true, false, false, true, true, false,
    true, true, true]) else (if b 9 = 0 then [true, false, true, true, false, false, true,
    true, true] else [false, false, true, true, true, false, true, true, true])))) else (if b 6
    = 0 then (if b 7 = 0 then (if b 8 = 0 then (if b 9 = 0 then [false, true, false, true,
    false, false, true, true, true] else [true, true, false, true, true, false, true, true,
    true]) else (if b 9 = 0 then [true, true, true, true, false, false, true, true, true] else
    [false, true, true, true, true, false, true, true, true])) else (if b 8 = 0 then (if b 9 =
    0 then [true, false, false, true, false, false, true, true, true] else [false, false,
    false, true, true, false, true, true, true]) else (if b 9 = 0 then [false, false, true,
    true, false, false, true, true, true] else [true, false, true, true, true, false, true,
    true, true]))) else (if b 7 = 0 then (if b 8 = 0 then (if b 9 = 0 then [true, false, false,
    false, false, false, true, true, false] else [false, false, false, false, true, false,
    true, true, false]) else (if b 9 = 0 then [false, false, true, false, false, false, true,
    true, false] else [true, false, true, false, true, false, true, true, false])) else (if b 8
    = 0 then (if b 9 = 0 then [false, true, false, false, false, false, true, true, false] else
    [true, true, false, false, true, false, true, true, false]) else (if b 9 = 0 then [true,
    true, true, false, false, false, true, true, false] else [false, true, true, false, true,
    false, true, true, false]))))) else (if b 5 = 0 then (if b 6 = 0 then (if b 7 = 0 then (if
    b 8 = 0 then (if b 9 = 0 then [true, false, false, true, false, false, true, true, false]
    else [false, false, false, true, true, false, true, true, false]) else (if b 9 = 0 then
    [false, false, true, true, false, false, true, true, false] else [true, false, true, true,
    true, false, true, true, false])) else (if b 8 = 0 then (if b 9 = 0 then [false, true,
    false, true, false, false, true, true, false] else [true, true, false, true, true, false,
    true, true, false]) else (if b 9 = 0 then [true, true, true, true, false, false, true,
    true, false] else [false, true, true, true, true, false, true, true, false]))) else (if b 7
    = 0 then (if b 8 = 0 then (if b 9 = 0 then [false, true, false, false, false, false, true,
    true, true] else [true, true, false, false, true, false, true, true, true]) else (if b 9 =
    0 then [true, true, true, false, false, false, true, true, true] else [false, true, true,
    false, true, false, true, true, true])) else (if b 8 = 0 then (if b 9 = 0 then [true,
    false, false, false, false, false, true, true, true] else [false, false, false, false,
    true, false, true, true, true]) else (if b 9 = 0 then [false, false, true, false, false,
    false, true, true, true] else [true, false, true, false, true, false, true, true, true]))))
    else (if b 6 = 0 then (if b 7 = 0 then (if b 8 = 0 then (if b 9 = 0 then [true, true,
    false, false, false, false, true, true, true] else [false, true, false, false, true, false,
    true, true, true]) else (if b 9 = 0 then [false, true, true, false, false, false, true,
    true, true] else [true, true, true, false, true, false, true, true, true])) else (if b 8 =
    0 then (if b 9 = 0 then [false, false, false, false, false, false, true, true, true] else
    [true, false, false, false, true, false, true, true, true]) else (if b 9 = 0 then [true,
    false, true, false, false, false, true, true, true] else [false, false, true, false, true,
    false, true, true, true]))) else (if b 7 = 0 then (if b 8 = 0 then (if b 9 = 0 then [false,
    false, false, true, false, false, true, true, false] else [true, false, false, true, true,
    false, true, true, false]) else (if b 9 = 0 then [true, false, true, true, false, false,
    true, true, false] else [false, false, true, true, true, false, true, true, false])) else
    (if b 8 = 0 then (if b 9 = 0 then [true, true, false, true, false, false, true, true,
    false] else [false, true, false, true, true, false, true, true, false]) else (if b 9 = 0
    then [false, true, true, true, false, false, true, true, false] else [true, true, true,
    true, true, false, true, true, false])))))) else (if b 4 = 0 then (if b 5 = 0 then (if b 6
    = 0 then (if b 7 = 0 then (if b 8 = 0 then (if b 9 = 0 then [true, false, false, false,
    false, true, true, true, false] else [false, false, false, false, true, true, true, true,
    false]) else (if b 9 = 0 then [false, false, true, false, false, true, true, true, false]
    else [true, false, true, false, true, true, true, true, false])) else (if b 8 = 0 then (if
    b 9 = 0 then [false, true, false, false, false, true, true, true, false] else [true, true,
    false, false, true, true, true, true, false]) else (if b 9 = 0 then [true, true, true,
    false, false, true, true, true, false] else [false, true, true, false, true, true, true,
    true, false]))) else (if b 7 = 0 then (if b 8 = 0 then (if b 9 = 0 then [false, true,
    false, true, false, true, true, true, true] else [true, true, false, true, true, true,
    true, true, true]) else (if b 9 = 0 then [true, true, true, true, false, true, true, true,
    true] else [false, true, true, true, true, true, true, true, true])) else (if b 8 = 0 then
    (if b 9 = 0 then [true, false, false, true, false, true, true, true, true] else [false,
    false, false, true, true, true, true, true, true]) else (if b 9 = 0 then [false, false,
    true, true, false, true, true, true, true] else [true, false, true, true, true, true, true,
    true, true])))) else (if b 6 = 0 then (if b 7 = 0 then (if b 8 = 0 then (if b 9 = 0 then
    [true, true, false, true, false, true, true, true, true] else [false, true, false, true,
    true, true, true, true, true]) else (if b 9 = 0 then [false, true, true, true, false, true,
    true, true, true] else [true, true, true, true, true, true, true, true, true])) else (if b
    8 = 0 then (if b 9 = 0 then [false, false, false, true, false, true, true, true, true] else
    [true, false, false, true, true, true, true, true, true]) else (if b 9 = 0 then [true,
    false, true, true, false, true, true, true, true] else [false, false, true, true, true,
    true, true, true, true]))) else (if b 7 = 0 then (if b 8 = 0 then (if b 9 = 0 then [false,
    false, false, false, false, true, true, true, false] else [true, false, false, false, true,
    true, true, true, false]) else (if b 9 = 0 then [true, false, true, false, false, true,
    true, true, false] else [false, false, true, false, true, true, true, true, false])) else
    (if b 8 = 0 then (if b 9 = 0 then [true, true, false, false, false, true, true, true,
    false] else [false, true, false, false, true, true, true, true, false]) else (if b 9 = 0
    then [false, true, true, false, false, true, true, true, false] else [true, true, true,
    false, true, true, true, true, false]))))) else (if b 5 = 0 then (if b 6 = 0 then (if b 7 =
    0 then (if b 8 = 0 then (if b 9 = 0 then [false, false, false, true, false, true, true,
    true, false] else [true, false, false, true, true, true, true, true, false]) else (if b 9 =
    0 then [true, false, true, true, false, true, true, true, false] else [false, false, true,
    true, true, true, true, true, false])) else (if b 8 = 0 then (if b 9 = 0 then [true, true,
    false, true, false, true, true, true, false] else [false, true, false, true, true, true,
    true, true, false]) else (if b 9 = 0 then [false, true, true, true, false, true, true,
    true, false] else [true, true, true, true, true, true, true, true, false]))) else (if b 7 =
    0 then (if b 8 = 0 then (if b 9 = 0 then [true, true, false, false, false, true, true,
    true, true] else [false, true, false, false, true, true, true, true, true]) else (if b 9 =
    0 then [false, true, true, false, false, true, true, true, true] else [true, true, true,
    false, true, true, true, true, true])) else (if b 8 = 0 then (if b 9 = 0 then [false,
    false, false, false, false, true, true, true, true] else [true, false, false, false, true,
    true, true, true, true]) else (if b 9 = 0 then [true, false, true, false, false, true,
    true, true, true] else [false, false, true, false, true, true, true, true, true])))) else
    (if b 6 = 0 then (if b 7 = 0 then (if b 8 = 0 then (if b 9 = 0 then [false, true, false,
    false, false, true, true, true, true] else [true, true, false, false, true, true, true,
    true, true]) else (if b 9 = 0 then [true, true, true, false, false, true, true, true, true]
    else [false, true, true, false, true, true, true, true, true])) else (if b 8 = 0 then (if b
    9 = 0 then [true, false, false, false, false, true, true, true, true] else [false, false,
    false, false, true, true, true, true, true]) else (if b 9 = 0 then [false, false, true,
    false, false, true, true, true, true] else [true, false, true, false, true, true, true,
    true, true]))) else (if b 7 = 0 then (if b 8 = 0 then (if b 9 = 0 then [true, false, false,
    true, false, true, true, true, false] else [false, false, false, true, true, true, true,
    true, false]) else (if b 9 = 0 then [false, false, true, true, false, true, true, true,
    false] else [true, false, true, true, true, true, true, true, false])) else (if b 8 = 0
    then (if b 9 = 0 then [false, true, false, true, false, true, true, true, false] else
    [true, true, false, true, true, true, true, true, false]) else (if b 9 = 0 then [true,
    true, true, true, false, true, true, true, false] else [false, true, true, true, true,
    true, true, true, false]))))))))))

@[expose] def ySubsetSum : List (Fin 10 → ZMod 2) → List Bool → Fin 10 → ZMod 2
  | [], _ => 0
  | v :: vs, [] => ySubsetSum vs []
  | v :: vs, true :: ms => v + ySubsetSum vs ms
  | v :: vs, false :: ms => ySubsetSum vs ms

theorem ySubsetSum_mem_of_closed {T : Set (Fin 10 → ZMod 2)}
    (h0 : (0 : Fin 10 → ZMod 2) ∈ T) (hadd : ∀ u ∈ T, ∀ v ∈ T, u + v ∈ T)
    {L : List (Fin 10 → ZMod 2)} (hL : ∀ v ∈ L, v ∈ T) :
    ∀ m : List Bool, ySubsetSum L m ∈ T := by
  induction L with
  | nil =>
    intro m
    cases m <;> simpa [ySubsetSum] using h0
  | cons v vs ih =>
    intro m
    cases m with
    | nil => exact ih (fun w hw => hL w (List.mem_cons_of_mem _ hw)) []
    | cons b ms =>
      cases b with
      | false => exact ih (fun w hw => hL w (List.mem_cons_of_mem _ hw)) ms
      | true => exact hadd v (hL v List.mem_cons_self) _
                  (ih (fun w hw => hL w (List.mem_cons_of_mem _ hw)) ms)

theorem ySpan0_check : ∀ b : Fin 10 → Fin 2, yB (yOf2 b) yY = 0 →
    yOf2 b = ySubsetSum ySpanVecs0 (yMaskOf0 b) := by
  decide +kernel

theorem ySpan1_check : ∀ b : Fin 10 → Fin 2, yB (yOf2 b) yY = 0 →
    yOf2 b = ySubsetSum ySpanVecs1 (yMaskOf1 b) := by
  decide +kernel

theorem yS0Roots_mem_levelZero : ∀ α ∈ yS0Roots, α ∈ yLevelZeroRoots := by
  decide +kernel

theorem yS0Root_mem_levelZero {p : YRootTable} (hp : p ∈ yS0RootData) :
    p.root ∈ yLevelZeroRoots :=
  yS0Roots_mem_levelZero p.root (List.mem_map_of_mem hp)

end CFSG.SeitzReduction.E7Pilot
