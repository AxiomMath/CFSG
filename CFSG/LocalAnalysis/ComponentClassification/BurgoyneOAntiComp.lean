module

public import CFSG.LocalAnalysis.ComponentClassification.BurgoyneOCentFix
public import CFSG.LieType.Universal.SpecialLinear
public import CFSG.LocalAnalysis.ComponentClassification.BurgoyneOEAlg

public noncomputable section

namespace CFSG.ComponentClassification.Burgoyne.O

open Matrix CFSG Subgroup
open scoped commutatorElement MatrixGroups

variable {K : Type} [Field K] {n : ℕ}

@[expose] def pairM (X X' : Matrix (Fin n) (Fin n) K) : Matrix (Fin n) (Fin n) (K × K) :=
  Matrix.of fun i j => (X i j, X' i j)

theorem pairM_mul (X X' Y Y' : Matrix (Fin n) (Fin n) K) :
    pairM X X' * pairM Y Y' = pairM (X * Y) (X' * Y') := by
  ext i j
  · simp [pairM, Matrix.mul_apply, Prod.fst_sum]
  · simp [pairM, Matrix.mul_apply, Prod.snd_sum]

theorem pairM_one : pairM (1 : Matrix (Fin n) (Fin n) K) 1 = 1 := by
  ext i j <;> by_cases h : i = j <;> simp [pairM, one_apply, h]

omit [Field K] in
theorem pairM_transpose (X X' : Matrix (Fin n) (Fin n) K) :
    (pairM X X')ᵀ = pairM Xᵀ X'ᵀ := by
  ext i j <;> rfl

theorem pairM_map_swap (X X' : Matrix (Fin n) (Fin n) K) :
    (pairM X X').map swapS = pairM X' X := by
  ext i j <;> rfl

omit [Field K] in
theorem eq_pairM (Y : Matrix (Fin n) (Fin n) (K × K)) :
    Y = pairM (Y.map Prod.fst) (Y.map Prod.snd) := by
  ext i j <;> rfl

omit [Field K] in
theorem pairM_injective {X X' Y Y' : Matrix (Fin n) (Fin n) K} (h : pairM X X' = pairM Y Y') :
    X = Y ∧ X' = Y' := by
  constructor
  · ext i j
    exact congrArg Prod.fst (congrFun (congrFun h i) j)
  · ext i j
    exact congrArg Prod.snd (congrFun (congrFun h i) j)

theorem pairM_val_inv (X : GL (Fin n) K) :
    pairM (X : Matrix (Fin n) (Fin n) K) ((X⁻¹ : GL (Fin n) K) : Matrix (Fin n) (Fin n) K)ᵀ *
      pairM ((X⁻¹ : GL (Fin n) K) : Matrix (Fin n) (Fin n) K) (X : Matrix (Fin n) (Fin n) K)ᵀ =
        1 := by
  rw [pairM_mul, ← transpose_mul, ← Units.val_mul, mul_inv_cancel, Units.val_one, transpose_one,
    pairM_one]

@[expose] def iotaS (n : ℕ) : GL (Fin n) K →* GL (Fin n) (K × K) where
  toFun X := ⟨pairM X ((X⁻¹ : GL (Fin n) K) : Matrix (Fin n) (Fin n) K)ᵀ,
    pairM ((X⁻¹ : GL (Fin n) K) : Matrix (Fin n) (Fin n) K) (X : Matrix (Fin n) (Fin n) K)ᵀ,
    pairM_val_inv X, by simpa using pairM_val_inv X⁻¹⟩
  map_one' := Units.ext (by simp [pairM_one])
  map_mul' X Y := by
    apply Units.ext
    change pairM ((X * Y : GL (Fin n) K) : Matrix (Fin n) (Fin n) K)
        (((X * Y)⁻¹ : GL (Fin n) K) : Matrix (Fin n) (Fin n) K)ᵀ =
      pairM (X : Matrix (Fin n) (Fin n) K) ((X⁻¹ : GL (Fin n) K) : Matrix (Fin n) (Fin n) K)ᵀ *
        pairM (Y : Matrix (Fin n) (Fin n) K) ((Y⁻¹ : GL (Fin n) K) : Matrix (Fin n) (Fin n) K)ᵀ
    rw [pairM_mul, _root_.mul_inv_rev, Units.val_mul, Units.val_mul, transpose_mul]

theorem coe_iotaS (X : GL (Fin n) K) :
    ((iotaS n X : GL (Fin n) (K × K)) : Matrix (Fin n) (Fin n) (K × K)) =
      pairM X ((X⁻¹ : GL (Fin n) K) : Matrix (Fin n) (Fin n) K)ᵀ := rfl

theorem iotaS_injective : Function.Injective (iotaS (K := K) n) := by
  intro X Y h
  have e := congrArg Units.val h
  rw [coe_iotaS, coe_iotaS] at e
  exact Units.ext (pairM_injective e).1

theorem iotaS_mem (X : GL (Fin n) K) :
    iotaS n X ∈ uGrp swapS (1 : Matrix (Fin n) (Fin n) (K × K)) := by
  rw [mem_uGrp, Matrix.mul_one, coe_iotaS, pairM_map_swap, pairM_transpose, transpose_transpose,
    pairM_mul, ← transpose_mul, ← Units.val_mul, inv_mul_cancel, Units.val_one, transpose_one,
    pairM_one]

theorem eq_iota_of_mem {Y : GL (Fin n) (K × K)}
    (hY : Y ∈ uGrp swapS (1 : Matrix (Fin n) (Fin n) (K × K))) :
    ∃ X : GL (Fin n) K, iotaS n X = Y := by
  rw [mem_uGrp, Matrix.mul_one] at hY
  set Y₁ := (Y : Matrix (Fin n) (Fin n) (K × K)).map Prod.fst with hY₁
  set Y₂ := (Y : Matrix (Fin n) (Fin n) (K × K)).map Prod.snd with hY₂
  have hY' : (Y : Matrix (Fin n) (Fin n) (K × K)) = pairM Y₁ Y₂ := eq_pairM _
  rw [hY', pairM_map_swap, pairM_transpose, pairM_mul, ← pairM_one] at hY
  obtain ⟨h1, h2⟩ := pairM_injective hY
  have h3 : Y₁ * Y₂ᵀ = 1 := mul_eq_one_comm.1 h1
  set X : GL (Fin n) K := ⟨Y₁, Y₂ᵀ, h3, h1⟩ with hX
  refine ⟨X, Units.ext ?_⟩
  rw [coe_iotaS, hY']
  rfl

theorem commutator_uGrp_swap_eq (hn : 3 ≤ n) :
    ⁅uGrp swapS (1 : Matrix (Fin n) (Fin n) (K × K)),
        uGrp swapS (1 : Matrix (Fin n) (Fin n) (K × K))⁆ =
      ((iotaS n).comp (SpecialLinearGroup.toGL : SL(n, K) →* GL (Fin n) K)).range := by
  apply le_antisymm
  · rw [Subgroup.commutator_le]
    intro a ha b hb
    obtain ⟨x, rfl⟩ := eq_iota_of_mem ha
    obtain ⟨y, rfl⟩ := eq_iota_of_mem hb
    rw [← map_commutatorElement]
    have hdet : ((⁅x, y⁆ : GL (Fin n) K) : Matrix (Fin n) (Fin n) K).det = 1 := by
      rw [← GeneralLinearGroup.val_det_apply, map_commutatorElement,
        commutatorElement_eq_one_iff_mul_comm.2 (mul_comm _ _), Units.val_one]
    let g : SL(n, K) := ⟨_, hdet⟩
    refine ⟨g, ?_⟩
    change iotaS n (SpecialLinearGroup.toGL g) = _
    congr 1
    exact Units.ext rfl
  · have hperf : Group.IsPerfect (SL(n, K)) :=
      CFSG.ClassicalModels.specialLinear_isPerfect_of_three_le hn
    rw [MonoidHom.range_eq_map, ← hperf.commutator_eq_top, _root_.commutator_def,
      Subgroup.map_commutator]
    have hle : (⊤ : Subgroup (SL(n, K))).map ((iotaS n).comp SpecialLinearGroup.toGL) ≤
        uGrp swapS (1 : Matrix (Fin n) (Fin n) (K × K)) := by
      rintro _ ⟨x, -, rfl⟩
      exact iotaS_mem _
    exact commutator_mono hle hle

theorem compData_anti [Finite K] (h2 : (2 : K) ≠ 0) {s : K} (hs : s ≠ 0) (hn : 3 ≤ n)
    {R A : GL (Fin (2 * n)) K}
    (hR : (R : Matrix (Fin (2 * n)) (Fin (2 * n)) K) = blkDiag n (wMat 1 (-(s ^ 2))))
    (hA : (A : Matrix (Fin (2 * n)) (Fin (2 * n)) K) = blkDiag n (jMat (s ^ 2))) :
    CompData ⁅isoCent R A, isoCent R A⁆ := by
  have hc0 : s ^ 2 ≠ 0 := pow_ne_zero 2 hs
  have hW₀ : wMat 1 (-(s ^ 2)⁻¹) * wMat 1 (-(s ^ 2)) = 1 := by
    rw [wMat, wMat, diagonal_mul_diagonal, ← diagonal_one]
    congr 1
    ext i
    fin_cases i <;> simp [hc0]
  have hRG : (R : Matrix (Fin (2 * n)) (Fin (2 * n)) K) =
      blkDiag n (wMat 1 (-(s ^ 2))) * resMat (phiS h2 hs).toRingHom n 1 := by
    rw [map_one, Matrix.mul_one, hR]
  have hZ := commutator_iso_inf_centralizer_eq (φ := (phiS h2 hs).toRingHom) (σ := swapS)
    (r := (s, -s)) (phiS_injective h2 hs) hW₀ (fun x => transpose_phiS_mul h2 hs x)
    (phiS_root h2 hs) (fun M hM => phiS_mem_range h2 hs hM) 1 hRG hA
  rw [hZ, commutator_uGrp_swap_eq hn]
  obtain ⟨m, rfl⟩ : ∃ m, n = m + 1 := ⟨n - 1, by omega⟩
  have hq := CFSG.LieType.Universal.SpecialLinear.isQuasisimple m K (by omega)
  have hinj : Function.Injective ((iotaS (m + 1)).comp
      (SpecialLinearGroup.toGL : SL(m + 1, K) →* GL (Fin (m + 1)) K)) :=
    iotaS_injective.comp (fun x y h => Subtype.ext (congrArg Units.val h))
  have hqr : IsQuasisimple ((iotaS (m + 1)).comp
      (SpecialLinearGroup.toGL : SL(m + 1, K) →* GL (Fin (m + 1)) K)).range :=
    LocalCores.isQuasisimple_of_mulEquiv (MonoidHom.ofInjective hinj) hq
  exact (CompData.of_isQuasisimple hqr).map (resGL_injective (phiS_injective h2 hs) (m + 1))

end CFSG.ComponentClassification.Burgoyne.O
