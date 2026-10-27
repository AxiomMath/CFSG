module

public import CFSG.ClassicalInvolution.Asc77.AscCX4L4

public section

namespace CFSG.ClassicalInvolution.Asc77.C25G

open CFSG.ClassicalInvolution.Generic

section Abstract

variable {H Y : Type*} [Group H] [Group Y]

theorem exists_twinCent6_of_std (ψ : H →* Y) (hker : ψ.ker ≤ Subgroup.center H)
    {R0 R0' : Subgroup H} {x0 τ0 s0 : H} (g : H) (hτ2 : τ0 * τ0 = 1) (hτx : τ0 * x0 = x0 * τ0)
    (hτR : conjSub τ0 R0 = R0) (hτR' : conjSub τ0 R0' = R0')
    (hs : s0 * x0 * s0⁻¹ = τ0) (hne : τ0 * x0⁻¹ ∉ Subgroup.center H) :
    ∃ τ y : Y, τ ≠ ψ (g * x0 * g⁻¹) ∧ τ * ψ (g * x0 * g⁻¹) = ψ (g * x0 * g⁻¹) * τ ∧
      τ * τ = 1 ∧ y * ψ (g * x0 * g⁻¹) * y⁻¹ = τ ∧
      conjSub τ ((conjSub g R0).map ψ) = (conjSub g R0).map ψ ∧
      conjSub τ ((conjSub g R0').map ψ) = (conjSub g R0').map ψ := by
  refine ⟨ψ (g * τ0 * g⁻¹), ψ (g * s0 * g⁻¹), ?_, ?_, ?_, ?_, ?_, ?_⟩
  · intro h
    apply hne
    have h1 : g * (τ0 * x0⁻¹) * g⁻¹ ∈ ψ.ker := by
      rw [MonoidHom.mem_ker]
      have : g * (τ0 * x0⁻¹) * g⁻¹ = (g * τ0 * g⁻¹) * (g * x0 * g⁻¹)⁻¹ := by group
      rw [this, map_mul, map_inv, h, mul_inv_cancel]
    have h2 := hker h1
    rw [Subgroup.mem_center_iff] at h2 ⊢
    intro w
    have h3 := h2 (g * w * g⁻¹)
    calc w * (τ0 * x0⁻¹) = g⁻¹ * ((g * w * g⁻¹) * (g * (τ0 * x0⁻¹) * g⁻¹)) * g := by group
      _ = g⁻¹ * ((g * (τ0 * x0⁻¹) * g⁻¹) * (g * w * g⁻¹)) * g := by rw [h3]
      _ = (τ0 * x0⁻¹) * w := by group
  · rw [← map_mul, ← map_mul]
    congr 1
    calc g * τ0 * g⁻¹ * (g * x0 * g⁻¹) = g * (τ0 * x0) * g⁻¹ := by group
      _ = g * (x0 * τ0) * g⁻¹ := by rw [hτx]
      _ = g * x0 * g⁻¹ * (g * τ0 * g⁻¹) := by group
  · rw [← map_mul]
    have : g * τ0 * g⁻¹ * (g * τ0 * g⁻¹) = 1 := by
      calc g * τ0 * g⁻¹ * (g * τ0 * g⁻¹) = g * (τ0 * τ0) * g⁻¹ := by group
        _ = 1 := by rw [hτ2]; group
    rw [this, map_one]
  · rw [← map_inv, ← map_mul, ← map_mul]
    congr 1
    calc g * s0 * g⁻¹ * (g * x0 * g⁻¹) * (g * s0 * g⁻¹)⁻¹ = g * (s0 * x0 * s0⁻¹) * g⁻¹ := by group
      _ = g * τ0 * g⁻¹ := by rw [hs]
  · rw [conjSub_map ψ (g * τ0 * g⁻¹) (conjSub g R0), ← conjSub_mul]
    have : g * τ0 * g⁻¹ * g = g * τ0 := by group
    rw [this, conjSub_mul, hτR]
  · rw [conjSub_map ψ (g * τ0 * g⁻¹) (conjSub g R0'), ← conjSub_mul]
    have : g * τ0 * g⁻¹ * g = g * τ0 := by group
    rw [this, conjSub_mul, hτR']

end Abstract

namespace L4

open Matrix CFSG.ClassicalInvolution.WeakCT CFSG.ClassicalInvolution.Models
  CFSG.ClassicalInvolution.ModelFacts.Orth15.OuterL4
  CFSG.ClassicalInvolution.ModelFacts.Orth15.InnerL4
open scoped MatrixGroups

variable {F : Type} [Field F]

@[expose] def tau0 : SL(4, F) :=
  ⟨Matrix.diagonal ![-1, 1, -1, 1], by simp [Matrix.det_diagonal, Fin.prod_univ_four]⟩

theorem coe_tau0 : ((tau0 : SL(4, F)) : Matrix (Fin 4) (Fin 4) F) =
    !![-1, 0, 0, 0; 0, 1, 0, 0; 0, 0, -1, 0; 0, 0, 0, 1] := by
  ext i j
  fin_cases i <;> fin_cases j <;> simp [tau0]

theorem tau0_mul_self : (tau0 : SL(4, F)) * tau0 = 1 := by
  apply Subtype.ext
  rw [Matrix.SpecialLinearGroup.coe_mul, coe_tau0, Matrix.SpecialLinearGroup.coe_one]
  ext i j
  fin_cases i <;> fin_cases j <;> simp [Matrix.mul_apply, Fin.sum_univ_four]

theorem tau0_inv : (tau0 : SL(4, F))⁻¹ = tau0 := inv_eq_of_mul_eq_one_right tau0_mul_self

theorem tau0_mul_x0 : (tau0 : SL(4, F)) * x0 F = x0 F * tau0 := by
  apply Subtype.ext
  rw [Matrix.SpecialLinearGroup.coe_mul, Matrix.SpecialLinearGroup.coe_mul, coe_tau0, coe_x0]
  ext i j
  fin_cases i <;> fin_cases j <;> simp [Matrix.mul_apply, Fin.sum_univ_four]

@[expose] def flipOff (M : SL(2, F)) : SL(2, F) :=
  ⟨!![(M : Matrix (Fin 2) (Fin 2) F) 0 0, -(M : Matrix (Fin 2) (Fin 2) F) 0 1;
    -(M : Matrix (Fin 2) (Fin 2) F) 1 0, (M : Matrix (Fin 2) (Fin 2) F) 1 1], by
    have h := M.2
    rw [Matrix.det_fin_two] at h
    rw [Matrix.det_fin_two]
    simp
    linear_combination h⟩

theorem coe_flipOff (M : SL(2, F)) : ((flipOff M : SL(2, F)) : Matrix (Fin 2) (Fin 2) F) =
    !![(M : Matrix (Fin 2) (Fin 2) F) 0 0, -(M : Matrix (Fin 2) (Fin 2) F) 0 1;
      -(M : Matrix (Fin 2) (Fin 2) F) 1 0, (M : Matrix (Fin 2) (Fin 2) F) 1 1] := rfl

theorem tau0_conj_block0 (M : SL(2, F)) :
    (tau0 : SL(4, F)) * blockSL F 4 2 0 (by norm_num) M * tau0⁻¹ =
      blockSL F 4 2 0 (by norm_num) (flipOff M) := by
  rw [tau0_inv]
  apply Subtype.ext
  simp only [Matrix.SpecialLinearGroup.coe_mul, coe_blockSL, coe_tau0, coe_flipOff,
    blockMat_four_zero]
  ext i j
  fin_cases i <;> fin_cases j <;> simp [Matrix.mul_apply, Fin.sum_univ_four]

theorem tau0_conj_block2 (M : SL(2, F)) :
    (tau0 : SL(4, F)) * blockSL F 4 2 2 (by norm_num) M * tau0⁻¹ =
      blockSL F 4 2 2 (by norm_num) (flipOff M) := by
  rw [tau0_inv]
  apply Subtype.ext
  simp only [Matrix.SpecialLinearGroup.coe_mul, coe_blockSL, coe_tau0, coe_flipOff,
    blockMat_four_two]
  ext i j
  fin_cases i <;> fin_cases j <;> simp [Matrix.mul_apply, Fin.sum_univ_four]

theorem tau0_conj_R0 : conjSub (tau0 : SL(4, F)) (R0 F) = R0 F := by
  apply conjSub_eq_of_mem_normalizer
  rw [Subgroup.mem_normalizer_iff]
  intro x
  constructor
  · intro hx
    obtain ⟨M, rfl⟩ := MonoidHom.mem_range.mp
      (show x ∈ (blockSL F 4 2 0 (by norm_num)).range from hx)
    exact MonoidHom.mem_range.mpr ⟨flipOff M, (tau0_conj_block0 M).symm⟩
  · intro hx
    obtain ⟨M', hM'⟩ := MonoidHom.mem_range.mp
      (show tau0 * x * tau0⁻¹ ∈ (blockSL F 4 2 0 (by norm_num)).range from hx)
    refine MonoidHom.mem_range.mpr ⟨flipOff M', ?_⟩
    have h1 : (tau0 : SL(4, F)) * (tau0 * x * tau0⁻¹) * tau0⁻¹ = x := by
      calc _ = (tau0 * tau0) * x * (tau0 * tau0)⁻¹ := by group
        _ = x := by rw [tau0_mul_self]; group
    rw [← tau0_conj_block0 M', hM']
    exact h1

theorem tau0_conj_R0' : conjSub (tau0 : SL(4, F)) (R0' F) = R0' F := by
  apply conjSub_eq_of_mem_normalizer
  rw [Subgroup.mem_normalizer_iff]
  intro x
  constructor
  · intro hx
    obtain ⟨M, rfl⟩ := MonoidHom.mem_range.mp
      (show x ∈ (blockSL F 4 2 2 (by norm_num)).range from hx)
    exact MonoidHom.mem_range.mpr ⟨flipOff M, (tau0_conj_block2 M).symm⟩
  · intro hx
    obtain ⟨M', hM'⟩ := MonoidHom.mem_range.mp
      (show tau0 * x * tau0⁻¹ ∈ (blockSL F 4 2 2 (by norm_num)).range from hx)
    refine MonoidHom.mem_range.mpr ⟨flipOff M', ?_⟩
    have h1 : (tau0 : SL(4, F)) * (tau0 * x * tau0⁻¹) * tau0⁻¹ = x := by
      calc _ = (tau0 * tau0) * x * (tau0 * tau0)⁻¹ := by group
        _ = x := by rw [tau0_mul_self]; group
    rw [← tau0_conj_block2 M', hM']
    exact h1

theorem blockMat_four_one' (A : Matrix (Fin 2) (Fin 2) F) :
    CFSG.ClassicalInvolution.Phan.blockMat 4 1 A =
      !![1, 0, 0, 0; 0, A 0 0, A 0 1, 0; 0, A 1 0, A 1 1, 0; 0, 0, 0, 1] := by
  ext a b
  rw [CFSG.ClassicalInvolution.Phan.blockMat_apply]
  fin_cases a <;> fin_cases b <;> simp

@[expose] noncomputable def s0 : SL(4, F) := blockSL F 4 2 1 (by norm_num) r0

theorem s0_mul_x0 : (s0 : SL(4, F)) * x0 F = tau0 * s0 := by
  apply Subtype.ext
  rw [Matrix.SpecialLinearGroup.coe_mul, Matrix.SpecialLinearGroup.coe_mul, s0, coe_blockSL, coe_r0,
    blockMat_four_one', coe_x0, coe_tau0]
  ext i j
  fin_cases i <;> fin_cases j <;> simp [Matrix.mul_apply, Fin.sum_univ_four]

theorem s0_conj_x0 : (s0 : SL(4, F)) * x0 F * s0⁻¹ = tau0 := by
  calc s0 * x0 F * s0⁻¹ = tau0 * s0 * s0⁻¹ := by rw [s0_mul_x0]
    _ = tau0 := by group

theorem tau0_x0_not_central (h2 : (2 : F) ≠ 0) :
    (tau0 : SL(4, F)) * (x0 F)⁻¹ ∉ Subgroup.center SL(4, F) := by
  intro hc
  rw [inv_eq_of_mul_eq_one_right x0_mul_self] at hc
  have h := Subgroup.mem_center_iff.mp hc (blockSL F 4 2 0 (by norm_num) r0)
  have e := congrArg (fun g : SL(4, F) => ((g : Matrix (Fin 4) (Fin 4) F)) 0 1) h
  simp only [Matrix.SpecialLinearGroup.coe_mul, coe_blockSL, coe_r0, blockMat_four_zero, coe_tau0,
    coe_x0, Matrix.mul_apply, Fin.sum_univ_four] at e
  simp at e
  apply h2
  first
    | linear_combination e
    | linear_combination (-1 : F) * e

theorem twinCent6_psl4 [Finite F] (h2 : (2 : F) ≠ 0) {Y : Type} [Group Y] (ψ : SL(4, F) →* Y)
    (hker : ψ.ker ≤ Subgroup.center SL(4, F)) {R R' : Subgroup SL(4, F)}
    (hR : R ∈ longRootSet (K := F) (show 2 ≤ 4 by norm_num))
    (hR' : R' ∈ longRootSet (K := F) (show 2 ≤ 4 by norm_num))
    (hne : R.map ψ ≠ R'.map ψ) {z' : Y} (hz : IsUniqueInvolution (R.map ψ) z')
    (hz' : IsUniqueInvolution (R'.map ψ) z') :
    ∃ τ y : Y, τ ≠ z' ∧ τ * z' = z' * τ ∧ τ * τ = 1 ∧ y * z' * y⁻¹ = τ ∧
      conjSub τ (R.map ψ) = R.map ψ ∧ conjSub τ (R'.map ψ) = R'.map ψ := by
  obtain ⟨i, hi⟩ := hR
  obtain ⟨i', hi'⟩ := hR'
  have hRR : R ≠ R' := fun h => hne (by rw [h])
  obtain ⟨hiR, hi2, hi1, hψi⟩ := CX.CX4.L4.twin_data h2 ψ hker hi hz
  obtain ⟨hi'R, hi'2, hi'1, hψi'⟩ := CX.CX4.L4.twin_data h2 ψ hker hi' hz'
  have hc : i' * i⁻¹ ∈ Subgroup.center SL(4, F) := hker (by
    rw [MonoidHom.mem_ker, map_mul, map_inv, hψi, hψi', mul_inv_cancel])
  obtain ⟨g, hRg, hR'g, hig⟩ := twin_std h2 ⟨i, hi⟩ ⟨i', hi'⟩ hRR hiR hi2 hi1 hi'R hi'2 hi'1 hc
  have hix : i = g * x0 F * g⁻¹ := hig
  have hz'eq : z' = ψ (g * x0 F * g⁻¹) := by rw [← hψi, hix]
  obtain ⟨τ, y, h1, h2', h3, h4, h5, h6⟩ := exists_twinCent6_of_std ψ hker (R0 := R0 F)
    (R0' := R0' F) (x0 := x0 F) (τ0 := tau0) (s0 := s0) g tau0_mul_self tau0_mul_x0
    tau0_conj_R0 tau0_conj_R0' s0_conj_x0 (tau0_x0_not_central h2)
  refine ⟨τ, y, ?_, ?_, h3, ?_, ?_, ?_⟩
  · rw [hz'eq]
    exact h1
  · rw [hz'eq]
    exact h2'
  · rw [hz'eq]
    exact h4
  · rw [hRg]
    exact h5
  · rw [hR'g]
    exact h6

end L4

end CFSG.ClassicalInvolution.Asc77.C25G
