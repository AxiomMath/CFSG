module

public import CFSG.ClassicalInvolution.Asc77.AscC25G2
public import CFSG.ClassicalInvolution.Asc77.AscCX4U5

public section

namespace CFSG.ClassicalInvolution.Asc77.C25G.U4

open Matrix CFSG.ClassicalInvolution.Phan CFSG.ClassicalInvolution.Models
  CFSG.ClassicalInvolution.ModelFacts.UnitaryAut CFSG.LieType.Universal.Unitary
  CFSG.LieType.BorelTits CFSG.ClassicalInvolution.ModelFacts.Orth15.ChainU
  CFSG.ClassicalGroups.Unitary CFSG.ClassicalInvolution.ModelFacts.Orth15.OuterU4
  CFSG.ClassicalInvolution.ModelFacts.Orth15.InnerSu CFSG.ClassicalInvolution.Generic
open scoped MatrixGroups

section Flip

theorem unitary_flip {K : Type} [Field K] (A : Matrix (Fin 2) (Fin 2) K) (σ : K ≃+* K)
    (hA : conjTr σ A * A = 1) :
    conjTr σ !![A 0 0, -A 0 1; -A 1 0, A 1 1] * !![A 0 0, -A 0 1; -A 1 0, A 1 1] = 1 := by
  set D : Matrix (Fin 2) (Fin 2) K := Matrix.diagonal ![-1, 1] with hD
  have hDD : D * D = 1 := by
    ext i j
    fin_cases i <;> fin_cases j <;> simp [hD, Matrix.mul_apply, Matrix.diagonal_apply]
  have hDc : conjTr σ D = D := by
    ext i j
    fin_cases i <;> fin_cases j <;> simp [hD, conjTr]
  have hflip : (!![A 0 0, -A 0 1; -A 1 0, A 1 1] : Matrix (Fin 2) (Fin 2) K) = D * A * D := by
    ext i j
    fin_cases i <;> fin_cases j <;> simp [hD, Matrix.mul_apply, Matrix.diagonal_apply]
  rw [hflip, conjTr_mul, conjTr_mul, hDc]
  calc D * (conjTr σ A * D) * (D * A * D) = D * (conjTr σ A * (D * D) * A) * D := by
        simp only [Matrix.mul_assoc]
    _ = 1 := by rw [hDD, Matrix.mul_one, hA, Matrix.mul_one, hDD]

end Flip

variable {K : Type} [Field K] [Finite K] {p f : ℕ} [Fact p.Prime] [CharP K p]

@[expose] noncomputable def flipOffU (A : Su K p f 2) : Su K p f 2 :=
  mkSU K p f !![suMat A 0 0, -suMat A 0 1; -suMat A 1 0, suMat A 1 1]
    (by
      have h := det_suMat A
      rw [Matrix.det_fin_two] at h
      rw [Matrix.det_fin_two]
      simp
      linear_combination h)
    (unitary_flip (suMat A) _ (by exact A.2.2))

theorem suMat_flipOffU (A : Su K p f 2) :
    suMat (flipOffU A) = !![suMat A 0 0, -suMat A 0 1; -suMat A 1 0, suMat A 1 1] := rfl

@[expose] noncomputable def tau0 : Su K p f 4 :=
  mkSU K p f (Matrix.diagonal ![-1, 1, -1, 1]) (by simp [Matrix.det_diagonal, Fin.prod_univ_four])
    (by
      ext a b
      fin_cases a <;> fin_cases b <;> simp [conjTr, Matrix.mul_apply, Matrix.diagonal_apply])

theorem suMat_tau0 : suMat (tau0 : Su K p f 4) =
    !![-1, 0, 0, 0; 0, 1, 0, 0; 0, 0, -1, 0; 0, 0, 0, 1] := by
  ext i j
  fin_cases i <;> fin_cases j <;> simp [tau0, suMat_mkSU]

theorem tau0_mul_self : (tau0 : Su K p f 4) * tau0 = 1 := by
  apply suMat_injective
  rw [suMat_mul, suMat_tau0, suMat_one]
  ext i j
  fin_cases i <;> fin_cases j <;> simp [Matrix.mul_apply, Fin.sum_univ_four]

theorem tau0_inv : (tau0 : Su K p f 4)⁻¹ = tau0 := inv_eq_of_mul_eq_one_right tau0_mul_self

theorem tau0_mul_x0 : (tau0 : Su K p f 4) * x0 K p f = x0 K p f * tau0 := by
  apply suMat_injective
  rw [suMat_mul, suMat_mul, suMat_tau0, suMat_x0]
  ext i j
  fin_cases i <;> fin_cases j <;> simp [Matrix.mul_apply, Fin.sum_univ_four]

theorem tau0_conj_block0 (A : Su K p f 2) :
    (tau0 : Su K p f 4) * blockEmb K p f 4 2 0 (by norm_num) A * tau0⁻¹ =
      blockEmb K p f 4 2 0 (by norm_num) (flipOffU A) := by
  rw [tau0_inv]
  apply suMat_injective
  rw [suMat_mul, suMat_mul, suMat_tau0, suMat_blockEmb_zero, suMat_blockEmb_zero,
    suMat_flipOffU]
  ext i j
  fin_cases i <;> fin_cases j <;> simp [Matrix.mul_apply, Fin.sum_univ_four]

theorem tau0_conj_block2 (A : Su K p f 2) :
    (tau0 : Su K p f 4) * blockEmb K p f 4 2 2 (by norm_num) A * tau0⁻¹ =
      blockEmb K p f 4 2 2 (by norm_num) (flipOffU A) := by
  rw [tau0_inv]
  apply suMat_injective
  rw [suMat_mul, suMat_mul, suMat_tau0, suMat_blockEmb_two, suMat_blockEmb_two,
    suMat_flipOffU]
  ext i j
  fin_cases i <;> fin_cases j <;> simp [Matrix.mul_apply, Fin.sum_univ_four]

theorem tau0_conj_R0 : conjSub (tau0 : Su K p f 4) (R0 K p f) = R0 K p f := by
  apply conjSub_eq_of_mem_normalizer
  rw [Subgroup.mem_normalizer_iff]
  intro x
  constructor
  · intro hx
    obtain ⟨A, rfl⟩ := MonoidHom.mem_range.mp
      (show x ∈ (blockEmb K p f 4 2 0 (by norm_num)).range from hx)
    exact MonoidHom.mem_range.mpr ⟨flipOffU A, (tau0_conj_block0 A).symm⟩
  · intro hx
    obtain ⟨A', hA'⟩ := MonoidHom.mem_range.mp
      (show tau0 * x * tau0⁻¹ ∈ (blockEmb K p f 4 2 0 (by norm_num)).range from hx)
    refine MonoidHom.mem_range.mpr ⟨flipOffU A', ?_⟩
    have h1 : (tau0 : Su K p f 4) * (tau0 * x * tau0⁻¹) * tau0⁻¹ = x := by
      calc _ = (tau0 * tau0) * x * (tau0 * tau0)⁻¹ := by group
        _ = x := by rw [tau0_mul_self]; group
    rw [← tau0_conj_block0 A', hA']
    exact h1

theorem tau0_conj_R0' : conjSub (tau0 : Su K p f 4) (R0' K p f) = R0' K p f := by
  apply conjSub_eq_of_mem_normalizer
  rw [Subgroup.mem_normalizer_iff]
  intro x
  constructor
  · intro hx
    obtain ⟨A, rfl⟩ := MonoidHom.mem_range.mp
      (show x ∈ (blockEmb K p f 4 2 2 (by norm_num)).range from hx)
    exact MonoidHom.mem_range.mpr ⟨flipOffU A, (tau0_conj_block2 A).symm⟩
  · intro hx
    obtain ⟨A', hA'⟩ := MonoidHom.mem_range.mp
      (show tau0 * x * tau0⁻¹ ∈ (blockEmb K p f 4 2 2 (by norm_num)).range from hx)
    refine MonoidHom.mem_range.mpr ⟨flipOffU A', ?_⟩
    have h1 : (tau0 : Su K p f 4) * (tau0 * x * tau0⁻¹) * tau0⁻¹ = x := by
      calc _ = (tau0 * tau0) * x * (tau0 * tau0)⁻¹ := by group
        _ = x := by rw [tau0_mul_self]; group
    rw [← tau0_conj_block2 A', hA']
    exact h1

@[expose] noncomputable def s0 : Su K p f 4 := blockEmb K p f 4 2 1 (by norm_num) (jSU K p f)

theorem s0_mul_x0 : (s0 : Su K p f 4) * x0 K p f = tau0 * s0 := by
  apply suMat_injective
  rw [suMat_mul, suMat_mul, s0, suMat_blockEmb, suMat_jSU, L4.blockMat_four_one', suMat_x0,
    suMat_tau0]
  ext i j
  fin_cases i <;> fin_cases j <;> simp [Matrix.mul_apply, Fin.sum_univ_four]

theorem s0_conj_x0 : (s0 : Su K p f 4) * x0 K p f * s0⁻¹ = tau0 := by
  calc s0 * x0 K p f * s0⁻¹ = tau0 * s0 * s0⁻¹ := by rw [s0_mul_x0]
    _ = tau0 := by group

theorem tau0_x0_not_central (h2 : (2 : K) ≠ 0) :
    (tau0 : Su K p f 4) * (x0 K p f)⁻¹ ∉ Subgroup.center (Su K p f 4) := by
  intro hc
  rw [inv_eq_of_mul_eq_one_right (x0_mul_self (K := K) (p := p) (f := f))] at hc
  have h := Subgroup.mem_center_iff.mp hc (blockEmb K p f 4 2 0 (by norm_num) (jSU K p f))
  have e := congrArg (fun g : Su K p f 4 => suMat g 0 1) h
  simp only [suMat_mul, suMat_blockEmb_zero, suMat_jSU, suMat_tau0, suMat_x0, Matrix.mul_apply,
    Fin.sum_univ_four] at e
  simp at e
  apply h2
  first
    | linear_combination e
    | linear_combination (-1 : K) * e

theorem twinCent6_psu4 (hK : Nat.card K = (p ^ f) ^ 2) (hp : p ≠ 2) {Y : Type} [Group Y]
    (θ : Su K p f 4 →* Y) (hker : θ.ker ≤ Subgroup.center (Su K p f 4))
    {R R' : Subgroup (Su K p f 4)}
    (hR : R ∈ longRootSetU (K := K) (p := p) (f := f) (show 2 ≤ 4 by norm_num))
    (hR' : R' ∈ longRootSetU (K := K) (p := p) (f := f) (show 2 ≤ 4 by norm_num))
    (hne : R.map θ ≠ R'.map θ) {z' : Y} (hz : IsUniqueInvolution (R.map θ) z')
    (hz' : IsUniqueInvolution (R'.map θ) z') :
    ∃ τ y : Y, τ ≠ z' ∧ τ * z' = z' * τ ∧ τ * τ = 1 ∧ y * z' * y⁻¹ = τ ∧
      conjSub τ (R.map θ) = R.map θ ∧ conjSub τ (R'.map θ) = R'.map θ := by
  have h2 : (2 : K) ≠ 0 := two_ne_zero_of_charP_ne_two (K := K) hp
  obtain ⟨i, hi⟩ := hR
  obtain ⟨i', hi'⟩ := hR'
  have hRR : R ≠ R' := fun h => hne (by rw [h])
  obtain ⟨hiR, hi2, hi1, hθi⟩ := CX.CX4.U4.twin_data hK hp θ hker hi hz
  obtain ⟨hi'R, hi'2, hi'1, hθi'⟩ := CX.CX4.U4.twin_data hK hp θ hker hi' hz'
  have hc : i' * i⁻¹ ∈ Subgroup.center (Su K p f 4) := hker (by
    rw [MonoidHom.mem_ker, map_mul, map_inv, hθi, hθi', mul_inv_cancel])
  obtain ⟨g, hRg, hR'g, hig⟩ :=
    twin_std_u hK hp ⟨i, hi⟩ ⟨i', hi'⟩ hRR hiR hi2 hi1 hi'R hi'2 hi'1 hc
  have hix : i = g * x0 K p f * g⁻¹ := hig
  have hz'eq : z' = θ (g * x0 K p f * g⁻¹) := by rw [← hθi, hix]
  obtain ⟨τ, y, h1, h2', h3, h4, h5, h6⟩ := exists_twinCent6_of_std θ hker (R0 := R0 K p f)
    (R0' := R0' K p f) (x0 := x0 K p f) (τ0 := tau0) (s0 := s0) g tau0_mul_self tau0_mul_x0
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

end CFSG.ClassicalInvolution.Asc77.C25G.U4
