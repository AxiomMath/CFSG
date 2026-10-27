module

public import CFSG.ClassicalInvolution.Q3.Q3MFOU4Sp
public import CFSG.ClassicalInvolution.Q3.Q3MFO4Fix

public section

set_option linter.unusedSectionVars false

namespace CFSG.ClassicalInvolution.Q3.Q3MFOU4

open Matrix CFSG.ClassicalInvolution.Q3.Q3PP CFSG.ClassicalInvolution.Models
  CFSG.LieType.Universal.Unitary CFSG.Assembly.LowTwoRank CFSG.ClassicalInvolution.Phan
  CFSG.ClassicalInvolution.Q3.Q3NM CFSG.ClassicalInvolution.Balance
  CFSG.ClassicalInvolution.Q3.Q3MFO4
open scoped MatrixGroups

section Scalars

theorem mem_center_of_scalar {z : Su F9 3 1 4} {c : F9}
    (hz : suMat z = c • (1 : Matrix (Fin 4) (Fin 4) F9)) :
    z ∈ Subgroup.center (Su F9 3 1 4) := by
  rw [Subgroup.mem_center_iff]
  intro g
  apply suMat_injective
  rw [suMat_mul, suMat_mul, hz, Matrix.mul_smul, Matrix.smul_mul, Matrix.mul_one, Matrix.one_mul]

theorem scalar_of_mem_center {z : Su F9 3 1 4} (hz : z ∈ Subgroup.center (Su F9 3 1 4)) :
    ∃ u : F9, u ≠ 0 ∧ suMat z = u • (1 : Matrix (Fin 4) (Fin 4) F9) := by
  obtain ⟨u, hu⟩ := exists_scalar_of_mem_center isUnitaryInvolution_σ9 (by norm_num : 3 ≤ 4) hz
  refine ⟨u, u.ne_zero, ?_⟩
  show ((z : GL (Fin 4) F9) : Matrix (Fin 4) (Fin 4) F9) = _
  rw [hu, Matrix.scalar_apply, ← Matrix.smul_one_eq_diagonal]

theorem suMat_pow (x : Su F9 3 1 4) (k : ℕ) : suMat (x ^ k) = suMat x ^ k := by
  induction k with
  | zero => simp
  | succ k ih => rw [pow_succ, suMat_mul, ih, pow_succ]

end Scalars

section Odd

variable (D : GraphData)

theorem G_ne_zero : D.G ≠ 0 := by
  intro h
  have h1 := congrFun (congrFun h 0) 1
  apply D.m_ne_zero
  simpa [GraphData.G, Gmat] using h1

theorem pow_two_mul_odd {c : F9} (h4 : c ^ 4 = 1) {k : ℕ} (hk : Odd k) : c ^ (2 * k) = c ^ 2 := by
  obtain ⟨j, rfl⟩ := hk
  have : 2 * (2 * j + 1) = 4 * j + 2 := by ring
  rw [this, pow_add, pow_mul, h4, one_pow, one_mul]

theorem comm_pow {X : Matrix (Fin 4) (Fin 4) F9} {c : F9}
    (h : D.G * X.map σ9 = c • (X * D.G)) :
    ∀ j : ℕ, D.G * (X ^ j).map σ9 = c ^ j • (X ^ j * D.G)
  | 0 => by simp
  | j + 1 => by
    have ih := comm_pow h j
    calc D.G * (X ^ (j + 1)).map σ9 = (D.G * (X ^ j).map σ9) * X.map σ9 := by
          rw [pow_succ, Matrix.map_mul, Matrix.mul_assoc]
      _ = c ^ j • (X ^ j * (D.G * X.map σ9)) := by
          rw [ih]
          simp only [Matrix.smul_mul, Matrix.mul_assoc]
      _ = c ^ j • (X ^ j * (c • (X * D.G))) := by rw [h]
      _ = c ^ (j + 1) • (X ^ (j + 1) * D.G) := by
          rw [pow_succ, pow_succ]
          simp only [Matrix.mul_smul, smul_smul, Matrix.mul_assoc]

theorem exists_comm_of_odd (α : Su F9 3 1 4 →* Su F9 3 1 4)
    (hαG : ∀ x, suMat (α x) * D.G = D.G * (suMat x).map σ9) (x : Su F9 3 1 4)
    (hxα : (QuotientGroup.mk (α x) : Su F9 3 1 4 ⧸ Subgroup.center (Su F9 3 1 4)) =
      QuotientGroup.mk x)
    (hodd : Odd (orderOf (QuotientGroup.mk x : Su F9 3 1 4 ⧸ Subgroup.center (Su F9 3 1 4)))) :
    ∃ x' : Su F9 3 1 4, (QuotientGroup.mk x' : Su F9 3 1 4 ⧸ Subgroup.center (Su F9 3 1 4)) =
      QuotientGroup.mk x ∧ D.G * (suMat x').map σ9 = suMat x' * D.G := by
  classical
  set X := suMat x with hX
  have hz : (α x)⁻¹ * x ∈ Subgroup.center (Su F9 3 1 4) := QuotientGroup.eq.mp hxα
  obtain ⟨u, hu0, hu⟩ := scalar_of_mem_center hz
  have hαx : suMat (α x) = u⁻¹ • X := by
    have h1 : suMat (α x) * (u • (1 : Matrix (Fin 4) (Fin 4) F9)) = X := by
      rw [← hu, ← suMat_mul, mul_inv_cancel_left]
    rw [Matrix.mul_smul, Matrix.mul_one] at h1
    rw [← h1, smul_smul, inv_mul_cancel₀ hu0, one_smul]
  set c₀ : F9 := u⁻¹ with hc₀
  have hcomm0 : D.G * X.map σ9 = c₀ • (X * D.G) := by
    rw [← hαG x, hαx, Matrix.smul_mul]
  have hc4 : c₀ ^ 4 = 1 := by
    have h1 := det_suMat (α x)
    rw [hαx, Matrix.det_smul, det_suMat x] at h1
    simpa using h1
  set k := orderOf (QuotientGroup.mk x : Su F9 3 1 4 ⧸ Subgroup.center (Su F9 3 1 4)) with hk
  have hk1 : (QuotientGroup.mk x : Su F9 3 1 4 ⧸ Subgroup.center (Su F9 3 1 4)) ^ k = 1 :=
    pow_orderOf_eq_one _
  have hxk : x ^ k ∈ Subgroup.center (Su F9 3 1 4) := by
    rw [← QuotientGroup.eq_one_iff, QuotientGroup.mk_pow]
    exact hk1
  obtain ⟨s, hs0, hs⟩ := scalar_of_mem_center hxk
  rw [suMat_pow] at hs
  have hs4 : s ^ 4 = 1 := by
    have h1 := det_suMat (x ^ k)
    rw [suMat_pow, hs, Matrix.det_smul, Matrix.det_one] at h1
    simpa using h1
  have hsn : σ9 s * s = 1 := by
    have h1 := (mem_SUid.mp (x ^ k).2).2
    have h2 : conjTr σ9 (suMat (x ^ k)) * suMat (x ^ k) = 1 := h1
    rw [suMat_pow, hs] at h2
    have e1 : (s • (1 : Matrix (Fin 4) (Fin 4) F9)).map σ9 =
        σ9 s • (1 : Matrix (Fin 4) (Fin 4) F9) := by
      rw [Matrix.map_smul' _ _ _ (map_mul σ9), Matrix.map_one _ (map_zero σ9) (map_one σ9)]
    rw [conjTr, e1, Matrix.transpose_smul, Matrix.transpose_one, Matrix.smul_mul,
      Matrix.one_mul, smul_smul] at h2
    have h3 := congrFun (congrFun h2 0) 0
    simpa [Matrix.smul_apply] using h3
  have hpow := comm_pow D hcomm0 k
  rw [hs] at hpow
  have hsG : σ9 s = c₀ ^ k * s := by
    have h1 : (σ9 s - c₀ ^ k * s) • D.G = 0 := by
      rw [sub_smul, sub_eq_zero]
      have h2 : D.G * ((s • (1 : Matrix (Fin 4) (Fin 4) F9)).map σ9) =
          c₀ ^ k • ((s • (1 : Matrix (Fin 4) (Fin 4) F9)) * D.G) := hpow
      simpa [Matrix.map_smul', Matrix.mul_smul, Matrix.smul_mul, smul_smul] using h2
    exact sub_eq_zero.mp ((smul_eq_zero.mp h1).resolve_right (G_ne_zero D))
  have hck : c₀ ^ k * (s * s) = 1 := by
    rw [← hsn, hsG]
    ring
  have hck2 : (c₀ ^ k) ^ 2 = 1 := by
    have : (c₀ ^ k) ^ 2 * s ^ 4 = 1 := by
      calc (c₀ ^ k) ^ 2 * s ^ 4 = (c₀ ^ k * (s * s)) ^ 2 := by ring
        _ = 1 := by rw [hck, one_pow]
    rwa [hs4, mul_one] at this
  have hc2 : c₀ ^ 2 = 1 := by
    rw [← pow_two_mul_odd hc4 hodd, pow_mul', hck2]
  rcases mul_self_eq_one_iff.mp (by rw [← pow_two]; exact hc2 : c₀ * c₀ = 1) with h1 | h1
  ·
    refine ⟨x, rfl, ?_⟩
    rw [hcomm0, h1, one_smul]
  ·
    obtain ⟨ι, hι, hιb⟩ := exists_iota
    have hι4 : ι ^ 4 = 1 := by
      calc ι ^ 4 = (ι * ι) ^ 2 := by ring
        _ = 1 := by rw [hι]; norm_num
    have hdet' : (ι • X).det = 1 := by
      rw [Matrix.det_smul, det_suMat x]
      simpa using hι4
    have hmap : (ι • X).map σ9 = σ9 ι • X.map σ9 := Matrix.map_smul' _ _ _ (map_mul σ9)
    have hu' : conjTr σ9 (ι • X) * (ι • X) = 1 := by
      have h2 : conjTr σ9 X * X = 1 := (mem_SUid.mp x.2).2
      calc conjTr σ9 (ι • X) * (ι • X) = (σ9 ι * ι) • (conjTr σ9 X * X) := by
            rw [conjTr, hmap, Matrix.transpose_smul, Matrix.smul_mul, Matrix.mul_smul, smul_smul]
            rfl
        _ = 1 := by
            rw [h2, hιb, show -ι * ι = -(ι * ι) by ring, hι]
            simp
    refine ⟨CFSG.ClassicalInvolution.Models.mkSU F9 3 1 (ι • X) hdet' hu', ?_, ?_⟩
    · symm
      apply QuotientGroup.eq.mpr
      refine mem_center_of_scalar (c := ι) ?_
      rw [suMat_mul, CFSG.ClassicalInvolution.Models.suMat_mkSU, Matrix.mul_smul,
        suMat_inv_mul_suMat]
    · rw [CFSG.ClassicalInvolution.Models.suMat_mkSU, hmap, Matrix.mul_smul, hcomm0, h1,
        hιb, smul_smul, Matrix.smul_mul]
      congr 1
      ring

end Odd

section Final

variable (D : GraphData)

theorem G_mul_inv : D.G * Gmat (-(D.m)⁻¹) (-(D.n)⁻¹) = 1 := by
  have hm := D.m_ne_zero
  have hn := D.n_ne_zero
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [GraphData.G, Gmat, Matrix.mul_apply, Fin.sum_univ_four, hm, hn]

theorem eq_of_mul_G {A B : Matrix (Fin 4) (Fin 4) F9} (h : A * D.G = B * D.G) : A = B := by
  have h1 := congrArg (fun X => X * Gmat (-(D.m)⁻¹) (-(D.n)⁻¹)) h
  simp only [Matrix.mul_assoc, G_mul_inv D, Matrix.mul_one] at h1
  exact h1

theorem oddCoreIn_fixed_graph_su4 (hq : CFSG.Open.IsQuasisimple (StatedSp 2 F3))
    (hZ : IsPGroup 2 (Subgroup.center (StatedSp 2 F3))) (α : Su F9 3 1 4 →* Su F9 3 1 4)
    (hαG : ∀ x, suMat (α x) * D.G = D.G * (suMat x).map σ9)
    (ρ : MulAut (Su F9 3 1 4 ⧸ Subgroup.center (Su F9 3 1 4)))
    (hρ : ∀ x, ρ (QuotientGroup.mk x) = QuotientGroup.mk (α x)) :
    oddCoreIn (fixedSubgroup ρ) = ⊥ := by
  classical
  obtain ⟨θ, hθ⟩ : ∃ θ : Su F9 3 1 4 →* Su F9 3 1 4 ⧸ Subgroup.center (Su F9 3 1 4),
      θ = QuotientGroup.mk' _ := ⟨_, rfl⟩
  have hker : (θ.comp D.psi).ker ≤ Subgroup.center (StatedSp 2 F3) := by
    intro x hx
    apply D.psi_ker
    have h1 : θ (D.psi x) = 1 := hx
    rw [hθ] at h1
    exact (QuotientGroup.eq_one_iff _).mp h1
  have hN : oddCoreIn (θ.comp D.psi).range = ⊥ :=
    oddCoreIn_range_eq_bot_of_isQuasisimple _ hq hZ hker
  refine oddCoreIn_eq_bot_of_odd_mem_sub (N := (θ.comp D.psi).range) ?_ ?_ hN
  · rintro _ ⟨x, rfl⟩
    show ρ (θ (D.psi x)) = θ (D.psi x)
    have h1 : ρ (θ (D.psi x)) = θ (α (D.psi x)) := by rw [hθ]; exact hρ _
    rw [h1]
    congr 1
    have h2 : α (D.psi x) = D.psi x := by
      apply suMat_injective
      apply eq_of_mul_G D
      rw [hαG, D.psi_comm]
    rw [h2]
  · intro y hy hodd
    obtain ⟨x, rfl⟩ := QuotientGroup.mk_surjective y
    have hxα : (QuotientGroup.mk (α x) : Su F9 3 1 4 ⧸ Subgroup.center (Su F9 3 1 4)) =
        QuotientGroup.mk x := by
      rw [← hρ]
      exact hy
    obtain ⟨x', hx', hcomm⟩ := exists_comm_of_odd D α hαG x hxα hodd
    obtain ⟨z, hz⟩ := D.psi_range x' hcomm
    refine ⟨z, ?_⟩
    show θ (D.psi z) = QuotientGroup.mk x
    rw [hz, hθ]
    exact hx'

end Final

end CFSG.ClassicalInvolution.Q3.Q3MFOU4
