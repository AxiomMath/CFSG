module

public import CFSG.LocalAnalysis.ComponentClassification.CatFactsSp4TypeOne
public import CFSG.ClassicalInvolution.SL2Facts

public noncomputable section

namespace CFSG.ClassicalInvolution.Q3.TA3.Sp4

open Matrix CFSG.Assembly.LowTwoRank CFSG.LocalAnalysis.ComponentInitial
open CFSG.ComponentClassification.CatFactsSp4 SymplecticHigher SymplecticFlag Subgroup

variable {K : Type} [Field K]

theorem kron_upper (c : K) :
    kron (!![1, c; 0, 1] : Matrix (Fin 2) (Fin 2) K) 1 = fromBlocks 1 (c • 1) 0 1 := by
  simp [kron]

theorem kron_lower (d : K) :
    kron (!![1, 0; d, 1] : Matrix (Fin 2) (Fin 2) K) 1 = fromBlocks 1 0 (d • 1) 1 := by
  simp [kron]

theorem kron_one_left (h : Matrix (Fin 2) (Fin 2) K) : kron 1 h = fromBlocks h 0 0 h := by
  simp [kron]

theorem eq_kron_one_of_commute {A : Matrix (Fin 2 ⊕ Fin 2) (Fin 2 ⊕ Fin 2) K} {c d : K}
    (hc : c ≠ 0) (hd : d ≠ 0)
    (h1 : A * kron !![1, c; 0, 1] 1 = kron !![1, c; 0, 1] 1 * A)
    (h2 : A * kron !![1, 0; d, 1] 1 = kron !![1, 0; d, 1] 1 * A) :
    A = kron 1 A.toBlocks₁₁ := by
  rw [kron_upper] at h1
  rw [kron_lower] at h2
  rw [← fromBlocks_toBlocks A, fromBlocks_multiply, fromBlocks_multiply] at h1 h2
  obtain ⟨e11, e12, -, -⟩ := fromBlocks_inj.mp h1
  obtain ⟨f11, -, -, -⟩ := fromBlocks_inj.mp h2
  simp only [Matrix.mul_one, Matrix.mul_zero, add_zero, Matrix.one_mul, Matrix.zero_mul,
    Matrix.mul_smul, Matrix.smul_mul] at e11 e12 f11
  have h21 : A.toBlocks₂₁ = 0 := (smul_eq_zero.mp (left_eq_add.mp e11)).resolve_left hc
  have h12 : A.toBlocks₁₂ = 0 := (smul_eq_zero.mp (add_eq_left.mp f11)).resolve_left hd
  have h22 : A.toBlocks₁₁ = A.toBlocks₂₂ := by
    rw [add_comm] at e12
    exact smul_right_injective _ hc (add_left_cancel e12)
  rw [kron_one_left]
  conv_lhs => rw [← fromBlocks_toBlocks A]
  rw [h21, h12, ← h22]

theorem mul_eq_or_eq_neg_of_commute {A B : StatedSp 2 K}
    (h : proj 2 K A * proj 2 K B = proj 2 K B * proj 2 K A) :
    ((A : GL (Fin 2 ⊕ Fin 2) K) : Matrix (Fin 2 ⊕ Fin 2) (Fin 2 ⊕ Fin 2) K) *
        ((B : GL (Fin 2 ⊕ Fin 2) K) : Matrix (Fin 2 ⊕ Fin 2) (Fin 2 ⊕ Fin 2) K) =
      ((B : GL (Fin 2 ⊕ Fin 2) K) : Matrix (Fin 2 ⊕ Fin 2) (Fin 2 ⊕ Fin 2) K) *
        ((A : GL (Fin 2 ⊕ Fin 2) K) : Matrix (Fin 2 ⊕ Fin 2) (Fin 2 ⊕ Fin 2) K) ∨
    ((A : GL (Fin 2 ⊕ Fin 2) K) : Matrix (Fin 2 ⊕ Fin 2) (Fin 2 ⊕ Fin 2) K) *
        ((B : GL (Fin 2 ⊕ Fin 2) K) : Matrix (Fin 2 ⊕ Fin 2) (Fin 2 ⊕ Fin 2) K) =
      -(((B : GL (Fin 2 ⊕ Fin 2) K) : Matrix (Fin 2 ⊕ Fin 2) (Fin 2 ⊕ Fin 2) K) *
        ((A : GL (Fin 2 ⊕ Fin 2) K) : Matrix (Fin 2 ⊕ Fin 2) (Fin 2 ⊕ Fin 2) K)) := by
  have := eq_or_eq_neg_of_proj_eq (a := B * A) (b := A * B) (by rw [map_mul, map_mul, h])
  simpa only [Subgroup.coe_mul, Units.val_mul] using this

theorem mul_sq_comm {n : Type*} [Fintype n] {A N : Matrix n n K}
    (h : A * N = N * A ∨ A * N = -(N * A)) : A * (N * N) = N * N * A := by
  rcases h with h | h
  · rw [← Matrix.mul_assoc, h, Matrix.mul_assoc, h, Matrix.mul_assoc]
  · rw [← Matrix.mul_assoc, h, Matrix.neg_mul, Matrix.mul_assoc, h, Matrix.mul_neg, neg_neg,
      Matrix.mul_assoc]

@[expose] def upperSL : Matrix.SpecialLinearGroup (Fin 2) K := ⟨!![1, 1; 0, 1], by simp⟩

@[expose] def lowerSL : Matrix.SpecialLinearGroup (Fin 2) K := ⟨!![1, 0; 1, 1], by simp⟩

theorem upperSL_mul_self :
    (upperSL (K := K) : Matrix (Fin 2) (Fin 2) K) * (upperSL (K := K) : Matrix (Fin 2) (Fin 2) K) =
      !![1, 2; 0, 1] := by
  simp [upperSL]
  norm_num

theorem lowerSL_mul_self :
    (lowerSL (K := K) : Matrix (Fin 2) (Fin 2) K) * (lowerSL (K := K) : Matrix (Fin 2) (Fin 2) K) =
      !![1, 0; 2, 1] := by
  simp [lowerSL]
  norm_num

theorem exists_kron_of_mem_centralizer_Lsub (h2 : (2 : K) ≠ 0) {A : StatedSp 2 K}
    (hA : proj 2 K A ∈ centralizer (Lsub K : Set (StatedProj (StatedSp 2 K)))) :
    ∃ h : Matrix (Fin 2) (Fin 2) K,
      ((A : GL (Fin 2 ⊕ Fin 2) K) : Matrix (Fin 2 ⊕ Fin 2) (Fin 2 ⊕ Fin 2) K) = kron 1 h ∧
        hᵀ * h = 1 := by
  have key : ∀ g : Matrix.SpecialLinearGroup (Fin 2) K,
      ((A : GL (Fin 2 ⊕ Fin 2) K) : Matrix (Fin 2 ⊕ Fin 2) (Fin 2 ⊕ Fin 2) K) *
          kron ((g : Matrix (Fin 2) (Fin 2) K) * (g : Matrix (Fin 2) (Fin 2) K)) 1 =
        kron ((g : Matrix (Fin 2) (Fin 2) K) * (g : Matrix (Fin 2) (Fin 2) K)) 1 *
          ((A : GL (Fin 2 ⊕ Fin 2) K) : Matrix (Fin 2 ⊕ Fin 2) (Fin 2 ⊕ Fin 2) K) := by
    intro g
    have hmem : proj 2 K (diagSL K g) ∈ Lsub K := ⟨diagSL K g, ⟨g, rfl⟩, rfl⟩
    have h' := mul_eq_or_eq_neg_of_commute (Subgroup.mem_centralizer_iff.mp hA _ hmem).symm
    rw [coe_diagSL] at h'
    rw [← Matrix.mul_one (1 : Matrix (Fin 2) (Fin 2) K), ← kron_mul]
    exact mul_sq_comm h'
  have hk := eq_kron_one_of_commute h2 h2 (upperSL_mul_self (K := K) ▸ key upperSL)
    (lowerSL_mul_self (K := K) ▸ key lowerSL)
  refine ⟨_, hk, ?_⟩
  have hs := symplectic_of_mem A
  rw [hk, kron_symplectic_iff, det_one, one_smul] at hs
  exact hs

theorem adjugate_eq_of_orthogonal {h : Matrix (Fin 2) (Fin 2) K} (hh : hᵀ * h = 1) :
    adjugate h = h.det • hᵀ := by
  calc adjugate h = hᵀ * h * adjugate h := by rw [hh, Matrix.one_mul]
    _ = hᵀ * (h * adjugate h) := Matrix.mul_assoc _ _ _
    _ = h.det • hᵀ := by rw [mul_adjugate, Matrix.mul_smul, Matrix.mul_one]

theorem det_mul_self_of_orthogonal {h : Matrix (Fin 2) (Fin 2) K} (hh : hᵀ * h = 1) :
    h.det * h.det = 1 := by
  have := congrArg Matrix.det hh
  rwa [det_mul, det_transpose, det_one] at this

theorem mul_self_eq_one_of_orthogonal {h : Matrix (Fin 2) (Fin 2) K} (hh : hᵀ * h = 1)
    (hd : h.det = -1) : h * h = 1 := by
  have ha := adjugate_eq_of_orthogonal hh
  rw [hd, adjugate_fin_two] at ha
  have e := congrFun (congrFun ha 0) 1
  simp at e
  have hs : hᵀ = h := by
    ext i j
    fin_cases i <;> fin_cases j <;> simp [e]
  rw [← hh, hs]

theorem rot_of_orthogonal {h : Matrix (Fin 2) (Fin 2) K} (hh : hᵀ * h = 1) (hd : h.det = 1) :
    h 1 1 = h 0 0 ∧ h 1 0 = -h 0 1 := by
  have ha := adjugate_eq_of_orthogonal hh
  rw [hd, one_smul, adjugate_fin_two] at ha
  have e1 := congrFun (congrFun ha 0) 0
  have e2 := congrFun (congrFun ha 0) 1
  simp at e1 e2
  exact ⟨e1, e2.symm⟩

theorem rot_comm {h h' : Matrix (Fin 2) (Fin 2) K} (hr : h 1 1 = h 0 0 ∧ h 1 0 = -h 0 1)
    (hr' : h' 1 1 = h' 0 0 ∧ h' 1 0 = -h' 0 1) : h * h' = h' * h := by
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [Matrix.mul_apply, Fin.sum_univ_two, hr.1, hr.2, hr'.1, hr'.2] <;> ring

theorem det_eq_one_of_kron {A : StatedSp 2 K} {h : Matrix (Fin 2) (Fin 2) K}
    (hA : ((A : GL (Fin 2 ⊕ Fin 2) K) : Matrix (Fin 2 ⊕ Fin 2) (Fin 2 ⊕ Fin 2) K) = kron 1 h)
    (hh : hᵀ * h = 1) (h2 : proj 2 K A ^ 2 ≠ 1) : h.det = 1 := by
  rcases mul_self_eq_one_iff.mp (det_mul_self_of_orthogonal hh) with hd | hd
  · exact hd
  · refine absurd ?_ h2
    have hA2 : A ^ 2 = 1 := sp_ext (by
      rw [pow_two, Subgroup.coe_mul, Units.val_mul, hA, kron_mul, Matrix.one_mul,
        mul_self_eq_one_of_orthogonal hh hd, kron_one_one]
      rfl)
    rw [← map_pow, hA2, map_one]

theorem commute_of_mem_centralizer_Lsub (h2 : (2 : K) ≠ 0) {x y : StatedProj (StatedSp 2 K)}
    (hx : x ∈ centralizer (Lsub K : Set (StatedProj (StatedSp 2 K))))
    (hy : y ∈ centralizer (Lsub K : Set (StatedProj (StatedSp 2 K))))
    (hx2 : x ^ 2 ≠ 1) (hy2 : y ^ 2 ≠ 1) : x * y = y * x := by
  obtain ⟨A, rfl⟩ := proj_surjective x
  obtain ⟨B, rfl⟩ := proj_surjective y
  obtain ⟨h, hA, hh⟩ := exists_kron_of_mem_centralizer_Lsub h2 hx
  obtain ⟨h', hB, hh'⟩ := exists_kron_of_mem_centralizer_Lsub h2 hy
  have hc : h * h' = h' * h :=
    rot_comm (rot_of_orthogonal hh (det_eq_one_of_kron hA hh hx2))
      (rot_of_orthogonal hh' (det_eq_one_of_kron hB hh' hy2))
  rw [← map_mul, ← map_mul]
  congr 1
  apply sp_ext
  simp only [Subgroup.coe_mul, Units.val_mul, hA, hB, kron_mul, Matrix.one_mul, hc]

theorem isPerfect_Lsub [Finite K] (h4 : 4 ≤ Nat.card K) : Group.IsPerfect (Lsub K) := by
  have : Group.IsPerfect (Matrix.SpecialLinearGroup (Fin 2) K) := sl2_isPerfect h4
  have : Group.IsPerfect (diagSL K).range := Group.IsPerfect.range _
  exact Group.IsPerfect.map (proj 2 K)

theorem conj_mem_Lsub [Finite K] (h2 : (2 : K) ≠ 0) (h4 : 4 ≤ Nat.card K)
    {c : StatedProj (StatedSp 2 K)} (hc : c ∈ centralizer {u2 K})
    {l : StatedProj (StatedSp 2 K)} (hl : l ∈ Lsub K) : c * l * c⁻¹ ∈ Lsub K := by
  have : Group.IsPerfect (Lsub K) := isPerfect_Lsub h4
  have hMC : (Lsub K).map (MulAut.conj c).toMonoidHom ≤ centralizer {u2 K} := by
    rintro _ ⟨m, hm, rfl⟩
    exact mul_mem (mul_mem hc (Lsub_le_centralizer hm)) (inv_mem hc)
  have hperf := Subgroup.isPerfect_iff.mp
    (Group.IsPerfect.map (H := Lsub K) (MulAut.conj c).toMonoidHom)
  exact perfect_le_L h2 hMC hperf ⟨l, hl, rfl⟩

theorem centralizer_u2_le_normalizer_Lsub [Finite K] (h2 : (2 : K) ≠ 0) (h4 : 4 ≤ Nat.card K) :
    centralizer {u2 K} ≤ normalizer (Lsub K : Set (StatedProj (StatedSp 2 K))) := by
  intro c hc
  rw [mem_normalizer_iff]
  intro l
  refine ⟨conj_mem_Lsub h2 h4 hc, fun hl => ?_⟩
  have := conj_mem_Lsub h2 h4 (inv_mem hc) hl
  rwa [inv_inv, ← mul_assoc, ← mul_assoc, inv_mul_cancel, one_mul, mul_assoc, inv_mul_cancel,
    mul_one] at this

end CFSG.ClassicalInvolution.Q3.TA3.Sp4
