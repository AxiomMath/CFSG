module

import Mathlib.FieldTheory.ChevalleyWarning
public import Mathlib.LinearAlgebra.Matrix.Adjugate

public section

namespace CFSG.ClassicalInvolution.PhanB3.S.Std.Q

open Matrix

variable {K : Type} [Field K]

@[expose] def Bf (N : Matrix (Fin 3) (Fin 3) K) (x x' : Fin 3 → K) : K := x ⬝ᵥ (N *ᵥ x')

theorem Bf_def (N : Matrix (Fin 3) (Fin 3) K) (x x' : Fin 3 → K) :
    Bf N x x' = ∑ i, ∑ j, x i * N i j * x' j := by
  simp only [Bf, dotProduct, mulVec, Finset.mul_sum]
  exact Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun j _ => by ring

theorem exists_isotropic [Finite K] (N : Matrix (Fin 3) (Fin 3) K) :
    ∃ e : Fin 3 → K, e ≠ 0 ∧ Bf N e e = 0 := by
  classical
  have := Fintype.ofFinite K
  have hp : Fact (ringChar K).Prime := ⟨CharP.char_is_prime K _⟩
  let F : MvPolynomial (Fin 3) K :=
    ∑ i, ∑ j, MvPolynomial.C (N i j) * MvPolynomial.X i * MvPolynomial.X j
  have hdeg : F.totalDegree ≤ 2 := by
    refine (MvPolynomial.totalDegree_finsetSum _ _).trans (Finset.sup_le fun i _ => ?_)
    refine (MvPolynomial.totalDegree_finsetSum _ _).trans (Finset.sup_le fun j _ => ?_)
    calc (MvPolynomial.C (N i j) * MvPolynomial.X i * MvPolynomial.X j).totalDegree
        ≤ (MvPolynomial.C (N i j) * MvPolynomial.X i).totalDegree +
            (MvPolynomial.X j : MvPolynomial (Fin 3) K).totalDegree :=
          MvPolynomial.totalDegree_mul _ _
      _ ≤ ((MvPolynomial.C (N i j) : MvPolynomial (Fin 3) K).totalDegree +
            (MvPolynomial.X i : MvPolynomial (Fin 3) K).totalDegree) +
            (MvPolynomial.X j : MvPolynomial (Fin 3) K).totalDegree :=
          Nat.add_le_add_right (MvPolynomial.totalDegree_mul _ _) _
      _ ≤ 2 := by simp [MvPolynomial.totalDegree_C, MvPolynomial.totalDegree_X]
  have hdvd := char_dvd_card_solutions (ringChar K)
    (show F.totalDegree < Fintype.card (Fin 3) by rw [Fintype.card_fin]; omega)
  have heval : ∀ x : Fin 3 → K, MvPolynomial.eval x F = Bf N x x := by
    intro x
    rw [Bf_def]
    simp only [F, map_sum, map_mul, MvPolynomial.eval_C, MvPolynomial.eval_X]
    exact Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun j _ => by ring
  by_contra hcon
  push Not at hcon
  have hcard : ∀ [inst : Fintype {x : Fin 3 → K // MvPolynomial.eval x F = 0}],
      Fintype.card {x : Fin 3 → K // MvPolynomial.eval x F = 0} = 1 := by
    intro inst
    rw [Fintype.card_eq_one_iff]
    refine ⟨⟨0, by rw [heval]; simp [Bf]⟩, fun ⟨x, hx⟩ => Subtype.ext ?_⟩
    by_contra hne
    exact hcon x hne (by rw [← heval]; exact hx)
  rw [@hcard _] at hdvd
  exact hp.out.one_lt.ne' (Nat.dvd_one.1 hdvd)

section Identities

variable (N : Matrix (Fin 3) (Fin 3) K) (hs : Nᵀ = N)

@[expose] def cr (a y : Fin 3 → K) : Fin 3 → K :=
  ![a 1 * y 2 - a 2 * y 1, a 2 * y 0 - a 0 * y 2, a 0 * y 1 - a 1 * y 0]

include hs in
theorem Bf_adj_cr_left (a y : Fin 3 → K) : Bf N (N.adjugate *ᵥ cr a y) a = 0 := by
  have h01 : N 1 0 = N 0 1 := by simpa using congrFun (congrFun hs 0) 1
  have h02 : N 2 0 = N 0 2 := by simpa using congrFun (congrFun hs 0) 2
  have h12 : N 2 1 = N 1 2 := by simpa using congrFun (congrFun hs 1) 2
  simp [Bf_def, Fin.sum_univ_three, Matrix.adjugate_fin_three, cr, h01, h02, h12]
  ring

include hs in
theorem Bf_adj_cr_right (a y : Fin 3 → K) : Bf N (N.adjugate *ᵥ cr a y) y = 0 := by
  have h01 : N 1 0 = N 0 1 := by simpa using congrFun (congrFun hs 0) 1
  have h02 : N 2 0 = N 0 2 := by simpa using congrFun (congrFun hs 0) 2
  have h12 : N 2 1 = N 1 2 := by simpa using congrFun (congrFun hs 1) 2
  simp [Bf_def, Fin.sum_univ_three, Matrix.adjugate_fin_three, cr, h01, h02, h12]
  ring

include hs in
theorem Bf_adj_cr_self (a y : Fin 3 → K) :
    Bf N (N.adjugate *ᵥ cr a y) (N.adjugate *ᵥ cr a y) =
      N.det * (Bf N a a * Bf N y y - Bf N a y ^ 2) := by
  have h01 : N 1 0 = N 0 1 := by simpa using congrFun (congrFun hs 0) 1
  have h02 : N 2 0 = N 0 2 := by simpa using congrFun (congrFun hs 0) 2
  have h12 : N 2 1 = N 1 2 := by simpa using congrFun (congrFun hs 1) 2
  simp [Bf_def, Fin.sum_univ_three, Matrix.adjugate_fin_three, cr, h01, h02, h12,
    Matrix.det_fin_three]
  ring

include hs in
theorem Bf_comm' (x x' : Fin 3 → K) : Bf N x x' = Bf N x' x := by
  have h01 : N 1 0 = N 0 1 := by simpa using congrFun (congrFun hs 0) 1
  have h02 : N 2 0 = N 0 2 := by simpa using congrFun (congrFun hs 0) 2
  have h12 : N 2 1 = N 1 2 := by simpa using congrFun (congrFun hs 1) 2
  simp only [Bf_def, Fin.sum_univ_three, h01, h02, h12]
  ring

include hs in
theorem Bf_conic (y v a : Fin 3 → K) (s c : K) :
    Bf N (y + s • v + c • a) (y + s • v + c • a) =
      Bf N y y + s ^ 2 * Bf N v v + c ^ 2 * Bf N a a + 2 * s * Bf N y v + 2 * c * Bf N y a +
        2 * s * c * Bf N v a := by
  have h01 : N 1 0 = N 0 1 := by simpa using congrFun (congrFun hs 0) 1
  have h02 : N 2 0 = N 0 2 := by simpa using congrFun (congrFun hs 0) 2
  have h12 : N 2 1 = N 1 2 := by simpa using congrFun (congrFun hs 1) 2
  simp only [Bf_def, Fin.sum_univ_three, h01, h02, h12, Pi.add_apply, Pi.smul_apply, smul_eq_mul]
  ring

theorem Bf_add_left (x x' z : Fin 3 → K) : Bf N (x + x') z = Bf N x z + Bf N x' z := by
  simp [Bf, add_dotProduct]

theorem Bf_add_right (x x' z : Fin 3 → K) : Bf N z (x + x') = Bf N z x + Bf N z x' := by
  simp [Bf, Matrix.mulVec_add, dotProduct_add]

theorem Bf_smul_left (c : K) (x z : Fin 3 → K) : Bf N (c • x) z = c * Bf N x z := by
  simp [Bf, smul_dotProduct]

theorem Bf_smul_right (c : K) (x z : Fin 3 → K) : Bf N z (c • x) = c * Bf N z x := by
  simp [Bf, Matrix.mulVec_smul, dotProduct_smul]

end Identities

theorem exists_conic_param [Finite K] (h2 : (2 : K) ≠ 0) (N : Matrix (Fin 3) (Fin 3) K)
    (hs : Nᵀ = N) (hN : N.det ≠ 0) :
    ∃ (y v a : Fin 3 → K) (γ : K), γ ≠ 0 ∧
      (∀ s : K, Bf N (y + s • v + (γ * s ^ 2) • a) (y + s • v + (γ * s ^ 2) • a) = 0) ∧
      ∀ x : Fin 3 → K, ∃ c₁ c₂ c₃ : K, x = c₁ • y + c₂ • v + c₃ • a := by
  classical
  obtain ⟨a, ha0, haa⟩ := exists_isotropic N
  have hNa : N.mulVec a ≠ 0 := fun h => ha0 (Matrix.eq_zero_of_mulVec_eq_zero hN h)
  obtain ⟨i, hi⟩ : ∃ i, N.mulVec a i ≠ 0 := by
    by_contra hcon
    push Not at hcon
    exact hNa (funext hcon)
  set m := N.mulVec a i with hm
  let y₀ : Fin 3 → K := Pi.single i 1
  have hy0a : Bf N y₀ a = m := by
    simp [Bf, y₀, hm]
  set B₀ := Bf N y₀ y₀ with hB₀
  set t := B₀ / (2 * m ^ 2) with ht
  set y : Fin 3 → K := m⁻¹ • y₀ + (-t) • a with hy
  have hay : Bf N y a = 1 := by
    rw [hy, Bf_add_left, Bf_smul_left, Bf_smul_left, hy0a, haa]
    field_simp
    ring
  have hya' : Bf N a y = 1 := by rw [Bf_comm' N hs]; exact hay
  have hyy : Bf N y y = 0 := by
    have hc := Bf_comm' N hs y₀ a
    rw [hy, Bf_add_left, Bf_add_right, Bf_add_right, Bf_smul_left, Bf_smul_left, Bf_smul_left,
      Bf_smul_left, Bf_smul_right, Bf_smul_right, Bf_smul_right, Bf_smul_right, ← hB₀,
      hy0a, ← hc, hy0a, haa, ht]
    field_simp
    ring
  set v : Fin 3 → K := N.adjugate *ᵥ cr a y with hv
  have hva : Bf N v a = 0 := Bf_adj_cr_left N hs a y
  have hvy : Bf N v y = 0 := Bf_adj_cr_right N hs a y
  have hvv : Bf N v v = -N.det := by
    have := Bf_adj_cr_self N hs a y
    rw [haa, hyy, hya'] at this
    rw [hv, this]
    ring
  have hav : Bf N a v = 0 := by rw [Bf_comm' N hs]; exact hva
  have hyv : Bf N y v = 0 := by rw [Bf_comm' N hs]; exact hvy
  refine ⟨y, v, a, N.det / 2, div_ne_zero hN h2, fun s => ?_, ?_⟩
  · rw [Bf_conic N hs, hyy, hvv, haa, hyv, hay, hva]
    field_simp
    ring
  · let Mx : Matrix (Fin 3) (Fin 3) K := Matrix.of ![a, y, v]
    have hG : Mx * N * Mxᵀ = !![0, 1, 0; 1, 0, 0; 0, 0, -N.det] := by
      ext r c
      have e : (Mx * N * Mxᵀ) r c = Bf N (![a, y, v] r) (![a, y, v] c) := by
        rw [Bf_def]
        simp only [Matrix.mul_apply, Matrix.transpose_apply, Fin.sum_univ_three]
        fin_cases r <;> fin_cases c <;>
          simp only [Mx, Matrix.of_apply, Matrix.cons_val_zero, Matrix.cons_val_one,
            Matrix.head_cons, Matrix.cons_val_two, Matrix.tail_cons, Fin.isValue,
            Fin.zero_eta, Fin.mk_one, Fin.reduceFinMk] <;> ring
      rw [e]
      fin_cases r <;> fin_cases c <;> simp [haa, hya', hay, hav, hva, hyy, hvy, hyv, hvv]
    have hΓ : (!![0, 1, 0; 1, 0, 0; 0, 0, -N.det] : Matrix (Fin 3) (Fin 3) K).det = N.det := by
      simp [Matrix.det_fin_three]
    have hdet : Mx.det * N.det * Mx.det = N.det := by
      have := congrArg Matrix.det hG
      rw [Matrix.det_mul, Matrix.det_mul, Matrix.det_transpose, hΓ] at this
      exact this
    have hMx : Mx.det ≠ 0 := by
      intro h0
      rw [h0] at hdet
      simp at hdet
      exact hN hdet.symm
    intro x
    have hu : IsUnit Mx.det := isUnit_iff_ne_zero.2 hMx
    have hc : (x ᵥ* Mx⁻¹) ᵥ* Mx = x := by
      rw [Matrix.vecMul_vecMul, Matrix.nonsing_inv_mul _ hu, Matrix.vecMul_one]
    refine ⟨(x ᵥ* Mx⁻¹) 1, (x ᵥ* Mx⁻¹) 2, (x ᵥ* Mx⁻¹) 0, ?_⟩
    ext k
    have := congrFun hc k
    simp only [Matrix.vecMul, dotProduct, Fin.sum_univ_three, Mx, Matrix.of_apply] at this ⊢
    simp only [Pi.add_apply, Pi.smul_apply, smul_eq_mul]
    simp at this
    linear_combination -this

end CFSG.ClassicalInvolution.PhanB3.S.Std.Q
