module

public import CFSG.GH74.GLS.Stage2.Signalizer.Ivk8P4S55BTSp4M
public import Mathlib.RingTheory.Henselian
public import Mathlib.RingTheory.RegularLocalRing.Defs
public import Mathlib.RingTheory.TotallySplit

public section

namespace CFSG.GH74.GLS.Stage2.Signalizer.Ivk8.BT

namespace BL4

open Matrix

variable {F : Type} [Field F]

abbrev dD : Matrix (Fin 2 ⊕ Fin 2) (Fin 2 ⊕ Fin 2) F := fromBlocks 1 0 0 (-1)

abbrev jT : Matrix (Fin 2) (Fin 2) F := !![0, 1; -1, 0]

theorem eq_fromBlocks_of_comm_dD (h2 : (2 : F) ≠ 0)
    {x : Matrix (Fin 2 ⊕ Fin 2) (Fin 2 ⊕ Fin 2) F} (h : dD * x = x * dD) :
    x = fromBlocks x.toBlocks₁₁ 0 0 x.toBlocks₂₂ := by
  have hx := fromBlocks_toBlocks x
  rw [← hx, fromBlocks_multiply, fromBlocks_multiply] at h
  simp only [Matrix.one_mul, Matrix.zero_mul, add_zero, zero_add, Matrix.mul_one,
    Matrix.mul_zero, Matrix.neg_mul, Matrix.mul_neg, fromBlocks_inj] at h
  obtain ⟨-, h12, h21, -⟩ := h
  have e12 : x.toBlocks₁₂ = 0 := by
    have : (2 : F) • x.toBlocks₁₂ = 0 := by rw [two_smul]; nth_rw 1 [h12]; abel
    exact (smul_eq_zero.mp this).resolve_left h2
  have e21 : x.toBlocks₂₁ = 0 := by
    have : (2 : F) • x.toBlocks₂₁ = 0 := by rw [two_smul]; nth_rw 2 [← h21]; abel
    exact (smul_eq_zero.mp this).resolve_left h2
  conv_lhs => rw [← hx, e12, e21]

theorem trace_fromBlocks' (a b c d : Matrix (Fin 2) (Fin 2) F) :
    (fromBlocks a b c d).trace = a.trace + d.trace := by
  simp [Matrix.trace, Fintype.sum_sum_type]

theorem ne_smul_of_trace_eq_zero (h2 : (2 : F) ≠ 0) {b : Matrix (Fin 2) (Fin 2) F}
    (hb : b * b = 1) (htr : b.trace = 0) : ∀ c : F, b ≠ c • 1 := by
  intro c hc
  rw [hc, trace_smul, trace_one, Fintype.card_fin, smul_eq_mul] at htr
  have hc0 : c = 0 := (mul_eq_zero.mp (by simpa [mul_comm] using htr)).resolve_right
    (by exact_mod_cast h2)
  rw [hc, hc0, zero_smul, Matrix.zero_mul] at hb
  have := congrFun (congrFun hb 0) 0
  simp at this

theorem comm_of_two_involutions (h2 : (2 : F) ≠ 0)
    {B : Matrix (Fin 2 ⊕ Fin 2) (Fin 2 ⊕ Fin 2) F} (hB2 : B * B = 1) (hDB : dD * B = B * dD)
    (htr : B.trace = 0) (htrD : (dD * B).trace = 0)
    {x y : Matrix (Fin 2 ⊕ Fin 2) (Fin 2 ⊕ Fin 2) F} (hx : dD * x = x * dD) (hxB : B * x = x * B)
    (hy : dD * y = y * dD) (hyB : B * y = y * B) : x * y = y * x := by
  rw [eq_fromBlocks_of_comm_dD h2 hDB] at hB2 htr htrD hxB hyB
  rw [eq_fromBlocks_of_comm_dD h2 hx] at hxB ⊢
  rw [eq_fromBlocks_of_comm_dD h2 hy] at hyB ⊢
  simp only [fromBlocks_multiply, Matrix.mul_zero, Matrix.zero_mul, add_zero, zero_add,
    Matrix.one_mul, Matrix.neg_mul, fromBlocks_inj, ← fromBlocks_one, trace_fromBlocks',
    trace_neg] at hB2 htr htrD hxB hyB ⊢
  obtain ⟨hp, -, -, hm⟩ := hB2
  obtain ⟨hxp, -, -, hxm⟩ := hxB
  obtain ⟨hyp, -, -, hym⟩ := hyB
  have htp : B.toBlocks₁₁.trace = 0 := by
    have : (2 : F) * B.toBlocks₁₁.trace = 0 := by linear_combination htr + htrD
    exact (mul_eq_zero.mp this).resolve_left h2
  have htm : B.toBlocks₂₂.trace = 0 := by
    have : (2 : F) * B.toBlocks₂₂.trace = 0 := by linear_combination htr - htrD
    exact (mul_eq_zero.mp this).resolve_left h2
  refine ⟨BS4.comm_of_comm_nonscalar (ne_smul_of_trace_eq_zero h2 hp htp) hxp.symm hyp.symm,
    trivial, trivial,
    BS4.comm_of_comm_nonscalar (ne_smul_of_trace_eq_zero h2 hm htm) hxm.symm hym.symm⟩

theorem mul_J_mul_transpose (M : Matrix (Fin 2) (Fin 2) F) : M * jT * Mᵀ = M.det • jT := by
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [Matrix.mul_apply, Fin.sum_univ_two, Matrix.det_fin_two] <;> ring

theorem comm_jT_of_so2 {M β : Matrix (Fin 2) (Fin 2) F} (hdet : M.det = 1)
    (hM : Mᵀ * β * M = β) : M * (jT * β) = (jT * β) * M := by
  calc M * (jT * β) = M * jT * (Mᵀ * β * M) := by rw [hM, Matrix.mul_assoc]
    _ = (M * jT * Mᵀ) * β * M := by simp only [Matrix.mul_assoc]
    _ = (jT * β) * M := by rw [mul_J_mul_transpose, hdet, one_smul]

theorem jT_mul_ne_smul (h2 : (2 : F) ≠ 0) {β : Matrix (Fin 2) (Fin 2) F} (hβ : βᵀ = β)
    (hdet : β.det ≠ 0) : ∀ c : F, jT * β ≠ c • 1 := by
  intro c hc
  have e := fun i j => congrFun (congrFun hc i) j
  have e00 := e 0 0
  have e01 := e 0 1
  have e10 := e 1 0
  have e11 := e 1 1
  simp [Matrix.mul_apply, Fin.sum_univ_two] at e00 e01 e10 e11
  have hs := congrFun (congrFun hβ 0) 1
  simp only [transpose_apply] at hs
  apply hdet
  have hc0 : c = 0 := by
    have : (2 : F) * c = 0 := by linear_combination -e00 - e11 + hs
    exact (mul_eq_zero.mp this).resolve_left h2
  rw [hc0] at e00
  rw [Matrix.det_fin_two, e00, e01, e10]
  ring

theorem comm_of_so2 (h2 : (2 : F) ≠ 0) {β M N : Matrix (Fin 2) (Fin 2) F} (hβ : βᵀ = β)
    (hdet : β.det ≠ 0) (hMd : M.det = 1) (hM : Mᵀ * β * M = β) (hNd : N.det = 1)
    (hN : Nᵀ * β * N = β) : M * N = N * M :=
  BS4.comm_of_comm_nonscalar (jT_mul_ne_smul h2 hβ hdet) (comm_jT_of_so2 hMd hM)
    (comm_jT_of_so2 hNd hN)

end BL4

end CFSG.GH74.GLS.Stage2.Signalizer.Ivk8.BT
