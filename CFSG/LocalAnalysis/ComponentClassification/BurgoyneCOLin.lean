module

public import CFSG.LocalAnalysis.ComponentClassification.BurgoyneCOShape

public noncomputable section

namespace CFSG.ComponentClassification.Burgoyne.C

open Matrix

variable {K : Type} [Field K]

theorem mul_self_eq_one_of_isometry {n : Type*} [Fintype n] [DecidableEq n] (h2 : (2 : K) ≠ 0)
    {D : Matrix n n K} (hD : Dᵀ = D) (hDinj : ∀ v, D *ᵥ v = 0 → v = 0) {u f : n → K}
    (hiso : (1 + vecMulVec u f)ᵀ * D * (1 + vecMulVec u f) = D) :
    (1 + vecMulVec u f) * (1 + vecMulVec u f) = 1 := by
  set a := D *ᵥ u with ha
  set s := u ⬝ᵥ a with hs
  set t := f ⬝ᵥ u with ht
  have hb : u ᵥ* D = a := by
    rw [ha, ← mulVec_transpose, hD]
  have hE : vecMulVec f a + vecMulVec a f + s • vecMulVec f f = 0 := by
    have e1 : (1 + vecMulVec u f)ᵀ * D = D + vecMulVec f a := by
      rw [transpose_add, transpose_one, transpose_vecMulVec, add_mul, one_mul, vecMulVec_mul, hb]
    have e2 : D * vecMulVec u f = vecMulVec a f := by rw [mul_vecMulVec, ← ha]
    have e3 : vecMulVec f a * vecMulVec u f = s • vecMulVec f f := by
      rw [vecMulVec_mul_vecMulVec, vecMulVec_smul, dotProduct_comm a u, ← hs]
    have key : (1 + vecMulVec u f)ᵀ * D * (1 + vecMulVec u f) =
        D + (vecMulVec f a + vecMulVec a f + s • vecMulVec f f) := by
      rw [e1, add_mul, mul_add, mul_add, mul_one, mul_one, e2, e3]
      abel
    rw [key] at hiso
    have := congrArg (· - D) hiso
    simpa using this
  have hsq : (1 + vecMulVec u f) * (1 + vecMulVec u f) = 1 + (2 + t) • vecMulVec u f := by
    rw [add_mul, mul_add, mul_add, one_mul, mul_one, one_mul, vecMulVec_mul_vecMulVec, ← ht,
      vecMulVec_smul, add_smul, two_smul]
    abel
  rw [hsq]
  by_cases hf : f = 0
  · rw [hf, vecMulVec_zero, smul_zero, add_zero]
  obtain ⟨k, hk⟩ : ∃ k, f k ≠ 0 := by
    by_contra h
    push Not at h
    exact hf (funext h)
  have hEij : ∀ i j, f i * a j + a i * f j + s * (f i * f j) = 0 := by
    intro i j
    have := congrFun (congrFun hE i) j
    simpa [vecMulVec_apply] using this
  have hak : 2 * a k = -(s * f k) := by
    have e := hEij k k
    have : f k * (2 * a k + s * f k) = 0 := by linear_combination e
    linear_combination (mul_eq_zero.1 this).resolve_left hk
  have h3 : (2 : K) * (s / 2) = s := by
    rw [← mul_div_assoc, mul_div_cancel_left₀ s h2]
  have hai : ∀ i, a i = -(s / 2) * f i := by
    intro i
    have e := hEij i k
    have : f k * (2 * a i + s * f i) = 0 := by
      linear_combination 2 * e - f i * hak
    have h' := (mul_eq_zero.1 this).resolve_left hk
    have h4 : (2 : K) * (a i + (s / 2) * f i) = 0 := by
      rw [mul_add, ← mul_assoc, h3]
      exact h'
    have h5 := (mul_eq_zero.1 h4).resolve_left h2
    linear_combination h5
  have hst : s * (2 + t) = 0 := by
    have hafs : a = (-(s / 2)) • f := funext fun i => by rw [hai]; rfl
    have hs' : s = -(s / 2) * t := by
      calc s = u ⬝ᵥ a := hs
        _ = u ⬝ᵥ ((-(s / 2)) • f) := by rw [← hafs]
        _ = -(s / 2) * t := by rw [dotProduct_smul, smul_eq_mul, ht, dotProduct_comm]
    have h6 : 2 * s = -(s * t) := by
      calc 2 * s = 2 * (-(s / 2) * t) := congrArg (2 * ·) hs'
        _ = -((2 * (s / 2)) * t) := by ring
        _ = -(s * t) := by rw [h3]
    linear_combination h6
  rcases mul_eq_zero.1 hst with h | h
  ·
    have ha0 : a = 0 := funext fun i => by rw [hai, h, zero_div, neg_zero, zero_mul]; rfl
    have hu : u = 0 := hDinj u (by rw [← ha, ha0])
    rw [hu]
    simp
  · rw [h, zero_smul, add_zero]

theorem exists_eq_smul_of_finrank_le_two {d : ℕ} {U : Submodule K (Fin d → K)}
    (hU : Module.finrank K U ≤ 2) {I : Finset (Fin d)} {v₀ : Fin d → K} (hv₀ : v₀ ∈ U)
    (hv₀I : v₀ ∈ suppOn K I) (hv₀0 : v₀ ≠ 0) {u a : Fin d → K} (hu : u ∈ U)
    (huI : u ∈ suppOn K Iᶜ) (hu0 : u ≠ 0) (ha : a ∈ U) (haI : a ∈ suppOn K Iᶜ) :
    ∃ c : K, a = c • u := by
  set x : Fin 3 → Fin d → K := ![v₀, u, a] with hx
  have hxU : ∀ i, x i ∈ U := by
    intro i
    fin_cases i
    · exact hv₀
    · exact hu
    · exact ha
  have hnot : ¬ LinearIndependent K x := by
    intro hli
    have hli' : LinearIndependent K (fun i => (⟨x i, hxU i⟩ : U)) :=
      LinearIndependent.of_comp U.subtype hli
    have := hli'.fintype_card_le_finrank
    rw [Fintype.card_fin] at this
    omega
  obtain ⟨g, hg, i₀, hi₀⟩ := Fintype.not_linearIndependent_iff.1 hnot
  rw [Fin.sum_univ_three] at hg
  simp only [hx, Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.cons_val_two,
    Matrix.head_cons, Matrix.tail_cons] at hg
  have hg0 : g 0 = 0 := by
    by_contra hg0
    apply hv₀0
    funext i
    by_cases hi : i ∈ I
    · have e := congrFun hg i
      simp only [Pi.add_apply, Pi.smul_apply, smul_eq_mul, Pi.zero_apply] at e
      rw [huI i (by simpa using hi), haI i (by simpa using hi), mul_zero, mul_zero, add_zero,
        add_zero] at e
      exact (mul_eq_zero.1 e).resolve_left hg0
    · exact hv₀I i hi
  rw [hg0, zero_smul, zero_add] at hg
  have hg2 : g 2 ≠ 0 := by
    intro hg2
    rw [hg2, zero_smul, add_zero] at hg
    have hg1 : g 1 = 0 := (smul_eq_zero.1 hg).resolve_right hu0
    fin_cases i₀
    · exact hi₀ hg0
    · exact hi₀ hg1
    · exact hi₀ hg2
  refine ⟨-(g 1 / g 2), ?_⟩
  have : g 2 • a = -(g 1 • u) := by
    rw [← add_eq_zero_iff_eq_neg, add_comm]
    exact hg
  calc a = (g 2)⁻¹ • (g 2 • a) := by rw [smul_smul, inv_mul_cancel₀ hg2, one_smul]
    _ = -(g 1 / g 2) • u := by
        rw [this, smul_neg, smul_smul, neg_smul, div_eq_inv_mul]

end CFSG.ComponentClassification.Burgoyne.C
