module

public import CFSG.LocalAnalysis.QuasithinUnique.Ch1.Lemma115OddL3Block

public section

namespace CFSG.QuasithinUnique.Ch1

open CFSG.Assembly.LowTwoRank CFSG.QuasithinUnique CFSG.LieType.Steinberg Matrix
open scoped MatrixGroups

section Adapted

variable {K : Type} [Field K]

theorem eq_of_forall_mulVec {A B : Matrix (Fin 3) (Fin 3) K} (h : ∀ x, A *ᵥ x = B *ᵥ x) :
    A = B := by
  ext i j
  have := congrFun (h (Pi.single j 1)) i
  simpa [Matrix.mulVec_single_one] using this

theorem exists_adapted_basis_of_line {B : Matrix (Fin 3) (Fin 3) K}
    (U W : Submodule K (Fin 3 → K)) (hUW : IsCompl U W)
    (hU : ∀ x ∈ U, B *ᵥ x = x) (hW : ∀ x ∈ W, B *ᵥ x = -x)
    (hU1 : Module.finrank K U = 1) (hW2 : Module.finrank K W = 2) :
    ∃ Q : GL (Fin 3) K,
      B * (Q : Matrix (Fin 3) (Fin 3) K) = (Q : Matrix (Fin 3) (Fin 3) K) * D3 := by
  classical
  let b : Module.Basis (Fin 2) K W := Module.finBasisOfFinrankEq K W hW2
  let c : Module.Basis (Fin 1) K U := Module.finBasisOfFinrankEq K U hU1
  let w0 : Fin 3 → K := (b 0 : W)
  let w1 : Fin 3 → K := (b 1 : W)
  let u0 : Fin 3 → K := (c 0 : U)
  let Q0 : Matrix (Fin 3) (Fin 3) K := Matrix.of fun i j => ![w0 i, w1 i, u0 i] j
  have hw0 : B *ᵥ w0 = -w0 := hW _ (b 0).2
  have hw1 : B *ᵥ w1 = -w1 := hW _ (b 1).2
  have hu0 : B *ᵥ u0 = u0 := hU _ (c 0).2
  have hBQ : B * Q0 = Q0 * D3 := by
    ext i j
    rw [D3, Matrix.mul_diagonal]
    fin_cases j
    · have := congrFun hw0 i
      simpa [Q0, Matrix.mul_apply, Matrix.mulVec, dotProduct] using this
    · have := congrFun hw1 i
      simpa [Q0, Matrix.mul_apply, Matrix.mulVec, dotProduct] using this
    · have := congrFun hu0 i
      simpa [Q0, Matrix.mul_apply, Matrix.mulVec, dotProduct] using this
  have key : ∀ x : Fin 3 → K, Q0 *ᵥ x = 0 → x = 0 := by
    intro x hx
    have hsum : Q0 *ᵥ x = x 0 • w0 + x 1 • w1 + x 2 • u0 := by
      ext i
      simp [Q0, Matrix.mulVec, dotProduct, Fin.sum_univ_three]
      ring
    let yW : W := x 0 • b 0 + x 1 • b 1
    let zU : U := x 2 • c 0
    have hy : (yW : Fin 3 → K) = x 0 • w0 + x 1 • w1 := rfl
    have hz : (zU : Fin 3 → K) = x 2 • u0 := rfl
    have hyz : (yW : Fin 3 → K) + (zU : Fin 3 → K) = 0 := by
      rw [hy, hz, ← hsum]
      exact hx
    have hyU : (yW : Fin 3 → K) ∈ U := by
      have : (yW : Fin 3 → K) = ((-zU : U) : Fin 3 → K) := by
        rw [Submodule.coe_neg]
        exact eq_neg_of_add_eq_zero_left hyz
      rw [this]
      exact (-zU : U).2
    have hy0 : (yW : Fin 3 → K) = 0 :=
      Submodule.disjoint_def.1 hUW.disjoint _ hyU yW.2
    have hz0 : (zU : Fin 3 → K) = 0 := by
      rw [hy0, zero_add] at hyz
      exact hyz
    have hyW0 : yW = 0 := Subtype.ext hy0
    have hzU0 : zU = 0 := Subtype.ext hz0
    have hb0 : x 0 = 0 ∧ x 1 = 0 := by
      have hli := Fintype.linearIndependent_iff.1 b.linearIndependent ![x 0, x 1]
        (by simpa [Fin.sum_univ_two] using hyW0)
      exact ⟨by simpa using hli 0, by simpa using hli 1⟩
    have hx2 : x 2 = 0 :=
      (smul_eq_zero.1 hzU0).resolve_right (c.ne_zero 0)
    ext i
    fin_cases i
    · exact hb0.1
    · exact hb0.2
    · exact hx2
  have hinj : Function.Injective Q0.mulVec := by
    intro x y hxy
    refine sub_eq_zero.1 (key _ ?_)
    rw [Matrix.mulVec_sub, hxy, sub_self]
  obtain ⟨Q, hQ⟩ := Matrix.mulVec_injective_iff_isUnit.1 hinj
  exact ⟨Q, by rw [hQ]; exact hBQ⟩

theorem exists_adapted_basis (h2 : (2 : K) ≠ 0) {A : Matrix (Fin 3) (Fin 3) K}
    (hA2 : A * A = 1) (hdet : A.det = 1) (hA1 : A ≠ 1) :
    ∃ Q : GL (Fin 3) K,
      A * (Q : Matrix (Fin 3) (Fin 3) K) = (Q : Matrix (Fin 3) (Fin 3) K) * D3 := by
  classical
  let f : Module.End K (Fin 3 → K) := Matrix.toLin' A
  let E : Module.End K (Fin 3 → K) := (2 : K)⁻¹ • (1 + f)
  have hEx : ∀ x, E x = (2 : K)⁻¹ • (x + A *ᵥ x) := by
    intro x
    simp [E, f, Matrix.toLin'_apply]
  have hAA : ∀ x, A *ᵥ (A *ᵥ x) = x := by
    intro x
    rw [Matrix.mulVec_mulVec, hA2, Matrix.one_mulVec]
  have hEE : IsIdempotentElem E := by
    refine LinearMap.ext fun x => ?_
    show E (E x) = E x
    rw [hEx (E x), hEx x]
    simp only [Matrix.mulVec_smul, Matrix.mulVec_add, hAA]
    have h1 : x + A *ᵥ x + (A *ᵥ x + x) = (2 : K) • (x + A *ᵥ x) := by
      rw [two_smul]
      abel
    rw [← smul_add, h1, smul_smul (2 : K)⁻¹ (2 : K) (x + A *ᵥ x), inv_mul_cancel₀ h2, one_smul]
  have hAx : ∀ x, x ∈ LinearMap.range E → A *ᵥ x = x := by
    intro x hx
    have h1 : E x = x := (LinearMap.IsIdempotentElem.mem_range_iff hEE).1 hx
    rw [hEx] at h1
    have h3 : x + A *ᵥ x = x + x := by
      calc x + A *ᵥ x = (2 : K) • ((2 : K)⁻¹ • (x + A *ᵥ x)) := by
            rw [smul_smul, mul_inv_cancel₀ h2, one_smul]
        _ = (2 : K) • x := by rw [h1]
        _ = x + x := two_smul K x
    exact add_left_cancel h3
  have hAx' : ∀ x, x ∈ LinearMap.ker E → A *ᵥ x = -x := by
    intro x hx
    have h1 : E x = 0 := hx
    rw [hEx] at h1
    have h3 : x + A *ᵥ x = 0 := by
      rcases smul_eq_zero.1 h1 with h | h
      · exact absurd h (inv_ne_zero h2)
      · exact h
    exact eq_neg_of_add_eq_zero_right h3
  have hcompl : IsCompl (LinearMap.range E) (LinearMap.ker E) :=
    LinearMap.IsIdempotentElem.isCompl hEE
  have hsum : Module.finrank K (LinearMap.range E) + Module.finrank K (LinearMap.ker E) = 3 := by
    rw [Submodule.finrank_add_eq_of_isCompl hcompl, Module.finrank_fin_fun]
  have hne1 : LinearMap.range E ≠ ⊥ := by
    intro hbot
    have hE0 : E = 0 := LinearMap.range_eq_bot.1 hbot
    have hall : ∀ x, A *ᵥ x = (-1 : Matrix (Fin 3) (Fin 3) K) *ᵥ x := by
      intro x
      have hx : x ∈ LinearMap.ker E := LinearMap.mem_ker.2 (by rw [hE0]; rfl)
      rw [hAx' x hx, Matrix.neg_mulVec, Matrix.one_mulVec]
    have hneg : A = -1 := eq_of_forall_mulVec hall
    have hd : A.det = -1 := by
      rw [hneg, Matrix.det_neg, Matrix.det_one, Fintype.card_fin]
      norm_num
    have h' : (1 : K) = -1 := hdet.symm.trans hd
    exact h2 (by linear_combination h')
  have hne2 : LinearMap.ker E ≠ ⊥ := by
    intro hbot
    have hinj : Function.Injective E := LinearMap.ker_eq_bot.1 hbot
    have hall : ∀ x, A *ᵥ x = (1 : Matrix (Fin 3) (Fin 3) K) *ᵥ x := by
      intro x
      have hxE : E x = x := by
        apply hinj
        exact congrArg (fun F : Module.End K (Fin 3 → K) => F x) hEE.eq
      have hx : x ∈ LinearMap.range E := (LinearMap.IsIdempotentElem.mem_range_iff hEE).2 hxE
      rw [hAx x hx, Matrix.one_mulVec]
    exact hA1 (eq_of_forall_mulVec hall)
  have hp1 : 1 ≤ Module.finrank K (LinearMap.range E) := Submodule.one_le_finrank_iff.2 hne1
  have hp2 : 1 ≤ Module.finrank K (LinearMap.ker E) := Submodule.one_le_finrank_iff.2 hne2
  have hcases :
      (Module.finrank K (LinearMap.range E) = 1 ∧ Module.finrank K (LinearMap.ker E) = 2) ∨
      (Module.finrank K (LinearMap.range E) = 2 ∧ Module.finrank K (LinearMap.ker E) = 1) := by
    omega
  rcases hcases with ⟨h1, h2'⟩ | ⟨h1, h2'⟩
  · exact exists_adapted_basis_of_line (LinearMap.range E) (LinearMap.ker E) hcompl hAx hAx'
      h1 h2'
  · obtain ⟨Q, hQ⟩ := exists_adapted_basis_of_line (B := -A) (LinearMap.ker E)
      (LinearMap.range E) hcompl.symm
      (fun x hx => by rw [Matrix.neg_mulVec, hAx' x hx, neg_neg])
      (fun x hx => by rw [Matrix.neg_mulVec, hAx x hx]) h2' h1
    exfalso
    have h3 : A * (Q : Matrix (Fin 3) (Fin 3) K) = -((Q : Matrix (Fin 3) (Fin 3) K) * D3) := by
      rw [← neg_eq_iff_eq_neg, ← Matrix.neg_mul]
      exact hQ
    have hdQ : ((Q : Matrix (Fin 3) (Fin 3) K)).det ≠ 0 :=
      ((Matrix.isUnit_iff_isUnit_det _).1 Q.isUnit).ne_zero
    have hdD : (D3 : Matrix (Fin 3) (Fin 3) K).det = 1 := by
      simp [D3, Matrix.det_diagonal, Fin.prod_univ_three]
    have hd := congrArg Matrix.det h3
    rw [Matrix.det_mul, Matrix.det_neg, Matrix.det_mul, hdet, hdD, Fintype.card_fin] at hd
    exact h2 (mul_left_cancel₀ hdQ (by linear_combination hd))

end Adapted

end CFSG.QuasithinUnique.Ch1
