module

public import CFSG.LocalAnalysis.GLTheoremA.CatB.TimmU1

public section

namespace CFSG.LocalAnalysis.GLTheoremA.Timm.UnitaryPoint

open Matrix CFSG.Open

variable {w : ℕ}

theorem dot_e0 (x : Fin (w + 2) → F4) : e0 w ⬝ᵥ x = x (Tp w 0) + x (Tp w 1) := by
  unfold dotProduct
  rw [Fin.sum_univ_add, Fin.sum_univ_two]
  simp [e0_val_zero_of_castAdd, e0_natAdd_zero, e0_natAdd_one]

theorem pow_mulVec_of {M : Matrix (Fin (w + 2)) (Fin (w + 2)) F4} {μ : F4}
    (h : M *ᵥ e0 w = μ • e0 w) (k : ℕ) : (M ^ k) *ᵥ e0 w = (μ ^ k) • e0 w := by
  induction k with
  | zero => simp
  | succ k ih =>
    rw [pow_succ', ← Matrix.mulVec_mulVec, ih, Matrix.mulVec_smul, h, smul_smul, pow_succ']
    ring_nf

theorem eq_one_of_sq_eq_one {μ : F4} (h : μ ^ 2 = 1) : μ = 1 := by
  have h' : μ * μ = 1 := by rw [← sq]; exact h
  rcases mul_self_eq_one_iff.mp h' with h1 | h1
  · exact h1
  · rw [h1]
    exact CharTwo.neg_eq (1 : F4)

theorem ne_zero_of_mulVec_e0 {M : Matrix (Fin (w + 2)) (Fin (w + 2)) F4} (hM : IsUnit M.det)
    {μ : F4} (h : M *ᵥ e0 w = μ • e0 w) : μ ≠ 0 := by
  rintro rfl
  have h1 : M *ᵥ e0 w = 0 := by rw [h, zero_smul]
  have h2 : e0 w = 0 := by
    have := congrArg (fun v => (M⁻¹ : Matrix (Fin (w + 2)) (Fin (w + 2)) F4) *ᵥ v) h1
    simp only [Matrix.mulVec_zero] at this
    rw [Matrix.mulVec_mulVec, Matrix.nonsing_inv_mul _ hM, Matrix.one_mulVec] at this
    exact this
  have h3 := congrFun h2 (Tp w 0)
  rw [e0_natAdd_zero] at h3
  exact one_ne_zero h3

theorem unip_cube {A : Matrix (Fin (w + 2)) (Fin (w + 2)) F4} (hU : IsUnitaryMat A)
    (hfix : A *ᵥ e0 w = e0 w) (hρ : rhoM A = 1) :
    (A - 1) * (A - 1) * (A - 1) = 0 := by
  have hfix1 : A *ᵥ e0 w = (1 : F4) • e0 w := by rw [one_smul]; exact hfix
  have hrow : e0 w ᵥ* A = e0 w := by
    rw [row_act hU hfix1, one_smul]
  have hcol : ∀ i : Fin w, A (Wc w i) (Tp w 0) = A (Wc w i) (Tp w 1) :=
    fun i => col_eq_of_mulVec hfix1 i
  set N : Matrix (Fin (w + 2)) (Fin (w + 2)) F4 := A - 1 with hN
  have hNe : ∀ v, N *ᵥ v = A *ᵥ v - v := by
    intro v
    rw [hN, Matrix.sub_mulVec, Matrix.one_mulVec]
  have hN0 : N *ᵥ e0 w = 0 := by
    rw [hNe, hfix, sub_self]
  have ha : ∀ v, e0 w ⬝ᵥ (N *ᵥ v) = 0 := by
    intro v
    rw [hNe, dotProduct_sub, Matrix.dotProduct_mulVec, hrow, sub_eq_zero]
  have hb : ∀ x : Fin (w + 2) → F4, e0 w ⬝ᵥ x = 0 → ∀ i : Fin w, (N *ᵥ x) (Wc w i) = 0 := by
    intro x hx i
    have hW : ∑ j : Fin w, A (Wc w i) (Wc w j) * x (Wc w j) = x (Wc w i) := by
      have hr : ∀ j : Fin w, A (Wc w i) (Wc w j) = if i = j then 1 else 0 := by
        intro j
        have := congrFun (congrFun hρ i) j
        simp only [rhoM, Matrix.of_apply, Matrix.one_apply] at this
        rw [this]
      simp only [hr, ite_mul, one_mul, zero_mul, Finset.sum_ite_eq, Finset.mem_univ, if_true]
    have hx' : x (Tp w 0) + x (Tp w 1) = 0 := by
      have := dot_e0 x
      rw [hx] at this
      exact this.symm
    have htop : A (Wc w i) (Tp w 0) * x (Tp w 0) + A (Wc w i) (Tp w 1) * x (Tp w 1) = 0 := by
      rw [hcol i, ← mul_add, hx', mul_zero]
    rw [hNe, Pi.sub_apply]
    show (∑ k, A (Wc w i) k * x k) - x (Wc w i) = 0
    rw [Fin.sum_univ_add, Fin.sum_univ_two, hW, htop]
    ring
  have hc : ∀ x : Fin (w + 2) → F4, e0 w ⬝ᵥ x = 0 → N *ᵥ x = (N *ᵥ x) (Tp w 0) • e0 w := by
    intro x hx
    funext k
    induction k using Fin.addCases with
    | left i => simp [e0_val_zero_of_castAdd, hb x hx i]
    | right t =>
      fin_cases t
      · simp [e0_natAdd_zero]
      · have h2 : (N *ᵥ x) (Tp w 0) + (N *ᵥ x) (Tp w 1) = 0 := by
          rw [← dot_e0]; exact ha x
        have h3 := char2_eq_of_add_eq_zero h2
        simp [e0_natAdd_one, h3]
  have hcube : ∀ v, N *ᵥ (N *ᵥ (N *ᵥ v)) = 0 := by
    intro v
    rw [hc (N *ᵥ v) (ha v), Matrix.mulVec_smul, hN0, smul_zero]
  apply Matrix.ext
  intro i j
  have hM : (N * N * N) *ᵥ (Pi.single j 1) = 0 := by
    rw [← Matrix.mulVec_mulVec, ← Matrix.mulVec_mulVec]
    exact hcube _
  have h := congrFun hM i
  rw [Matrix.mulVec_single_one] at h
  simpa using h

theorem pow_four_of_unip {A : Matrix (Fin (w + 2)) (Fin (w + 2)) F4} (hU : IsUnitaryMat A)
    (hfix : A *ᵥ e0 w = e0 w) (hρ : rhoM A = 1) : A ^ 4 = 1 := by
  have hc := unip_cube hU hfix hρ
  obtain ⟨N, hN⟩ : ∃ N : Matrix (Fin (w + 2)) (Fin (w + 2)) F4, N = A - 1 := ⟨_, rfl⟩
  rw [← hN] at hc
  have hA : A = 1 + N := by rw [hN, add_sub_cancel]
  have hNN : N + N = 0 := by
    ext i j
    simp [Matrix.add_apply, CharTwo.add_self_eq_zero]
  have hQ : N * N + N * N = 0 := by
    ext i j
    simp [Matrix.add_apply, CharTwo.add_self_eq_zero]
  have hQQ : (N * N) * (N * N) = 0 := by
    calc (N * N) * (N * N) = (N * N * N) * N := by simp only [Matrix.mul_assoc]
      _ = 0 := by rw [hc, Matrix.zero_mul]
  have hA2 : A * A = 1 + N * N := by
    rw [hA]
    calc (1 + N) * (1 + N) = 1 + (N + N) + N * N := by noncomm_ring
      _ = 1 + N * N := by rw [hNN, add_zero]
  have hA4 : A ^ 4 = (A * A) * (A * A) := by
    rw [show (4 : ℕ) = 2 + 2 from rfl, pow_add, sq]
  rw [hA4, hA2]
  calc (1 + N * N) * (1 + N * N) = 1 + (N * N + N * N) + (N * N) * (N * N) := by noncomm_ring
    _ = 1 := by rw [hQ, hQQ, add_zero, add_zero]

theorem eq_one_of_pow_five {x : GL (Fin (w + 2)) F4} (hw : 0 < w) (hx : x ∈ stabSU w)
    {c : F4} (hc0 : c ≠ 0) (hc : rhoM (x : Matrix (Fin (w + 2)) (Fin (w + 2)) F4) = c • 1)
    (h5 : x ^ 5 = 1) : x = 1 := by
  obtain ⟨hdet, hU, μ, hμ⟩ := (mem_stabSU_iff x).1 hx
  have hM5 : (x : Matrix (Fin (w + 2)) (Fin (w + 2)) F4) ^ 5 = 1 := by
    rw [← Units.val_pow_eq_pow_val, h5, Units.val_one]
  have hμ5 : μ ^ 5 = 1 := by
    have h := pow_mulVec_of hμ 5
    rw [hM5, Matrix.one_mulVec] at h
    have h' := congrFun h (Tp w 0)
    simpa [e0_natAdd_zero] using h'.symm
  have hμ0 : μ ≠ 0 := ne_zero_of_mulVec_e0 (by rw [hdet]; exact isUnit_one) hμ
  have hμ3 := pow_three_of_ne_zero hμ0
  have hμ2 : μ ^ 2 = 1 := by
    have : μ ^ 2 = μ ^ 5 := by rw [show μ ^ 5 = μ ^ 2 * μ ^ 3 by ring, hμ3, mul_one]
    rw [this, hμ5]
  have hμ1 : μ = 1 := eq_one_of_sq_eq_one hμ2
  set X : ↥(stabSU w) := ⟨x, hx⟩ with hX
  have hX5 : X ^ 5 = 1 := Subtype.ext h5
  have hr5 : (rhoHom X) ^ 5 = 1 := by rw [← map_pow, hX5, map_one]
  have hrM5 : (rhoM (x : Matrix (Fin (w + 2)) (Fin (w + 2)) F4)) ^ 5 = 1 := by
    have h := congrArg (fun g : ↥(unitSub w) => ((g : GL (Fin w) F4) : Matrix (Fin w) (Fin w) F4))
      hr5
    simp only [rhoHom_val, rhoGL_val, Subgroup.coe_pow, Units.val_pow_eq_pow_val,
      Subgroup.coe_one, Units.val_one] at h
    exact h
  rw [hc, smul_pow, one_pow] at hrM5
  have hc5 : c ^ 5 = 1 := by
    have h := congrFun (congrFun hrM5 ⟨0, hw⟩) ⟨0, hw⟩
    simpa using h
  have hc3 := pow_three_of_ne_zero hc0
  have hc2 : c ^ 2 = 1 := by
    have : c ^ 2 = c ^ 5 := by rw [show c ^ 5 = c ^ 2 * c ^ 3 by ring, hc3, mul_one]
    rw [this, hc5]
  have hc1 : c = 1 := eq_one_of_sq_eq_one hc2
  have hρ1 : rhoM (x : Matrix (Fin (w + 2)) (Fin (w + 2)) F4) = 1 := by
    rw [hc, hc1, one_smul]
  have hfix : (x : Matrix (Fin (w + 2)) (Fin (w + 2)) F4) *ᵥ e0 w = e0 w := by
    rw [hμ, hμ1, one_smul]
  have h4 : x ^ 4 = 1 := by
    apply Units.ext
    rw [Units.val_pow_eq_pow_val, Units.val_one]
    exact pow_four_of_unip hU hfix hρ1
  calc x = x ^ 4 * x := by rw [h4, one_mul]
    _ = x ^ 5 := (pow_succ x 4).symm
    _ = 1 := h5

end CFSG.LocalAnalysis.GLTheoremA.Timm.UnitaryPoint

end
