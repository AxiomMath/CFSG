module

public import CFSG.LinearAlgebra.LinearGroups.UnitaryFourOrder
public import CFSG.Assembly.LowTwoRankDefs
public import CFSG.ClassicalGroups.UnitaryFlag.GramForm

public section

namespace CFSG.GH74.Generic.S45.Uni

open Matrix CFSG.LinearGroups CFSG.LocalAnalysis.ComponentInitial CFSG.ClassicalGroups.UnitaryFlag

variable {p f : ℕ} {K : Type} [Field K] (h : UnitaryFieldData p f K) {n : ℕ}

theorem hh_comm (x y : Fin n → K) :
    stdHermForm h n y x = h.bar (stdHermForm h n x y) :=
  ((stdHermForm_isSymm h n).eq x y).symm

theorem hh_mulVec_left (M : Matrix (Fin n) (Fin n) K) (x y : Fin n → K) :
    stdHermForm h n (M *ᵥ x) y = stdHermForm h n x ((M.map h.bar)ᵀ *ᵥ y) := by
  simp only [stdHermForm_apply, mulVec, dotProduct, map_sum, map_mul, Finset.sum_mul,
    Finset.mul_sum, transpose_apply, map_apply]
  rw [Finset.sum_comm]
  refine Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun j _ => ?_
  ring

theorem hh_single_right (x : Fin n → K) (j : Fin n) :
    stdHermForm h n x (Pi.single j 1) = h.bar (x j) := by
  rw [stdHermForm_apply, Finset.sum_eq_single j (fun i _ hi => by simp [hi]) (by simp)]
  simp

theorem eq_zero_of_hh_zero {v : Fin n → K} (hv : ∀ z, stdHermForm h n z v = 0) : v = 0 := by
  funext j
  have := hv (Pi.single j 1)
  rwa [stdHermForm_single] at this

theorem exists_norm_eq {a : K} (ha : h.bar a = a) (ha0 : a ≠ 0) : ∃ s : K, h.bar s * s = a := by
  obtain ⟨u, hu⟩ := (h.card_ker_normUnits_and_surjective.2)
    (Units.mk0 (⟨a, ha⟩ : h.fixedField) (fun h0 => ha0 (congrArg Subtype.val h0)))
  have h1 : h.norm (u : K) = a := by
    have := congrArg (fun w : h.fixedFieldˣ => ((w : h.fixedField) : K)) hu
    simpa using this
  exact ⟨u, by rw [← h1, UnitaryFieldData.norm, mul_comm]⟩

theorem exists_bar_neg : ∃ θ : K, θ ≠ 0 ∧ h.bar θ = -θ := by
  obtain ⟨c, hc⟩ := h.exists_bar_ne
  refine ⟨c - h.bar c, sub_ne_zero.2 (Ne.symm hc), ?_⟩
  rw [map_sub, h.bar_bar]
  ring

theorem eq_zero_of_hh_self_zero (h2 : (2 : K) ≠ 0) {E : Matrix (Fin n) (Fin n) K}
    (hE : ∀ x y, stdHermForm h n (E *ᵥ x) y = stdHermForm h n x (E *ᵥ y))
    (h0 : ∀ z, stdHermForm h n z (E *ᵥ z) = 0) : E = 0 := by
  obtain ⟨θ, hθ0, hθ⟩ := exists_bar_neg h (K := K)
  have key : ∀ z w, stdHermForm h n z (E *ᵥ w) + h.bar (stdHermForm h n z (E *ᵥ w)) = 0 := by
    intro z w
    have h1 := h0 (z + w)
    simp only [mulVec_add, map_add, LinearMap.add_apply] at h1
    rw [h0 z, h0 w] at h1
    have h2' : stdHermForm h n w (E *ᵥ z) = h.bar (stdHermForm h n z (E *ᵥ w)) := by
      rw [← hE w z]
      exact hh_comm h z (E *ᵥ w)
    rw [h2'] at h1
    linear_combination h1
  have hz : ∀ z w, stdHermForm h n z (E *ᵥ w) = 0 := by
    intro z w
    have e1 := key z w
    have e2 := key (h.bar θ • z) w
    rw [map_smulₛₗ, LinearMap.smul_apply, smul_eq_mul, map_mul, h.bar_bar, hθ] at e2
    set u := stdHermForm h n z (E *ᵥ w) with hu
    have e3 : θ * (u - h.bar u) = 0 := by linear_combination e2
    have e4 : u - h.bar u = 0 := (mul_eq_zero.1 e3).resolve_left hθ0
    have e5 : 2 * u = 0 := by linear_combination e1 + e4
    exact (mul_eq_zero.1 e5).resolve_left h2
  have hw : ∀ w, E *ᵥ w = 0 := fun w => eq_zero_of_hh_zero h fun z => hz z w
  ext i j
  have := congrFun (hw (Pi.single j 1)) i
  simpa [mulVec_single] using this

theorem matrix_ext_mulVec {M N : Matrix (Fin n) (Fin n) K} (hMN : ∀ z, M *ᵥ z = N *ᵥ z) : M = N := by
  ext i j
  have := congrFun (hMN (Pi.single j 1)) i
  simpa [mulVec_single] using this

theorem exists_unit_vec (h2 : (2 : K) ≠ 0) {E : Matrix (Fin n) (Fin n) K}
    (hE : ∀ x y, stdHermForm h n (E *ᵥ x) y = stdHermForm h n x (E *ᵥ y))
    (hE2 : E * E = E) (hE0 : E ≠ 0) :
    ∃ x, E *ᵥ x = x ∧ stdHermForm h n x x = 1 := by
  have : ∃ z, stdHermForm h n z (E *ᵥ z) ≠ 0 := by
    by_contra hcon
    push Not at hcon
    exact hE0 (eq_zero_of_hh_self_zero h h2 hE hcon)
  obtain ⟨z, hz⟩ := this
  set a := stdHermForm h n z (E *ᵥ z) with ha
  have hEE : ∀ v, E *ᵥ (E *ᵥ v) = E *ᵥ v := fun v => by rw [mulVec_mulVec, hE2]
  have hxx : stdHermForm h n (E *ᵥ z) (E *ᵥ z) = a := by
    rw [hE z (E *ᵥ z), hEE z]
  have hba : h.bar a = a := by
    rw [ha, ← hh_comm h z (E *ᵥ z), hE z z]
  obtain ⟨s, hs⟩ := exists_norm_eq h (a := a⁻¹) (by rw [map_inv₀, hba]) (inv_ne_zero hz)
  refine ⟨s • (E *ᵥ z), ?_, ?_⟩
  · rw [mulVec_smul, hEE]
  · simp only [map_smulₛₗ, LinearMap.smul_apply, smul_eq_mul, RingHom.id_apply]
    rw [hxx]
    calc s * (h.bar s * a) = (h.bar s * s) * a := by ring
      _ = 1 := by rw [hs, inv_mul_cancel₀ hz]

@[expose] noncomputable def projVec (x : Fin n → K) : Matrix (Fin n) (Fin n) K :=
  Matrix.of fun i j => x i * h.bar (x j)

theorem projVec_mulVec (x z : Fin n → K) :
    projVec h x *ᵥ z = stdHermForm h n x z • x := by
  funext i
  simp only [projVec, mulVec, dotProduct, of_apply, Pi.smul_apply, smul_eq_mul, stdHermForm_apply]
  rw [Finset.sum_mul]
  exact Finset.sum_congr rfl fun j _ => by ring



theorem sub_mulVec' (A B : Matrix (Fin n) (Fin n) K) (z : Fin n → K) :
    (A - B) *ᵥ z = A *ᵥ z - B *ᵥ z := sub_mulVec A B z

theorem pair_or_small (h2 : (2 : K) ≠ 0) {E : Matrix (Fin n) (Fin n) K}
    (hE : ∀ x y, stdHermForm h n (E *ᵥ x) y = stdHermForm h n x (E *ᵥ y))
    (hE2 : E * E = E) :
    (∃ x y, E *ᵥ x = x ∧ E *ᵥ y = y ∧ stdHermForm h n x x = 1 ∧ stdHermForm h n y y = 1 ∧
        stdHermForm h n x y = 0) ∨ ∃ x₀, ∀ z, E *ᵥ z = stdHermForm h n x₀ z • x₀ := by
  by_cases hE0 : E = 0
  · right
    exact ⟨0, fun z => by simp [hE0]⟩
  obtain ⟨x, hx, hxx⟩ := exists_unit_vec h h2 hE hE2 hE0
  set E' : Matrix (Fin n) (Fin n) K := E - projVec h x with hE'
  have hE'z : ∀ z, E' *ᵥ z = E *ᵥ z - stdHermForm h n x z • x := by
    intro z
    rw [hE', sub_mulVec, projVec_mulVec]
  have hEx : ∀ z, stdHermForm h n x (E *ᵥ z) = stdHermForm h n x z := by
    intro z
    rw [← hE x z, hx]
  have hE'x : ∀ z, stdHermForm h n x (E' *ᵥ z) = 0 := by
    intro z
    rw [hE'z, map_sub, map_smul, hEx, smul_eq_mul, hxx, mul_one, sub_self]
  have hE'adj : ∀ z w, stdHermForm h n (E' *ᵥ z) w = stdHermForm h n z (E' *ᵥ w) := by
    intro z w
    rw [hE'z, hE'z]
    simp only [map_sub, LinearMap.sub_apply, map_smulₛₗ, LinearMap.smul_apply, smul_eq_mul,
      RingHom.id_apply]
    rw [hE z w, hh_comm h x z]
    ring
  have hE'2 : E' * E' = E' := by
    apply matrix_ext_mulVec
    intro z
    rw [← mulVec_mulVec, hE'z (E' *ᵥ z), hE'x, zero_smul, sub_zero, hE'z z, mulVec_sub,
      mulVec_smul, hx, mulVec_mulVec, hE2]
  by_cases hE'0 : E' = 0
  · right
    refine ⟨x, fun z => ?_⟩
    have := hE'z z
    rw [hE'0, zero_mulVec] at this
    exact (sub_eq_zero.1 this.symm)
  · left
    obtain ⟨y, hy, hyy⟩ := exists_unit_vec h h2 hE'adj hE'2 hE'0
    have hxy : stdHermForm h n x y = 0 := by
      rw [← hy]
      exact hE'x y
    refine ⟨x, y, hx, ?_, hxx, hyy, hxy⟩
    have := hE'z y
    rw [hy, hxy, zero_smul, sub_zero] at this
    exact this.symm

theorem exists_orth_pair (hn : 3 ≤ n) (x y : Fin n → K) :
    ∃ w : Fin n → K, w ≠ 0 ∧ stdHermForm h n x w = 0 ∧ stdHermForm h n y w = 0 := by
  let F : (Fin n → K) →ₗ[K] (Fin 2 → K) := LinearMap.pi ![stdHermForm h n x, stdHermForm h n y]
  have hlt : Module.finrank K (Fin 2 → K) < Module.finrank K (Fin n → K) := by
    simp only [Module.finrank_fin_fun]
    omega
  have hker := LinearMap.ker_ne_bot_of_finrank_lt (f := F) hlt
  obtain ⟨w, hw, hw0⟩ := (Submodule.ne_bot_iff _).1 hker
  refine ⟨w, hw0, ?_, ?_⟩
  · have := congrFun (LinearMap.mem_ker.1 hw) 0
    simpa [F] using this
  · have := congrFun (LinearMap.mem_ker.1 hw) 1
    simpa [F] using this



@[expose] noncomputable def pairRotU (x y : Fin n → K) : Matrix (Fin n) (Fin 2) K :=
  Matrix.of fun i j => ![y i - x i, -(x i + y i)] j

@[expose] noncomputable def pairRotV (x y : Fin n → K) : Matrix (Fin 2) (Fin n) K :=
  Matrix.of fun j k => ![h.bar (x k), h.bar (y k)] j

@[expose] noncomputable def pairRot (x y : Fin n → K) : Matrix (Fin n) (Fin n) K :=
  1 + pairRotU x y * pairRotV h x y

theorem pairRotV_mulVec (x y z : Fin n → K) :
    pairRotV h x y *ᵥ z = ![stdHermForm h n x z, stdHermForm h n y z] := by
  funext j
  fin_cases j <;> simp [pairRotV, mulVec, dotProduct, stdHermForm_apply]

theorem pairRotU_mulVec (x y : Fin n → K) (w : Fin 2 → K) :
    pairRotU x y *ᵥ w = w 0 • (y - x) + w 1 • (-(x + y)) := by
  funext i
  simp [pairRotU, mulVec, dotProduct, Fin.sum_univ_two]
  ring

theorem pairRot_mulVec (x y z : Fin n → K) :
    pairRot h x y *ᵥ z = z + stdHermForm h n x z • (y - x) - stdHermForm h n y z • (x + y) := by
  rw [pairRot, add_mulVec, one_mulVec, ← mulVec_mulVec, pairRotV_mulVec, pairRotU_mulVec]
  simp only [Matrix.cons_val_zero, Matrix.cons_val_one, smul_neg]
  abel



section Rot

variable {x y : Fin n → K} (hx : stdHermForm h n x x = 1) (hy : stdHermForm h n y y = 1)
  (hxy : stdHermForm h n x y = 0)

include hx hy hxy

theorem pairRot_isometry (z w : Fin n → K) :
    stdHermForm h n (pairRot h x y *ᵥ z) (pairRot h x y *ᵥ w) = stdHermForm h n z w := by
  have hyx : stdHermForm h n y x = 0 := by rw [hh_comm h x y, hxy, map_zero]
  rw [pairRot_mulVec, pairRot_mulVec]
  simp only [map_add, map_sub, map_smulₛₗ, LinearMap.add_apply, LinearMap.sub_apply,
    LinearMap.smul_apply, smul_eq_mul, RingHom.id_apply, hx, hy, hxy, hyx]
  rw [hh_comm h x z, hh_comm h y z]
  ring

theorem pairRot_sq_apply (w : Fin n → K) :
    pairRot h x y *ᵥ (pairRot h x y *ᵥ w) =
      w - (2 * stdHermForm h n x w) • x - (2 * stdHermForm h n y w) • y := by
  have hyx : stdHermForm h n y x = 0 := by rw [hh_comm h x y, hxy, map_zero]
  rw [pairRot_mulVec, pairRot_mulVec]
  simp only [map_add, map_sub, map_smul, smul_eq_mul, hx, hy, hxy, hyx]
  module

theorem pairRot_pow_four : (pairRot h x y * pairRot h x y) * (pairRot h x y * pairRot h x y) = 1 := by
  have hyx : stdHermForm h n y x = 0 := by rw [hh_comm h x y, hxy, map_zero]
  apply matrix_ext_mulVec
  intro z
  have e1 := pairRot_sq_apply h hx hy hxy z
  have e2 := pairRot_sq_apply h hx hy hxy (pairRot h x y *ᵥ (pairRot h x y *ᵥ z))
  simp only [← mulVec_mulVec, one_mulVec] at e1 e2 ⊢
  rw [e2, e1]
  simp only [map_sub, map_smul, smul_eq_mul, hx, hy, hxy, hyx]
  module

theorem pairRot_det : (pairRot h x y).det = 1 := by
  have hyx : stdHermForm h n y x = 0 := by rw [hh_comm h x y, hxy, map_zero]
  rw [pairRot, det_one_add_mul_comm]
  have e00 : ∑ k, h.bar (x k) * (y k - x k) = -1 := by
    have : ∑ k, h.bar (x k) * (y k - x k) = stdHermForm h n x y - stdHermForm h n x x := by
      simp only [stdHermForm_apply, mul_sub, Finset.sum_sub_distrib]
    rw [this, hxy, hx]
    ring
  have e01 : ∑ k, h.bar (x k) * (-(x k + y k)) = -1 := by
    have : ∑ k, h.bar (x k) * (-(x k + y k)) = -(stdHermForm h n x x + stdHermForm h n x y) := by
      simp only [stdHermForm_apply, mul_neg, mul_add, Finset.sum_neg_distrib,
        Finset.sum_add_distrib]
    rw [this, hxy, hx]
    ring
  have e10 : ∑ k, h.bar (y k) * (y k - x k) = 1 := by
    have : ∑ k, h.bar (y k) * (y k - x k) = stdHermForm h n y y - stdHermForm h n y x := by
      simp only [stdHermForm_apply, mul_sub, Finset.sum_sub_distrib]
    rw [this, hyx, hy]
    ring
  have e11 : ∑ k, h.bar (y k) * (-(x k + y k)) = -1 := by
    have : ∑ k, h.bar (y k) * (-(x k + y k)) = -(stdHermForm h n y x + stdHermForm h n y y) := by
      simp only [stdHermForm_apply, mul_neg, mul_add, Finset.sum_neg_distrib,
        Finset.sum_add_distrib]
    rw [this, hyx, hy]
    ring
  have hVU : 1 + pairRotV h x y * pairRotU x y = !![0, -1; 1, 0] := by
    ext i j
    fin_cases i <;> fin_cases j
    · simp [mul_apply, pairRotV, pairRotU, e00]
    · simpa [mul_apply, pairRotV, pairRotU] using e01
    · simp [mul_apply, pairRotV, pairRotU, e10]
    · have := e11
      simp [mul_apply, pairRotV, pairRotU] at this ⊢
      linear_combination this
  rw [hVU, det_fin_two_of]
  ring

omit hy in
theorem pairRot_apply_x : pairRot h x y *ᵥ x = y := by
  have hyx : stdHermForm h n y x = 0 := by rw [hh_comm h x y, hxy, map_zero]
  rw [pairRot_mulVec, hx, hyx]
  module

omit hx in
theorem pairRot_apply_y : pairRot h x y *ᵥ y = -x := by
  rw [pairRot_mulVec, hy, hxy]
  module

omit hx hy hxy in
theorem pairRot_apply_orth {w : Fin n → K} (hxw : stdHermForm h n x w = 0)
    (hyw : stdHermForm h n y w = 0) : pairRot h x y *ᵥ w = w := by
  rw [pairRot_mulVec, hxw, hyw]
  module

theorem pairRot_not_scalar (h2 : (2 : K) ≠ 0) (hn : 3 ≤ n) (l : K) :
    pairRot h x y * pairRot h x y ≠ l • (1 : Matrix (Fin n) (Fin n) K) := by
  intro hl
  have hall : ∀ v, pairRot h x y *ᵥ (pairRot h x y *ᵥ v) = l • v := by
    intro v
    rw [mulVec_mulVec, hl, smul_mulVec, one_mulVec]
  obtain ⟨w, hw0, hxw, hyw⟩ := exists_orth_pair h hn x y
  have h1 := hall w
  rw [pairRot_apply_orth h hxw hyw, pairRot_apply_orth h hxw hyw] at h1
  have hl1 : l = 1 := by
    have : (1 - l) • w = 0 := by rw [sub_smul, one_smul, ← h1, sub_self]
    have := (smul_eq_zero.1 this).resolve_right hw0
    linear_combination -this
  have h2' := hall x
  rw [pairRot_apply_x h hx hxy, pairRot_apply_y h hy hxy] at h2'
  have hx0 : x ≠ 0 := by
    rintro rfl
    simp at hx
  have hl2 : l = -1 := by
    have : (l + 1) • x = 0 := by rw [add_smul, one_smul, ← h2', neg_add_cancel]
    have := (smul_eq_zero.1 this).resolve_right hx0
    linear_combination this
  rw [hl1] at hl2
  exact h2 (by linear_combination hl2)

omit hx hy hxy in
theorem pairRot_comm {T : Matrix (Fin n) (Fin n) K} {ε : K} (hε : h.bar ε = ε)
    (hTa : ∀ z w, stdHermForm h n (T *ᵥ z) w = stdHermForm h n z (T *ᵥ w))
    (hTx : T *ᵥ x = ε • x) (hTy : T *ᵥ y = ε • y) :
    pairRot h x y * T = T * pairRot h x y := by
  apply matrix_ext_mulVec
  intro z
  have hxz : stdHermForm h n x (T *ᵥ z) = ε * stdHermForm h n x z := by
    rw [← hTa x z, hTx, map_smulₛₗ, hε, LinearMap.smul_apply, smul_eq_mul]
  have hyz : stdHermForm h n y (T *ᵥ z) = ε * stdHermForm h n y z := by
    rw [← hTa y z, hTy, map_smulₛₗ, hε, LinearMap.smul_apply, smul_eq_mul]
  rw [← mulVec_mulVec, ← mulVec_mulVec, pairRot_mulVec, pairRot_mulVec, hxz, hyz]
  simp only [mulVec_sub, mulVec_add, mulVec_smul, hTx, hTy]
  module

end Rot

theorem unitary_of_isometry {M : Matrix (Fin n) (Fin n) K}
    (hM : ∀ z w, stdHermForm h n (M *ᵥ z) (M *ᵥ w) = stdHermForm h n z w) :
    (M.map h.bar)ᵀ * M = 1 := by
  apply matrix_ext_mulVec
  intro w
  rw [← mulVec_mulVec, one_mulVec]
  have : ∀ z, stdHermForm h n z ((M.map h.bar)ᵀ *ᵥ (M *ᵥ w) - w) = 0 := by
    intro z
    rw [map_sub, ← hh_mulVec_left, hM, sub_self]
  exact sub_eq_zero.1 (eq_zero_of_hh_zero h this)

theorem exists_rot_commuting (h2 : (2 : K) ≠ 0) (hn : 3 ≤ n) {x y : Fin n → K}
    (hx : stdHermForm h n x x = 1) (hy : stdHermForm h n y y = 1)
    (hxy : stdHermForm h n x y = 0) {T : Matrix (Fin n) (Fin n) K} {ε : K}
    (hε : h.bar ε = ε)
    (hTa : ∀ z w, stdHermForm h n (T *ᵥ z) w = stdHermForm h n z (T *ᵥ w))
    (hTx : T *ᵥ x = ε • x) (hTy : T *ᵥ y = ε • y) :
    ∃ c : Matrix (Fin n) (Fin n) K, (c.map h.bar)ᵀ * c = 1 ∧ c.det = 1 ∧
      (∀ l : K, c * c ≠ l • 1) ∧ c * c * (c * c) = 1 ∧ c * T = T * c :=
  ⟨pairRot h x y, unitary_of_isometry h (pairRot_isometry h hx hy hxy), pairRot_det h hx hy hxy,
    pairRot_not_scalar h hx hy hxy h2 hn, pairRot_pow_four h hx hy hxy,
    pairRot_comm h hε hTa hTx hTy⟩







@[expose] noncomputable def eigProj (T : Matrix (Fin n) (Fin n) K) (ε : K) : Matrix (Fin n) (Fin n) K :=
  (2 : K)⁻¹ • (1 + ε • T)

theorem eigProj_mulVec (T : Matrix (Fin n) (Fin n) K) (ε : K) (z : Fin n → K) :
    eigProj T ε *ᵥ z = (2 : K)⁻¹ • (z + ε • (T *ᵥ z)) := by
  rw [eigProj, smul_mulVec, add_mulVec, one_mulVec, smul_mulVec]

theorem eigProj_selfAdj {T : Matrix (Fin n) (Fin n) K} {ε : K} (hε : h.bar ε = ε)
    (hTa : ∀ z w, stdHermForm h n (T *ᵥ z) w = stdHermForm h n z (T *ᵥ w)) (z w : Fin n → K) :
    stdHermForm h n (eigProj T ε *ᵥ z) w = stdHermForm h n z (eigProj T ε *ᵥ w) := by
  have h2b : h.bar ((2 : K)⁻¹) = (2 : K)⁻¹ := by rw [map_inv₀, map_ofNat]
  rw [eigProj_mulVec, eigProj_mulVec]
  simp only [map_smulₛₗ, map_add, LinearMap.smul_apply, LinearMap.add_apply, smul_eq_mul, hε, h2b,
    hTa, RingHom.id_apply]

theorem eigProj_idem (h2 : (2 : K) ≠ 0) {T : Matrix (Fin n) (Fin n) K} {ε : K}
    (hεε : ε * ε = 1) (hT2 : T * T = 1) : eigProj T ε * eigProj T ε = eigProj T ε := by
  apply matrix_ext_mulVec
  intro z
  have hTT : T *ᵥ (T *ᵥ z) = z := by rw [mulVec_mulVec, hT2, one_mulVec]
  have hε2 : ε • ε • z = z := by rw [smul_smul, hεε, one_smul]
  rw [← mulVec_mulVec]
  simp only [eigProj_mulVec, mulVec_smul, mulVec_add, hTT]
  have hinner : (2 : K)⁻¹ • (z + ε • T *ᵥ z) + ε • (2 : K)⁻¹ • (T *ᵥ z + ε • z) =
      z + ε • T *ᵥ z := by
    have e1 : ε • (2 : K)⁻¹ • (T *ᵥ z + ε • z) = (2 : K)⁻¹ • (ε • T *ᵥ z + z) := by
      rw [smul_comm ε (2 : K)⁻¹, smul_add, hε2]
    rw [e1, ← smul_add]
    have h22 : (z + ε • T *ᵥ z) + (ε • T *ᵥ z + z) = (2 : K) • (z + ε • T *ᵥ z) := by module
    rw [h22, smul_smul, inv_mul_cancel₀ h2, one_smul]
  rw [hinner]

theorem eig_of_fixed (h2 : (2 : K) ≠ 0) {T : Matrix (Fin n) (Fin n) K} {ε : K}
    (hεε : ε * ε = 1) {x : Fin n → K} (hx : eigProj T ε *ᵥ x = x) : T *ᵥ x = ε • x := by
  rw [eigProj_mulVec] at hx
  have h1 : x + ε • T *ᵥ x = (2 : K) • x := by
    have := congrArg (fun v => (2 : K) • v) hx
    simp only [smul_smul, mul_inv_cancel₀ h2, one_smul] at this
    exact this
  have h3 : ε • T *ᵥ x = x := by
    have : ε • T *ᵥ x = (2 : K) • x - x := by rw [← h1]; abel
    rw [this]
    module
  calc T *ᵥ x = ε • ε • T *ᵥ x := by rw [smul_smul, hεε, one_smul]
    _ = ε • x := by rw [h3]

theorem exists_eigenpair (h2 : (2 : K) ≠ 0) (hn : 3 ≤ n) {T : Matrix (Fin n) (Fin n) K}
    (hTa : ∀ z w, stdHermForm h n (T *ᵥ z) w = stdHermForm h n z (T *ᵥ w)) (hT2 : T * T = 1) :
    ∃ (x y : Fin n → K) (ε : K), h.bar ε = ε ∧ T *ᵥ x = ε • x ∧ T *ᵥ y = ε • y ∧
      stdHermForm h n x x = 1 ∧ stdHermForm h n y y = 1 ∧ stdHermForm h n x y = 0 := by
  have hb1 : h.bar (1 : K) = 1 := map_one _
  have hbm1 : h.bar (-1 : K) = -1 := by rw [map_neg, map_one]
  rcases pair_or_small h h2 (eigProj_selfAdj h hb1 hTa)
      (eigProj_idem h2 (by norm_num : (1 : K) * 1 = 1) hT2) with
    ⟨x, y, hx, hy, hxx, hyy, hxy⟩ | ⟨xp, hxp⟩
  · exact ⟨x, y, 1, hb1, eig_of_fixed h2 (by norm_num) hx, eig_of_fixed h2 (by norm_num) hy,
      hxx, hyy, hxy⟩
  rcases pair_or_small h h2 (eigProj_selfAdj h hbm1 hTa)
      (eigProj_idem h2 (by norm_num : (-1 : K) * -1 = 1) hT2) with
    ⟨x, y, hx, hy, hxx, hyy, hxy⟩ | ⟨xm, hxm⟩
  · exact ⟨x, y, -1, hbm1, eig_of_fixed h2 (by norm_num) hx, eig_of_fixed h2 (by norm_num) hy,
      hxx, hyy, hxy⟩
  exfalso
  obtain ⟨w, hw0, hw1, hw2⟩ := exists_orth_pair h hn xp xm
  have e1 := hxp w
  have e2 := hxm w
  rw [hw1, zero_smul, eigProj_mulVec] at e1
  rw [hw2, zero_smul, eigProj_mulVec] at e2
  have hw : w = (2 : K)⁻¹ • (w + (1 : K) • T *ᵥ w) + (2 : K)⁻¹ • (w + (-1 : K) • T *ᵥ w) := by
    have e : (w + (1 : K) • T *ᵥ w) + (w + (-1 : K) • T *ᵥ w) = (2 : K) • w := by module
    rw [← smul_add, e, smul_smul, inv_mul_cancel₀ h2, one_smul]
  rw [e1, e2, add_zero] at hw
  exact hw0 hw


section Scalar

theorem mulVec_single_apply' (M : Matrix (Fin n) (Fin n) K) (i j : Fin n) :
    (M *ᵥ (Pi.single j 1 : Fin n → K)) i = M i j := by
  simp [mulVec, dotProduct, Pi.single_apply]

theorem eq_smul_one_of_comm_rot (h2 : (2 : K) ≠ 0) (hn : 3 ≤ n) {M : Matrix (Fin n) (Fin n) K}
    (hM : ∀ i j : Fin n, i ≠ j → M * pairRot h (Pi.single i 1) (Pi.single j 1) =
      pairRot h (Pi.single i 1) (Pi.single j 1) * M) : ∃ c : K, M = c • 1 := by
  have hnorm : ∀ i : Fin n, stdHermForm h n (Pi.single i 1) (Pi.single i 1) = 1 := by
    intro i
    rw [stdHermForm_single]
    simp
  have horth : ∀ i j : Fin n, i ≠ j → stdHermForm h n (Pi.single i 1) (Pi.single j 1) = 0 := by
    intro i j hij
    rw [stdHermForm_single]
    simp [hij]
  have hcomm : ∀ i j : Fin n, i ≠ j → ∀ w, M *ᵥ (pairRot h (Pi.single i 1) (Pi.single j 1) *ᵥ w) =
      pairRot h (Pi.single i 1) (Pi.single j 1) *ᵥ (M *ᵥ w) := by
    intro i j hij w
    rw [mulVec_mulVec, mulVec_mulVec, hM i j hij]
  have hdiag : ∀ a b : Fin n, a ≠ b → M a b = 0 := by
    intro a b hab
    obtain ⟨k, -, hk⟩ := Finset.exists_mem_notMem_of_card_lt_card
      (s := ({a, b} : Finset (Fin n))) (t := Finset.univ)
      (by
        calc ({a, b} : Finset (Fin n)).card ≤ 2 := Finset.card_le_two
          _ < Finset.univ.card := by simp; omega)
    have hka : k ≠ a := fun h' => hk (by simp [h'])
    have hkb : k ≠ b := fun h' => hk (by simp [h'])
    have hak : a ≠ k := hka.symm
    set g := pairRot h (Pi.single a 1) (Pi.single k 1) with hg
    have hgg := pairRot_sq_apply h (hnorm a) (hnorm k) (horth a k hak) (Pi.single b 1 : Fin n → K)
    have hba : stdHermForm h n (Pi.single a 1) (Pi.single b 1) = 0 := horth a b hab
    have hbk : stdHermForm h n (Pi.single k 1) (Pi.single b 1) = 0 := horth k b hkb
    simp only [hba, hbk, mul_zero, zero_smul, sub_zero] at hgg
    set u : Fin n → K := M *ᵥ Pi.single b 1 with hu
    have e1 : u = g *ᵥ (g *ᵥ u) := by
      calc u = M *ᵥ (g *ᵥ (g *ᵥ Pi.single b 1)) := by rw [hgg]
        _ = g *ᵥ (M *ᵥ (g *ᵥ Pi.single b 1)) := hcomm a k hak _
        _ = g *ᵥ (g *ᵥ u) := by rw [hcomm a k hak]
    have e2 := pairRot_sq_apply h (hnorm a) (hnorm k) (horth a k hak) u
    rw [← e1] at e2
    have e3 := congrFun e2 a
    simp only [Pi.sub_apply, Pi.smul_apply, smul_eq_mul, stdHermForm_single, Pi.single_eq_same,
      Pi.single_eq_of_ne hak, mul_one, mul_zero, sub_zero] at e3
    have e4 : 2 * u a = 0 := by linear_combination e3
    have e5 : u a = 0 := (mul_eq_zero.1 e4).resolve_left h2
    rw [hu, mulVec_single_apply'] at e5
    exact e5
  have hdiag2 : ∀ a b : Fin n, M a a = M b b := by
    intro a b
    by_cases hab : a = b
    · rw [hab]
    · have h1 := hcomm a b hab (Pi.single a 1)
      rw [pairRot_apply_x h (hnorm a) (horth a b hab)] at h1
      have hMa : M *ᵥ (Pi.single a 1 : Fin n → K) = M a a • Pi.single a 1 := by
        funext i
        by_cases hia : i = a
        · subst hia
          simp [mulVec_single]
        · simp [mulVec_single, hdiag i a hia, hia]
      rw [hMa, mulVec_smul, pairRot_apply_x h (hnorm a) (horth a b hab)] at h1
      have := congrFun h1 b
      rw [mulVec_single_apply', Pi.smul_apply, Pi.single_eq_same, smul_eq_mul, mul_one] at this
      exact this.symm
  refine ⟨M ⟨0, by omega⟩ ⟨0, by omega⟩, ?_⟩
  ext a b
  by_cases hab : a = b
  · subst hab
    simp [hdiag2 a ⟨0, by omega⟩]
  · simp [hdiag a b hab, Matrix.one_apply_ne hab]

end Scalar
end CFSG.GH74.Generic.S45.Uni
