module

public import CFSG.ClassicalInvolution.Models.SymplecticPairs.Intrinsic

public section

open scoped Matrix
open CFSG.ClassicalInvolution.Models.SymplecticPairs

namespace CFSG.ClassicalInvolution.Asc77.C25W.Sp

variable {F : Type} [Field F] {m : ℕ}


@[expose] def tv (τ : F ≃+* F) (v : Fin (m + 1) ⊕ Fin (m + 1) → F) :
    Fin (m + 1) ⊕ Fin (m + 1) → F :=
  fun i => τ (v i)

@[expose] def phi
    (N : Matrix (Fin (m + 1) ⊕ Fin (m + 1)) (Fin (m + 1) ⊕ Fin (m + 1)) F) (τ : F ≃+* F)
    (v : Fin (m + 1) ⊕ Fin (m + 1) → F) : Fin (m + 1) ⊕ Fin (m + 1) → F :=
  N *ᵥ tv τ v

variable (τ : F ≃+* F) (N : Matrix (Fin (m + 1) ⊕ Fin (m + 1)) (Fin (m + 1) ⊕ Fin (m + 1)) F)

theorem tv_add (v w : Fin (m + 1) ⊕ Fin (m + 1) → F) : tv τ (v + w) = tv τ v + tv τ w := by
  ext i; simp [tv]

theorem tv_smul (c : F) (v : Fin (m + 1) ⊕ Fin (m + 1) → F) : tv τ (c • v) = τ c • tv τ v := by
  ext i; simp [tv]

theorem tv_tv (hτ : ∀ x, τ (τ x) = x) (v : Fin (m + 1) ⊕ Fin (m + 1) → F) :
    tv τ (tv τ v) = v := by
  ext i; simp [tv, hτ]

theorem tv_mulVec (M : Matrix (Fin (m + 1) ⊕ Fin (m + 1)) (Fin (m + 1) ⊕ Fin (m + 1)) F)
    (v : Fin (m + 1) ⊕ Fin (m + 1) → F) : tv τ (M *ᵥ v) = M.map τ *ᵥ tv τ v := by
  ext i
  simp [tv, Matrix.mulVec, dotProduct, map_sum, map_mul]

theorem phi_add (v w : Fin (m + 1) ⊕ Fin (m + 1) → F) :
    phi N τ (v + w) = phi N τ v + phi N τ w := by
  simp [phi, tv_add, Matrix.mulVec_add]

theorem phi_smul (c : F) (v : Fin (m + 1) ⊕ Fin (m + 1) → F) :
    phi N τ (c • v) = τ c • phi N τ v := by
  simp [phi, tv_smul, Matrix.mulVec_smul]

theorem form_tv (u v : Fin (m + 1) ⊕ Fin (m + 1) → F) :
    form (tv τ u) (tv τ v) = τ (form u v) := by
  rw [form_apply, form_apply, map_sum]
  refine Finset.sum_congr rfl fun a _ => ?_
  have hs : τ (sgn F a) = sgn F a := by cases a <;> simp [sgn]
  simp [tv, map_mul, hs]

theorem form_mulVec_of_isometry (hN : Nᵀ * gram F (m + 1) * N = gram F (m + 1))
    (u v : Fin (m + 1) ⊕ Fin (m + 1) → F) : form (N *ᵥ u) (N *ᵥ v) = form u v := by
  unfold form
  rw [Matrix.mulVec_mulVec, ← Matrix.vecMul_transpose, ← Matrix.dotProduct_mulVec,
    Matrix.mulVec_mulVec, ← Matrix.mul_assoc, hN]

theorem form_phi (hN : Nᵀ * gram F (m + 1) * N = gram F (m + 1))
    (u v : Fin (m + 1) ⊕ Fin (m + 1) → F) : form (phi N τ u) (phi N τ v) = τ (form u v) := by
  unfold phi
  rw [form_mulVec_of_isometry N hN, form_tv]

theorem phi_phi (hτ : ∀ x, τ (τ x) = x) (c' : F) (hc : N * N.map τ = c' • 1)
    (v : Fin (m + 1) ⊕ Fin (m + 1) → F) : phi N τ (phi N τ v) = c' • v := by
  unfold phi
  rw [tv_mulVec, tv_tv τ hτ, Matrix.mulVec_mulVec, hc]
  rw [Matrix.smul_mulVec, Matrix.one_mulVec]


theorem eq_zero_of_form_right (v : Fin (m + 1) ⊕ Fin (m + 1) → F) (h : ∀ w, form v w = 0) :
    v = 0 := by
  funext a
  have := h (Pi.single (par a) 1)
  rw [form_single_right, par_par] at this
  exact (mul_eq_zero.1 this).resolve_right (sgn_ne_zero _)

theorem eq_zero_of_form_left (z : Fin (m + 1) ⊕ Fin (m + 1) → F) (h : ∀ x, form x z = 0) :
    z = 0 := by
  refine eq_zero_of_form_right z fun x => ?_
  rw [form_antisymm, h x, neg_zero]

theorem form_neg_right (u v : Fin (m + 1) ⊕ Fin (m + 1) → F) : form u (-v) = -form u v := by
  have := form_smul_right u v (-1 : F)
  rw [neg_one_smul] at this
  rw [this]; ring

theorem form_neg_left (u v : Fin (m + 1) ⊕ Fin (m + 1) → F) : form (-u) v = -form u v := by
  have := form_smul_left u v (-1 : F)
  rw [neg_one_smul] at this
  rw [this]; ring

theorem form_sub_left (a b v : Fin (m + 1) ⊕ Fin (m + 1) → F) :
    form (a - b) v = form a v - form b v := by
  rw [sub_eq_add_neg, form_add_left, form_neg_left]; ring

theorem form_sub_right (v a b : Fin (m + 1) ⊕ Fin (m + 1) → F) :
    form v (a - b) = form v a - form v b := by
  rw [sub_eq_add_neg, form_add_right, form_neg_right]; ring

theorem phi_inj (hτ : ∀ x, τ (τ x) = x) (c' : F) (hc' : c' ≠ 0) (hc : N * N.map τ = c' • 1)
    (y : Fin (m + 1) ⊕ Fin (m + 1) → F) (h : phi N τ y = 0) : y = 0 := by
  have h1 := phi_phi τ N hτ c' hc y
  have h2 : phi N τ 0 = 0 := by
    have : tv τ (0 : Fin (m + 1) ⊕ Fin (m + 1) → F) = 0 := by ext i; simp [tv]
    simp [phi, this]
  rw [h, h2] at h1
  have := (smul_eq_zero.1 h1.symm).resolve_left hc'
  exact this

theorem exists_form_phi_ne_of_ne (hτ : ∃ a, τ a ≠ a) (hinj : ∀ y, phi N τ y = 0 → y = 0) :
    ∃ x, form x (phi N τ x) ≠ 0 := by
  by_contra hcon
  push Not at hcon
  have hsym : ∀ x y, form x (phi N τ y) + form y (phi N τ x) = 0 := by
    intro x y
    have h := hcon (x + y)
    rw [phi_add, form_add_left, form_add_right, form_add_right, hcon x, hcon y] at h
    linear_combination h
  obtain ⟨a, ha⟩ := hτ
  have hz : ∀ x y, form x (phi N τ y) = 0 := by
    intro x y
    have h1 := hsym (a • x) y
    have h2 := hsym x y
    rw [form_smul_left, phi_smul, form_smul_right] at h1
    have : (a - τ a) * form x (phi N τ y) = 0 := by linear_combination h1 - (τ a) * h2
    exact (mul_eq_zero.mp this).resolve_left (sub_ne_zero.mpr (Ne.symm ha))
  have h0 : ∀ y, phi N τ y = 0 := fun y => eq_zero_of_form_left _ (fun x => hz x y)
  have := hinj (Pi.single (Sum.inl 0) 1) (h0 _)
  have h1 := congrFun this (Sum.inl 0)
  simp at h1

theorem exists_form_ne_of_sq_neg (h2 : (2 : F) ≠ 0)
    (hN : Nᵀ * gram F (m + 1) * N = gram F (m + 1)) (hN2 : N * N = -1) :
    ∃ x, form x (N *ᵥ x) ≠ 0 := by
  by_contra hcon
  push Not at hcon
  have hsym : ∀ x y, form x (N *ᵥ y) + form y (N *ᵥ x) = 0 := by
    intro x y
    have h := hcon (x + y)
    rw [Matrix.mulVec_add, form_add_left, form_add_right, form_add_right, hcon x, hcon y] at h
    linear_combination h
  have hsq : ∀ y, N *ᵥ (N *ᵥ y) = -y := by
    intro y; rw [Matrix.mulVec_mulVec, hN2, Matrix.neg_mulVec, Matrix.one_mulVec]
  have hiso : ∀ x y, form x (N *ᵥ y) = form y (N *ᵥ x) := by
    intro x y
    have h := form_mulVec_of_isometry N hN x (N *ᵥ y)
    rw [hsq, form_neg_right] at h
    have h' := form_antisymm (N *ᵥ x) y
    linear_combination -h - h'
  have hz : ∀ x y, form x (N *ᵥ y) = 0 := by
    intro x y
    have h1 := hsym x y
    rw [← hiso x y] at h1
    have : (2 : F) * form x (N *ᵥ y) = 0 := by linear_combination h1
    exact (mul_eq_zero.1 this).resolve_left h2
  have h0 : ∀ y, N *ᵥ y = 0 := fun y => eq_zero_of_form_left _ (fun x => hz x y)
  have h3 := hsq (Pi.single (Sum.inl 0) 1)
  rw [h0] at h3
  have h4 := congrFun h3 (Sum.inl 0)
  simp at h4


theorem phi_sub (a b : Fin (m + 1) ⊕ Fin (m + 1) → F) :
    phi N τ (a - b) = phi N τ a - phi N τ b := by
  have h := phi_add τ N (a - b) b
  rw [sub_add_cancel] at h
  exact eq_sub_of_add_eq h.symm

theorem exists_fixed_pair_lin (h2 : (2 : F) ≠ 0)
    (hN : Nᵀ * gram F (m + 1) * N = gram F (m + 1)) (hN2 : N * N = 1)
    (y : Fin (m + 1) ⊕ Fin (m + 1) → F) (hy : N *ᵥ y + y ≠ 0) :
    ∃ u w, N *ᵥ u = u ∧ N *ᵥ w = w ∧ form u w = 1 := by
  have hsq : ∀ y, N *ᵥ (N *ᵥ y) = y := by
    intro y; rw [Matrix.mulVec_mulVec, hN2, Matrix.one_mulVec]
  have hu : N *ᵥ (N *ᵥ y + y) = N *ᵥ y + y := by
    rw [Matrix.mulVec_add, hsq]; exact add_comm _ _
  obtain ⟨w', hw'⟩ : ∃ w', form (N *ᵥ y + y) w' ≠ 0 := by
    by_contra h
    push Not at h
    exact hy (eq_zero_of_form_right _ h)
  have hw'' : N *ᵥ (N *ᵥ w' + w') = N *ᵥ w' + w' := by
    rw [Matrix.mulVec_add, hsq]; exact add_comm _ _
  have hform : form (N *ᵥ y + y) (N *ᵥ w' + w') = 2 * form (N *ᵥ y + y) w' := by
    have h := form_mulVec_of_isometry N hN (N *ᵥ y + y) (N *ᵥ w')
    rw [hu, hsq] at h
    rw [form_add_right, ← h]; ring
  refine ⟨N *ᵥ y + y, (form (N *ᵥ y + y) (N *ᵥ w' + w'))⁻¹ • (N *ᵥ w' + w'), hu, ?_, ?_⟩
  · rw [Matrix.mulVec_smul, hw'']
  · rw [form_smul_right, inv_mul_cancel₀]
    rw [hform]; exact mul_ne_zero h2 hw'

theorem exists_fixed_pair_semi (h2 : (2 : F) ≠ 0) (hτ : ∀ x, τ (τ x) = x) (hne : ∃ a, τ a ≠ a)
    (hN : Nᵀ * gram F (m + 1) * N = gram F (m + 1)) (hc : N * N.map τ = (1 : F) • 1) :
    ∃ u w, phi N τ u = u ∧ phi N τ w = w ∧ form u w = 1 := by
  have hinj : ∀ y, phi N τ y = 0 → y = 0 := phi_inj τ N hτ 1 one_ne_zero hc
  obtain ⟨x, hx⟩ := exists_form_phi_ne_of_ne τ N hne hinj
  have hφφ : ∀ v, phi N τ (phi N τ v) = v := fun v => by rw [phi_phi τ N hτ 1 hc]; simp
  obtain ⟨a, ha⟩ := hne
  have hδ0 : a - τ a ≠ 0 := sub_ne_zero.2 (Ne.symm ha)
  have hτδ : τ (a - τ a) = -(a - τ a) := by rw [map_sub, hτ]; ring
  have he₀ : phi N τ (x + phi N τ x) = x + phi N τ x := by
    rw [phi_add, hφφ]; exact add_comm _ _
  have hf₀ : phi N τ ((a - τ a) • (x - phi N τ x)) = (a - τ a) • (x - phi N τ x) := by
    rw [phi_smul, phi_sub, hφφ, hτδ, neg_smul, ← smul_neg, neg_sub]
  have hform : form (x + phi N τ x) ((a - τ a) • (x - phi N τ x)) =
      -2 * (a - τ a) * form x (phi N τ x) := by
    rw [form_smul_right, form_add_left, form_sub_right, form_sub_right, form_self,
      form_self, form_antisymm x (phi N τ x)]
    ring
  have hform0 : form (x + phi N τ x) ((a - τ a) • (x - phi N τ x)) ≠ 0 := by
    rw [hform]
    exact mul_ne_zero (mul_ne_zero (neg_ne_zero.2 h2) hδ0) hx
  have hτform : τ (form (x + phi N τ x) ((a - τ a) • (x - phi N τ x))) =
      form (x + phi N τ x) ((a - τ a) • (x - phi N τ x)) := by
    rw [← form_phi τ N hN, he₀, hf₀]
  refine ⟨x + phi N τ x, (form (x + phi N τ x) ((a - τ a) • (x - phi N τ x)))⁻¹ •
    ((a - τ a) • (x - phi N τ x)), he₀, ?_, ?_⟩
  · rw [phi_smul, hf₀, map_inv₀, hτform]
  · rw [form_smul_right, inv_mul_cancel₀ hform0]

theorem exists_decomp (u w v : Fin (m + 1) ⊕ Fin (m + 1) → F) (huw : form u w = 1) :
    ∃ (A B : F) (q : Fin (m + 1) ⊕ Fin (m + 1) → F), form q u = 0 ∧ form q w = 0 ∧
      v = A • u + B • w + q := by
  refine ⟨form v w, form u v, v - form v w • u - form u v • w, ?_, ?_, by abel⟩
  · rw [form_sub_left, form_sub_left, form_smul_left, form_smul_left, form_self,
      form_antisymm u w, huw, form_antisymm u v]
    ring
  · rw [form_sub_left, form_sub_left, form_smul_left, form_smul_left, form_self, huw]
    ring

theorem comm_of_pair (φ : (Fin (m + 1) ⊕ Fin (m + 1) → F) → (Fin (m + 1) ⊕ Fin (m + 1) → F))
    (hadd : ∀ x y, φ (x + y) = φ x + φ y) (hsmul : ∀ (c : F) x, φ (c • x) = τ c • φ x)
    {u w : Fin (m + 1) ⊕ Fin (m + 1) → F} (huw : form u w = 1)
    (s : Matrix (Fin (m + 1) ⊕ Fin (m + 1)) (Fin (m + 1) ⊕ Fin (m + 1)) F)
    (hperp : ∀ q, form q u = 0 → form q w = 0 → s *ᵥ q = q)
    (hφperp : ∀ q, form q u = 0 → form q w = 0 → form (φ q) u = 0 ∧ form (φ q) w = 0)
    (hu : φ (s *ᵥ u) = s *ᵥ φ u) (hw : φ (s *ᵥ w) = s *ᵥ φ w)
    (v : Fin (m + 1) ⊕ Fin (m + 1) → F) : φ (s *ᵥ v) = s *ᵥ φ v := by
  obtain ⟨A, B, q, hq1, hq2, rfl⟩ := exists_decomp u w v huw
  have hsq := hperp q hq1 hq2
  have hφq := hφperp q hq1 hq2
  have hsφq := hperp (φ q) hφq.1 hφq.2
  rw [Matrix.mulVec_add, Matrix.mulVec_add, Matrix.mulVec_smul, Matrix.mulVec_smul, hsq,
    hadd, hadd, hsmul, hsmul, hu, hw, hadd, hadd, hsmul, hsmul, Matrix.mulVec_add,
    Matrix.mulVec_add, Matrix.mulVec_smul, Matrix.mulVec_smul, hsφq]

end CFSG.ClassicalInvolution.Asc77.C25W.Sp
