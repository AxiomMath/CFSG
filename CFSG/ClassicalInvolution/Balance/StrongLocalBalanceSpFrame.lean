module

public import CFSG.ClassicalInvolution.Balance.StrongLocalBalanceSpTens
public import CFSG.ClassicalInvolution.Balance.StrongLocalBalanceSpForms

public section

namespace CFSG.ClassicalInvolution.Balance.StrongBalance.Sp

open CFSG.Assembly.LowTwoRank
open CFSG.ClassicalInvolution.Models.SymplecticPairs
open CFSG.LieType.Universal.Symplectic.SpExtras (mat mat_injective mat_apply)
open scoped Matrix

variable {F : Type} [Field F]

theorem exists_sq_add_sq [Finite F] (hodd : ringChar F ≠ 2) (x : F) :
    ∃ a b : F, a ^ 2 + b ^ 2 = x := by
  classical
  have : Fintype F := Fintype.ofFinite F
  obtain ⟨a, b, hab⟩ : ∃ a b, (Polynomial.X ^ 2 : Polynomial F).eval a +
      (Polynomial.X ^ 2 - Polynomial.C x).eval b = 0 :=
    FiniteField.exists_root_sum_quadratic (Polynomial.degree_X_pow 2)
      (Polynomial.degree_X_pow_sub_C (by decide) _) (FiniteField.odd_card_of_char_ne_two hodd)
  refine ⟨a, b, ?_⟩
  rw [← sub_eq_zero]
  simpa only [Polynomial.eval_C, Polynomial.eval_X, Polynomial.eval_pow, Polynomial.eval_sub,
    ← add_sub_assoc] using hab

theorem form_sum_right {ι : Type*} (s : Finset ι) (v : Fin 2 ⊕ Fin 2 → F)
    (w : ι → Fin 2 ⊕ Fin 2 → F) : form v (∑ i ∈ s, w i) = ∑ i ∈ s, form v (w i) := by
  classical
  induction s using Finset.induction_on with
  | empty => simp [form_zero_right]
  | insert a s ha ih => rw [Finset.sum_insert ha, Finset.sum_insert ha, form_add_right, ih]

theorem eq_zero_of_form_basis (b : Module.Basis (Fin 2 ⊕ Fin 2) F (Fin 2 ⊕ Fin 2 → F))
    {y : Fin 2 ⊕ Fin 2 → F} (h : ∀ i, form y (b i) = 0) : y = 0 := by
  by_contra hy
  obtain ⟨s, hs⟩ := exists_form_eq_one hy
  have : form y s = 0 := by
    conv_lhs => rw [← b.sum_repr s]
    rw [form_sum_right]
    refine Finset.sum_eq_zero fun i _ => ?_
    rw [form_smul_right, h i, mul_zero]
  rw [hs] at this
  exact one_ne_zero this

section Involution

variable {x : StatedSp 2 F}

theorem mulVec_mulVec_neg (hx : x * x = negOne) (t : Fin 2 ⊕ Fin 2 → F) :
    mat 2 F x *ᵥ (mat 2 F x *ᵥ t) = -t := by
  rw [Matrix.mulVec_mulVec, ← map_mul, hx, mat_negOne, Matrix.neg_mulVec, Matrix.one_mulVec]

theorem form_swap (hx : x * x = negOne) (u w : Fin 2 ⊕ Fin 2 → F) :
    form w (mat 2 F x *ᵥ u) = form u (mat 2 F x *ᵥ w) := by
  calc form w (mat 2 F x *ᵥ u)
      = form (mat 2 F x *ᵥ w) (mat 2 F x *ᵥ (mat 2 F x *ᵥ u)) := (form_mulVec x w _).symm
    _ = form (mat 2 F x *ᵥ w) (-u) := by rw [mulVec_mulVec_neg hx]
    _ = -form (mat 2 F x *ᵥ w) u := form_neg_right _ _
    _ = form u (mat 2 F x *ᵥ w) := (form_antisymm _ _).symm

theorem exists_form_mulVec_ne_zero (h2 : (2 : F) ≠ 0) (hx : x * x = negOne) :
    ∃ v, form v (mat 2 F x *ᵥ v) ≠ 0 := by
  by_contra hcon
  push Not at hcon
  have hbil : ∀ u w, form u (mat 2 F x *ᵥ w) = 0 := by
    intro u w
    have h1 := hcon (u + w)
    rw [Matrix.mulVec_add, form_add_left, form_add_right, form_add_right, hcon u, hcon w,
      form_swap hx u w] at h1
    have : (2 : F) * form u (mat 2 F x *ᵥ w) = 0 := by linear_combination h1
    exact (mul_eq_zero.mp this).resolve_left h2
  have hz : ∀ w, mat 2 F x *ᵥ w = 0 := by
    intro w
    by_contra hw
    obtain ⟨s, hs⟩ := exists_form_eq_one hw
    have := hbil s w
    rw [form_antisymm, hs] at this
    simp at this
  have := mulVec_mulVec_neg hx (Pi.single (Sum.inl 0) (1 : F))
  rw [hz] at this
  have := congrFun this (Sum.inl 0)
  simp at this

theorem form_mulVec_left (hx : x * x = negOne) (a w : Fin 2 ⊕ Fin 2 → F) :
    form (mat 2 F x *ᵥ a) w = -form a (mat 2 F x *ᵥ w) := by
  have h : w = -(mat 2 F x *ᵥ (mat 2 F x *ᵥ w)) := by rw [mulVec_mulVec_neg hx, neg_neg]
  calc form (mat 2 F x *ᵥ a) w
      = form (mat 2 F x *ᵥ a) (-(mat 2 F x *ᵥ (mat 2 F x *ᵥ w))) := by rw [← h]
    _ = -form (mat 2 F x *ᵥ a) (mat 2 F x *ᵥ (mat 2 F x *ᵥ w)) := form_neg_right _ _
    _ = -form a (mat 2 F x *ᵥ w) := by rw [form_mulVec]

theorem exists_orth_form_ne_zero (h2 : (2 : F) ≠ 0) (hx : x * x = negOne)
    {v : Fin 2 ⊕ Fin 2 → F} (hc : form v (mat 2 F x *ᵥ v) ≠ 0) :
    ∃ u, form v u = 0 ∧ form (mat 2 F x *ᵥ v) u = 0 ∧ form u (mat 2 F x *ᵥ u) ≠ 0 := by
  set c := form v (mat 2 F x *ᵥ v) with hcdef
  set q : Fin 2 ⊕ Fin 2 → F := c⁻¹ • (mat 2 F x *ᵥ v) with hq
  have hXv : mat 2 F x *ᵥ v = c • q := by rw [hq, smul_smul, mul_inv_cancel₀ hc, one_smul]
  have hpq : form v q = 1 := by rw [hq, form_smul_right, inv_mul_cancel₀ hc]
  obtain ⟨b, hb, hbp, hbq⟩ : ∃ b : Module.Basis (Fin 2 ⊕ Fin 2) F (Fin 2 ⊕ Fin 2 → F),
      (∀ x y, form (b x) (b y) = gram F 2 x y) ∧ b (Sum.inl 0) = v ∧ b (Sum.inr 0) = q :=
    exists_symplectic_basis (m := 1) v q hpq
  have hvu₁ : form v (b (Sum.inl 1)) = 0 := by
    have := hb (Sum.inl 0) (Sum.inl 1)
    rw [hbp] at this
    simpa [gram_apply] using this
  have hvu₂ : form v (b (Sum.inr 1)) = 0 := by
    have := hb (Sum.inl 0) (Sum.inr 1)
    rw [hbp] at this
    simpa [gram_apply] using this
  have hqu₁ : form q (b (Sum.inl 1)) = 0 := by
    have := hb (Sum.inr 0) (Sum.inl 1)
    rw [hbq] at this
    simpa [gram_apply] using this
  have hqu₂ : form q (b (Sum.inr 1)) = 0 := by
    have := hb (Sum.inr 0) (Sum.inr 1)
    rw [hbq] at this
    simpa [gram_apply] using this
  have huu : form (b (Sum.inl 1)) (b (Sum.inr 1)) = 1 := by
    have := hb (Sum.inl 1) (Sum.inr 1)
    simpa [gram_apply] using this
  have hXvu : ∀ u, form q u = 0 → form (mat 2 F x *ᵥ v) u = 0 := fun u h => by
    rw [hXv, form_smul_left, h, mul_zero]
  by_contra H
  push Not at H
  set u₁ := b (Sum.inl 1) with hu₁
  set u₂ := b (Sum.inr 1) with hu₂
  have k1 := H u₁ hvu₁ (hXvu _ hqu₁)
  have k2 := H u₂ hvu₂ (hXvu _ hqu₂)
  have k3 := H (u₁ + u₂) (by rw [form_add_right, hvu₁, hvu₂, add_zero])
    (hXvu _ (by rw [form_add_right, hqu₁, hqu₂, add_zero]))
  have k12 : form u₁ (mat 2 F x *ᵥ u₂) = 0 := by
    rw [Matrix.mulVec_add, form_add_left, form_add_right, form_add_right, k1, k2,
      form_swap hx u₁ u₂] at k3
    have : (2 : F) * form u₁ (mat 2 F x *ᵥ u₂) = 0 := by linear_combination k3
    exact (mul_eq_zero.mp this).resolve_left h2
  have hy : mat 2 F x *ᵥ u₁ = 0 := by
    refine eq_zero_of_form_basis b fun i => ?_
    rw [form_mulVec_left hx, neg_eq_zero]
    rcases i with i | i <;> obtain rfl | rfl : i = 0 ∨ i = 1 := by fin_cases i <;> simp
    · rw [hbp, hXv, form_smul_right, form_antisymm q u₁, hqu₁]
      simp
    · rw [← hu₁, k1]
    · rw [hbq, hq, Matrix.mulVec_smul, form_smul_right, mulVec_mulVec_neg hx, form_neg_right,
        form_antisymm, hvu₁, neg_zero, neg_zero, mul_zero]
    · exact k12
  have hu0 : u₁ = 0 := by
    have := mulVec_mulVec_neg hx u₁
    rw [hy, Matrix.mulVec_zero] at this
    exact neg_eq_zero.mp this.symm
  rw [hu0, form_zero_left] at huu
  exact zero_ne_one huu

theorem exists_swap_frame [Finite F] (hodd : ringChar F ≠ 2) (hx : x * x = negOne) :
    ∃ E E' : Fin 2 ⊕ Fin 2 → F, form E E' = 1 ∧ form E (mat 2 F x *ᵥ E) = 0 ∧
      form E (mat 2 F x *ᵥ E') = 0 ∧ form E' (mat 2 F x *ᵥ E') = 0 := by
  have h2 : (2 : F) ≠ 0 := Ring.two_ne_zero hodd
  obtain ⟨v, hc⟩ := exists_form_mulVec_ne_zero h2 hx
  obtain ⟨u, hvu, hXvu, hc'⟩ := exists_orth_form_ne_zero h2 hx hc
  set c := form v (mat 2 F x *ᵥ v) with hcdef
  set c' := form u (mat 2 F x *ᵥ u) with hc'def
  obtain ⟨a, b, hab⟩ := exists_sq_add_sq hodd (-(c / c'))
  set w : Fin 2 ⊕ Fin 2 → F := a • u + b • (mat 2 F x *ᵥ u) with hw
  have hXw : mat 2 F x *ᵥ w = a • (mat 2 F x *ᵥ u) + b • (-u) := by
    rw [hw, Matrix.mulVec_add, Matrix.mulVec_smul, Matrix.mulVec_smul, mulVec_mulVec_neg hx]
  have hvXu : form v (mat 2 F x *ᵥ u) = 0 := by
    rw [← form_mulVec x v (mat 2 F x *ᵥ u), mulVec_mulVec_neg hx, form_neg_right, hXvu, neg_zero]
  have hvw : form v w = 0 := by
    rw [hw, form_add_right, form_smul_right, form_smul_right, hvu, hvXu]
    ring
  have hwv : form w v = 0 := by rw [form_antisymm, hvw, neg_zero]
  have hvXw : form v (mat 2 F x *ᵥ w) = 0 := by
    rw [hXw, form_add_right, form_smul_right, form_smul_right, form_neg_right, hvXu, hvu]
    ring
  have hwXv : form w (mat 2 F x *ᵥ v) = 0 := by rw [form_swap hx v w, hvXw]
  have hwXw : form w (mat 2 F x *ᵥ w) = -c := by
    have h1 : form w (mat 2 F x *ᵥ w) = (a ^ 2 + b ^ 2) * c' := by
      have e1 : form (mat 2 F x *ᵥ u) u = -c' := form_antisymm _ _
      rw [hXw, hw]
      simp only [form_add_left, form_add_right, form_smul_left, form_smul_right, form_neg_right,
        form_self, e1]
      rw [← hc'def]
      ring
    rw [h1, hab]
    field_simp
  have hww : form w w = 0 := form_self w
  have hvv : form v v = 0 := form_self v
  have hpair : ∀ s t : F, form (v + s • w) (v + t • w) = 0 := by
    intro s t
    rw [form_add_left, form_add_right, form_add_right, form_smul_left, form_smul_left,
      form_smul_right, form_smul_right, hvv, hvw, hwv, hww]
    ring
  have hpairX : ∀ s t : F, form (v + s • w) (mat 2 F x *ᵥ (v + t • w)) = c * (1 - s * t) := by
    intro s t
    rw [Matrix.mulVec_add, Matrix.mulVec_smul, form_add_left, form_add_right, form_add_right,
      form_smul_left, form_smul_left, form_smul_right, form_smul_right, hvXw, hwXv, hwXw, ← hcdef]
    ring
  have h2c : (2 : F) * c ≠ 0 := mul_ne_zero h2 hc
  set E' : Fin 2 ⊕ Fin 2 → F := v + (-1 : F) • w with hE'
  refine ⟨v + (1 : F) • w, (2 * c)⁻¹ • (mat 2 F x *ᵥ E'), ?_, ?_, ?_, ?_⟩
  · rw [form_smul_right, hE', hpairX]
    field_simp
    ring
  · rw [hpairX]
    ring
  · rw [Matrix.mulVec_smul, form_smul_right, mulVec_mulVec_neg hx, form_neg_right, hE', hpair]
    ring
  · have h0 : form E' (mat 2 F x *ᵥ E') = 0 := by
      rw [hE', hpairX]
      ring
    rw [Matrix.mulVec_smul, form_smul_left, form_smul_right, mulVec_mulVec_neg hx, form_neg_right,
      form_antisymm E' (mat 2 F x *ᵥ E'), h0]
    ring

end Involution

theorem mulVec_conj_basis_eq {n : ℕ} (g y : StatedSp n F) (j : Fin n ⊕ Fin n)
    {v r : Fin n ⊕ Fin n → F} (hg : mat n F g *ᵥ Pi.single j 1 = v)
    (hy : mat n F y *ᵥ v = mat n F g *ᵥ r) : mat n F (g⁻¹ * y * g) *ᵥ Pi.single j 1 = r := by
  rw [map_mul, map_mul, ← Matrix.mulVec_mulVec, ← Matrix.mulVec_mulVec, hg, hy,
    Matrix.mulVec_mulVec, ← map_mul, inv_mul_cancel, map_one, Matrix.one_mulVec]

section Columns

theorem mulVec_xSw_inl_zero :
    mat 2 F xSw *ᵥ Pi.single (Sum.inl 0) 1 = Pi.single (Sum.inl 1) 1 := by
  rw [mat_xSw, Matrix.mulVec_single_one]
  funext i
  rcases i with a | a <;> fin_cases a <;> simp [tens, Rot]

theorem mulVec_xSw_inl_one :
    mat 2 F xSw *ᵥ Pi.single (Sum.inl 1) 1 = -Pi.single (Sum.inl 0) 1 := by
  rw [mat_xSw, Matrix.mulVec_single_one]
  funext i
  rcases i with a | a <;> fin_cases a <;> simp [tens, Rot]

theorem mulVec_xSw_inr_zero :
    mat 2 F xSw *ᵥ Pi.single (Sum.inr 0) 1 = Pi.single (Sum.inr 1) 1 := by
  rw [mat_xSw, Matrix.mulVec_single_one]
  funext i
  rcases i with a | a <;> fin_cases a <;> simp [tens, Rot]

theorem mulVec_xSw_inr_one :
    mat 2 F xSw *ᵥ Pi.single (Sum.inr 1) 1 = -Pi.single (Sum.inr 0) 1 := by
  rw [mat_xSw, Matrix.mulVec_single_one]
  funext i
  rcases i with a | a <;> fin_cases a <;> simp [tens, Rot]

end Columns

theorem exists_conj_xSw [Finite F] (hodd : ringChar F ≠ 2) {x : StatedSp 2 F}
    (hx : x * x = negOne) : ∃ g : StatedSp 2 F, g⁻¹ * x * g = xSw := by
  obtain ⟨E, E', h₁, h₂, h₃, h₄⟩ := exists_swap_frame hodd hx
  have hXX : form (mat 2 F x *ᵥ E) (mat 2 F x *ᵥ E') = 1 := by rw [form_mulVec, h₁]
  have o₃ : form E' (mat 2 F x *ᵥ E) = 0 := by rw [form_swap hx, h₃]
  obtain ⟨g, g1, g2, g3, g4⟩ := exists_sp_apply_eq_two (m := 0) E E' (mat 2 F x *ᵥ E)
    (mat 2 F x *ᵥ E') h₁ hXX h₂ h₃ o₃ h₄
  refine ⟨g, mat_injective (matrix_ext_mulVec_single fun j => ?_)⟩
  rcases j with j | j <;> obtain rfl | rfl : j = 0 ∨ j = 1 := by fin_cases j <;> simp
  · rw [mulVec_xSw_inl_zero]
    exact mulVec_conj_basis_eq g x _ g1 g3.symm
  · rw [mulVec_xSw_inl_one]
    exact mulVec_conj_basis_eq g x _ g3 (by rw [mulVec_mulVec_neg hx, Matrix.mulVec_neg, g1])
  · rw [mulVec_xSw_inr_zero]
    exact mulVec_conj_basis_eq g x _ g2 g4.symm
  · rw [mulVec_xSw_inr_one]
    exact mulVec_conj_basis_eq g x _ g4 (by rw [mulVec_mulVec_neg hx, Matrix.mulVec_neg, g2])

end CFSG.ClassicalInvolution.Balance.StrongBalance.Sp
