module

public import CFSG.ClassicalInvolution.Models.SymplecticPairs.Witt

public section

namespace CFSG.HardMathSupport.Meierfrankenfeld.LieOdd

open Matrix CFSG.ClassicalInvolution.Models.SymplecticPairs CFSG.Assembly.LowTwoRank
open CFSG.LieType.Universal.Symplectic.SpExtras (mat mat_injective)

variable {K : Type} [Field K] {r : ℕ}

section Form

theorem form_add_left (u u' v : Fin r ⊕ Fin r → K) : form (u + u') v = form u v + form u' v := by
  simp [form, add_dotProduct]

theorem form_add_right (u v v' : Fin r ⊕ Fin r → K) : form u (v + v') = form u v + form u v' := by
  simp [form, Matrix.mulVec_add, dotProduct_add]

theorem form_smul_left (c : K) (u v : Fin r ⊕ Fin r → K) : form (c • u) v = c * form u v := by
  simp [form, smul_dotProduct]

theorem form_smul_right (c : K) (u v : Fin r ⊕ Fin r → K) : form u (c • v) = c * form u v := by
  simp [form, Matrix.mulVec_smul, dotProduct_smul]

theorem form_neg_left (u v : Fin r ⊕ Fin r → K) : form (-u) v = -form u v := by
  simp [form]

theorem form_neg_right (u v : Fin r ⊕ Fin r → K) : form u (-v) = -form u v := by
  simp [form, Matrix.mulVec_neg, dotProduct_neg]

theorem form_zero_left (v : Fin r ⊕ Fin r → K) : form 0 v = 0 := by
  simp [form]

theorem form_zero_right (u : Fin r ⊕ Fin r → K) : form u 0 = 0 := by
  simp [form]

theorem form_sub_left (u u' v : Fin r ⊕ Fin r → K) : form (u - u') v = form u v - form u' v := by
  simp [form, sub_dotProduct]

theorem form_sub_right (u v v' : Fin r ⊕ Fin r → K) : form u (v - v') = form u v - form u v' := by
  simp [form, Matrix.mulVec_sub, dotProduct_sub]

theorem eq_zero_of_forall_form_eq_zero {u : Fin r ⊕ Fin r → K} (h : ∀ w, form u w = 0) : u = 0 := by
  funext a
  have := h (Pi.single (par a) 1)
  rw [form_single_right, par_par] at this
  simpa [sgn_ne_zero] using this

theorem exists_form_ne_zero {u : Fin r ⊕ Fin r → K} (hu : u ≠ 0) : ∃ w, form u w ≠ 0 := by
  by_contra h
  exact hu (eq_zero_of_forall_form_eq_zero fun w => by_contra fun hw => h ⟨w, hw⟩)

theorem symplectic_of_form (M : Matrix (Fin r ⊕ Fin r) (Fin r ⊕ Fin r) K)
    (h : ∀ a b, form (M *ᵥ a) (M *ᵥ b) = form a b) : Mᵀ * gram K r * M = gram K r := by
  rw [Matrix.ext_iff_mulVec]
  intro b
  refine dotProduct_eq _ _ fun a => ?_
  have key : ∀ y, (M *ᵥ a) ⬝ᵥ y = (Mᵀ *ᵥ y) ⬝ᵥ a := fun y => by
    rw [dotProduct_comm, Matrix.dotProduct_mulVec, Matrix.mulVec_transpose]
  have e := h a b
  unfold form at e
  rw [key] at e
  rw [← Matrix.mulVec_mulVec, ← Matrix.mulVec_mulVec, e, dotProduct_comm]

@[expose] def eichM (v u : Fin r ⊕ Fin r → K) (c : K) :
    Matrix (Fin r ⊕ Fin r) (Fin r ⊕ Fin r) K :=
  1 + vecMulVec u (gram K r *ᵥ v) + vecMulVec v (gram K r *ᵥ u) +
    c • vecMulVec v (gram K r *ᵥ v)

theorem eichM_mulVec (v u : Fin r ⊕ Fin r → K) (c : K) (w : Fin r ⊕ Fin r → K) :
    eichM v u c *ᵥ w = w + form w v • u + form w u • v + (c * form w v) • v := by
  have h : ∀ x : Fin r ⊕ Fin r → K, (gram K r *ᵥ x) ⬝ᵥ w = form w x := fun x => by
    rw [dotProduct_comm]; rfl
  simp only [eichM, Matrix.add_mulVec, Matrix.smul_mulVec, Matrix.one_mulVec,
    Matrix.vecMulVec_mulVec, op_smul_eq_smul, h, mul_smul]

theorem form_eichM (v u : Fin r ⊕ Fin r → K) (c : K) (hu : form u v = 0)
    (a b : Fin r ⊕ Fin r → K) :
    form (eichM v u c *ᵥ a) (eichM v u c *ᵥ b) = form a b := by
  have hvu : form v u = 0 := by rw [form_antisymm, hu, neg_zero]
  have hvv := form_self v
  have huu := form_self u
  rw [eichM_mulVec, eichM_mulVec]
  simp only [form_add_left, form_add_right, form_smul_left, form_smul_right, hu, hvu, hvv, huu,
    form_antisymm b u, form_antisymm b v]
  ring

@[expose] noncomputable def Eel (v u : Fin r ⊕ Fin r → K) (c : K) (hu : form u v = 0) :
    StatedSp r K :=
  ofSymplecticMat (eichM v u c) (symplectic_of_form _ (form_eichM v u c hu))

theorem Eel_mulVec (v u : Fin r ⊕ Fin r → K) (c : K) (hu : form u v = 0)
    (w : Fin r ⊕ Fin r → K) :
    mat r K (Eel v u c hu) *ᵥ w = w + form w v • u + form w u • v + (c * form w v) • v :=
  eichM_mulVec v u c w

theorem Sp_ext_mulVec {g h : StatedSp r K}
    (H : ∀ w, mat r K g *ᵥ w = mat r K h *ᵥ w) : g = h :=
  mat_injective (Matrix.ext_iff_mulVec.2 H)

theorem Eel_congr {v u u' : Fin r ⊕ Fin r → K} {c c' : K} (hu : form u v = 0)
    (hu' : form u' v = 0) (h1 : u = u') (h2 : c = c') : Eel v u c hu = Eel v u' c' hu' := by
  subst h1; subst h2; rfl

theorem Eel_zero (v : Fin r ⊕ Fin r → K) : Eel v 0 0 (form_zero_left v) = 1 := by
  refine Sp_ext_mulVec fun w => ?_
  rw [Eel_mulVec, map_one, Matrix.one_mulVec]
  simp [form_zero_right]

theorem Eel_mul {v u u' : Fin r ⊕ Fin r → K} (c c' : K) (hu : form u v = 0)
    (hu' : form u' v = 0) :
    Eel v u c hu * Eel v u' c' hu' =
      Eel v (u + u') (c + c' - form u u') (by rw [form_add_left, hu, hu', add_zero]) := by
  refine Sp_ext_mulVec fun w => ?_
  have hvu : form v u = 0 := by rw [form_antisymm, hu, neg_zero]
  have hvu' : form v u' = 0 := by rw [form_antisymm, hu', neg_zero]
  have hvv := form_self v
  rw [map_mul, ← Matrix.mulVec_mulVec, Eel_mulVec, Eel_mulVec, Eel_mulVec]
  simp only [form_add_left, form_add_right, form_smul_left, hu', hvu, hvv, form_antisymm u' u,
    mul_zero, add_zero, smul_add]
  module

theorem Eel_inv {v u : Fin r ⊕ Fin r → K} (c : K) (hu : form u v = 0) :
    (Eel v u c hu)⁻¹ = Eel v (-u) (-c) (by rw [form_neg_left, hu, neg_zero]) := by
  refine inv_eq_of_mul_eq_one_right ?_
  rw [Eel_mul, ← Eel_zero v]
  exact Eel_congr _ _ (add_neg_cancel u) (by simp [form_neg_right, form_self])

theorem Eel_pow {v u : Fin r ⊕ Fin r → K} (c : K) (hu : form u v = 0) (k : ℕ) :
    (Eel v u c hu) ^ k = Eel v ((k : K) • u) ((k : K) * c)
      (by rw [form_smul_left, hu, mul_zero]) := by
  induction k with
  | zero =>
    rw [pow_zero, ← Eel_zero v]
    exact (Eel_congr _ _ (by simp) (by simp)).symm
  | succ k ih =>
    rw [pow_succ, ih, Eel_mul]
    refine Eel_congr _ _ ?_ ?_
    · rw [Nat.cast_succ, add_smul, one_smul]
    · rw [form_smul_left, form_self, Nat.cast_succ]
      ring

theorem Eel_pow_char {v u : Fin r ⊕ Fin r → K} (c : K) (hu : form u v = 0) (p : ℕ) [CharP K p] :
    (Eel v u c hu) ^ p = 1 := by
  rw [Eel_pow, ← Eel_zero v]
  exact Eel_congr _ _ (by simp [CharP.cast_eq_zero]) (by simp [CharP.cast_eq_zero])

theorem conj_Eel (g : StatedSp r K) {v u : Fin r ⊕ Fin r → K} (c : K) (hu : form u v = 0) :
    g * Eel v u c hu * g⁻¹ =
      Eel (mat r K g *ᵥ v) (mat r K g *ᵥ u) c (by rw [form_mulVec]; exact hu) := by
  refine Sp_ext_mulVec fun w => ?_
  rw [map_mul, map_mul, ← Matrix.mulVec_mulVec, ← Matrix.mulVec_mulVec, Eel_mulVec, Eel_mulVec]
  have h1 : form (mat r K g⁻¹ *ᵥ w) v = form w (mat r K g *ᵥ v) := by
    rw [← form_mulVec g (mat r K g⁻¹ *ᵥ w) v, mulVec_mulVec_inv]
  have h2 : form (mat r K g⁻¹ *ᵥ w) u = form w (mat r K g *ᵥ u) := by
    rw [← form_mulVec g (mat r K g⁻¹ *ᵥ w) u, mulVec_mulVec_inv]
  rw [Matrix.mulVec_add, Matrix.mulVec_add, Matrix.mulVec_add, Matrix.mulVec_smul,
    Matrix.mulVec_smul, Matrix.mulVec_smul, mulVec_mulVec_inv, h1, h2]

theorem Eel_swap_neg {v u : Fin r ⊕ Fin r → K} (hu' : form (-v) u = 0) (hu'' : form (-u) v = 0) : Eel u (-v) 0 hu' = Eel v (-u) 0 hu'' := by
  refine Sp_ext_mulVec fun w => ?_
  rw [Eel_mulVec, Eel_mulVec]
  simp only [form_neg_right, zero_mul]
  module

end Form

end CFSG.HardMathSupport.Meierfrankenfeld.LieOdd
