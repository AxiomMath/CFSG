module

public import CFSG.ClassicalInvolution.Q3.Q3ZAHeis
public import CFSG.ClassicalInvolution.Q3.Q3ZFraFrame

public section

namespace CFSG.ClassicalInvolution.Q3.Q3ZB

open CFSG.Assembly.LowTwoRank CFSG.ClassicalInvolution.Models.SymplecticPairs
  CFSG.ClassicalInvolution.Q3.Q3ZA
open CFSG.LieType.Universal.Symplectic.SpExtras (mat mat_injective)
open Matrix

theorem f3_three_eq_zero : (3 : F3) = 0 := by
  have : CharP F3 3 := inferInstance
  exact_mod_cast CharP.cast_eq_zero F3 3

theorem f3_eq_zero_or_one_or_neg_one (a : F3) : a = 0 ∨ a = 1 ∨ a = -1 := by
  classical
  have : Fintype F3 := Fintype.ofFinite _
  have hcard : Fintype.card F3 = 3 := by
    rw [← Nat.card_eq_fintype_card, GaloisField.card 3 1 one_ne_zero]
    norm_num
  have h := FiniteField.pow_card a
  rw [hcard] at h
  have h3 : a * (a - 1) * (a + 1) = 0 := by linear_combination h
  rcases mul_eq_zero.mp h3 with h4 | h4
  · rcases mul_eq_zero.mp h4 with h5 | h5
    · exact Or.inl h5
    · exact Or.inr (Or.inl (sub_eq_zero.mp h5))
  · exact Or.inr (Or.inr (eq_neg_of_add_eq_zero_left h4))

theorem eq_one_of_heisAct_eq {s : StatedSp 2 F3} (h : ∀ x, heisAct s x = x) : s = 1 := by
  apply mat_injective
  rw [map_one, Matrix.ext_iff_mulVec]
  intro v
  have := congrArg Heis.v (h (Heis.vec v))
  rw [Matrix.one_mulVec]
  exact this

theorem heisAct_injective : Function.Injective (heisAct : StatedSp 2 F3 →* MulAut Heis) := by
  rw [injective_iff_map_eq_one]
  intro s hs
  exact eq_one_of_heisAct_eq fun x => by rw [hs]; rfl

theorem heisAct_negOne (x : Heis) :
    heisAct (CFSG.ClassicalInvolution.Q3.Q3Z.negOne 2 F3) x = ⟨x.c, -x.v⟩ := by
  rw [heisAct_apply, CFSG.ClassicalInvolution.Q3.Q3Z.mat_negOne, Matrix.neg_mulVec,
    Matrix.one_mulVec]

section Aut

variable {α : Heis ≃* Heis} {ℓ : V4 → F3} {M : V4 → V4}

theorem heisAut_central (hz : α Heis.center = Heis.center) (c : F3) : α ⟨c, 0⟩ = ⟨c, 0⟩ := by
  rcases f3_eq_zero_or_one_or_neg_one c with rfl | rfl | rfl
  · rw [← Heis.one_def, map_one]
  · exact hz
  · have h : (⟨-1, 0⟩ : Heis) = Heis.center⁻¹ := by
      refine Heis.ext rfl ?_
      simp [Heis.inv_def, Heis.center]
    rw [h, map_inv, hz]

theorem heisAut_apply (hz : α Heis.center = Heis.center)
    (h : ∀ v, α (Heis.vec v) = ⟨ℓ v, M v⟩) (c : F3) (v : V4) :
    α ⟨c, v⟩ = ⟨c + ℓ v, M v⟩ := by
  have e : (⟨c, v⟩ : Heis) = ⟨c, 0⟩ * Heis.vec v := by
    rw [Heis.mul_def]
    refine Heis.ext ?_ ?_ <;> simp [Heis.vec, form_zero_left]
  rw [e, map_mul, heisAut_central hz, h, Heis.mul_def]
  refine Heis.ext ?_ ?_ <;> simp [form_zero_left]

theorem heisAut_vec_mul (hz : α Heis.center = Heis.center)
    (h : ∀ v, α (Heis.vec v) = ⟨ℓ v, M v⟩) (v w : V4) :
    M (v + w) = M v + M w ∧ 2 * form v w + ℓ (v + w) = ℓ v + ℓ w + 2 * form (M v) (M w) := by
  have e := congrArg α (Heis.vec_mul_vec v w)
  rw [map_mul, h, h, heisAut_apply hz h, Heis.mul_def] at e
  exact ⟨(congrArg Heis.v e).symm, (congrArg Heis.c e).symm⟩

theorem heisAut_form (hz : α Heis.center = Heis.center)
    (h : ∀ v, α (Heis.vec v) = ⟨ℓ v, M v⟩) (v w : V4) : form (M v) (M w) = form v w := by
  have h1 := (heisAut_vec_mul hz h v w).2
  have h2 := (heisAut_vec_mul hz h w v).2
  rw [add_comm w v, form_antisymm v w, form_antisymm (M v) (M w)] at h2
  linear_combination (-1 : F3) * h1 + h2 + (form v w - form (M v) (M w)) * f3_three_eq_zero

theorem heisAut_add (hz : α Heis.center = Heis.center)
    (h : ∀ v, α (Heis.vec v) = ⟨ℓ v, M v⟩) (v w : V4) : ℓ (v + w) = ℓ v + ℓ w := by
  have h1 := (heisAut_vec_mul hz h v w).2
  rw [heisAut_form hz h] at h1
  linear_combination h1

theorem heisAut_neg
    (hτ : ∀ x, α (heisAct (CFSG.ClassicalInvolution.Q3.Q3Z.negOne 2 F3) x) =
      heisAct (CFSG.ClassicalInvolution.Q3.Q3Z.negOne 2 F3) (α x))
    (h : ∀ v, α (Heis.vec v) = ⟨ℓ v, M v⟩) (v : V4) : ℓ (-v) = ℓ v ∧ M (-v) = -M v := by
  have e := hτ (Heis.vec v)
  rw [heisAct_negOne, h, heisAct_negOne] at e
  have e' : (⟨ℓ (-v), M (-v)⟩ : Heis) = ⟨ℓ v, -M v⟩ := by
    rw [← h]
    exact e
  exact ⟨congrArg Heis.c e', congrArg Heis.v e'⟩

theorem heisAut_ell_eq_zero (hz : α Heis.center = Heis.center)
    (hτ : ∀ x, α (heisAct (CFSG.ClassicalInvolution.Q3.Q3Z.negOne 2 F3) x) =
      heisAct (CFSG.ClassicalInvolution.Q3.Q3Z.negOne 2 F3) (α x))
    (h : ∀ v, α (Heis.vec v) = ⟨ℓ v, M v⟩) (v : V4) : ℓ v = 0 := by
  have h0 : ℓ 0 = 0 := by
    have := heisAut_add hz h 0 0
    rw [add_zero] at this
    linear_combination (-1 : F3) * this
  have h1 := heisAut_add hz h v (-v)
  rw [add_neg_cancel, h0, (heisAut_neg hτ h v).1] at h1
  linear_combination (-2 : F3) * h1 - ℓ v * f3_three_eq_zero

theorem heisAut_smul (hz : α Heis.center = Heis.center)
    (hτ : ∀ x, α (heisAct (CFSG.ClassicalInvolution.Q3.Q3Z.negOne 2 F3) x) =
      heisAct (CFSG.ClassicalInvolution.Q3.Q3Z.negOne 2 F3) (α x))
    (h : ∀ v, α (Heis.vec v) = ⟨ℓ v, M v⟩) (c : F3) (v : V4) : M (c • v) = c • M v := by
  rcases f3_eq_zero_or_one_or_neg_one c with rfl | rfl | rfl
  · have := (heisAut_vec_mul hz h 0 0).1
    rw [add_zero] at this
    rw [zero_smul, zero_smul]
    simpa using this
  · rw [one_smul, one_smul]
  · rw [neg_one_smul, neg_one_smul]
    exact (heisAut_neg hτ h v).2

end Aut

theorem exists_matrix_mulVec_of_additive (M : V4 → V4) (hadd : ∀ v w, M (v + w) = M v + M w)
    (hsmul : ∀ (c : F3) v, M (c • v) = c • M v) :
    ∃ A : Matrix (Fin 2 ⊕ Fin 2) (Fin 2 ⊕ Fin 2) F3, ∀ v, A *ᵥ v = M v := by
  let L : V4 →ₗ[F3] V4 :=
    { toFun := M
      map_add' := hadd
      map_smul' := fun c v => by simpa using hsmul c v }
  exact ⟨LinearMap.toMatrix' L, fun v => by simp [L]⟩

theorem form_single_one_single_one (a b : Fin 2 ⊕ Fin 2) :
    form (Pi.single a (1 : F3) : V4) (Pi.single b 1) = gram F3 2 a b := by
  unfold form
  rw [single_dotProduct, one_mul, mulVec_single_one_apply]

theorem symplectic_of_form_mulVec_eq (A : Matrix (Fin 2 ⊕ Fin 2) (Fin 2 ⊕ Fin 2) F3)
    (hA : ∀ v w : V4, form (A *ᵥ v) (A *ᵥ w) = form v w) :
    Aᵀ * gram F3 2 * A = gram F3 2 := by
  ext a b
  rw [transpose_mul_gram_mul_apply]
  have e := hA (Pi.single a 1) (Pi.single b 1)
  rw [form_apply, form_single_one_single_one] at e
  simpa only [mulVec_single_one_apply] using e

theorem exists_heisAct_of_aut (α : Heis ≃* Heis) (hz : α Heis.center = Heis.center)
    (hτ : ∀ x, α (heisAct (CFSG.ClassicalInvolution.Q3.Q3Z.negOne 2 F3) x) =
      heisAct (CFSG.ClassicalInvolution.Q3.Q3Z.negOne 2 F3) (α x)) :
    ∃ s : StatedSp 2 F3, ∀ x, α x = heisAct s x := by
  obtain ⟨ℓ, M, h⟩ : ∃ (ℓ : V4 → F3) (M : V4 → V4), ∀ v, α (Heis.vec v) = ⟨ℓ v, M v⟩ :=
    ⟨fun v => (α (Heis.vec v)).c, fun v => (α (Heis.vec v)).v, fun v => rfl⟩
  obtain ⟨A, hA⟩ := exists_matrix_mulVec_of_additive M (fun v w => (heisAut_vec_mul hz h v w).1)
    (heisAut_smul hz hτ h)
  have hsymp : Aᵀ * gram F3 2 * A = gram F3 2 :=
    symplectic_of_form_mulVec_eq A fun v w => by rw [hA, hA, heisAut_form hz h]
  refine ⟨ofSymplecticMat A hsymp, fun x => ?_⟩
  rw [heisAct_apply, mat_ofSymplecticMat]
  have e := heisAut_apply hz h x.c x.v
  rw [heisAut_ell_eq_zero hz hτ h, add_zero] at e
  exact e.trans (by rw [hA])

end CFSG.ClassicalInvolution.Q3.Q3ZB
