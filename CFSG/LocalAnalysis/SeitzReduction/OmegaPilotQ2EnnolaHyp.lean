module

public import CFSG.LocalAnalysis.SeitzReduction.OmegaPilotLeviFact

public section

set_option linter.unusedSectionVars false
set_option linter.unusedSimpArgs false

namespace CFSG.SeitzReduction.OmegaPilot

open Subgroup QuadraticMap Matrix
open CFSG.Assembly.LowTwoRank (StatedOmega StatedQuadPlus)
open CFSG.LieType.Universal.Spin (quadPlus quadPlus_apply coe_quadPlus)

section Gram

variable {F : Type} [Field F] {ι : Type*} [Fintype ι] [DecidableEq ι]

theorem quad_sum_eq_of_gram {M₁ M₂ : Type*} [AddCommGroup M₁] [Module F M₁] [AddCommGroup M₂]
    [Module F M₂] (Q₁ : QuadraticForm F M₁) (Q₂ : QuadraticForm F M₂) (s : Finset ι)
    (f₁ : ι → M₁) (f₂ : ι → M₂) (hQ : ∀ i ∈ s, Q₁ (f₁ i) = Q₂ (f₂ i))
    (hB : ∀ i ∈ s, ∀ j ∈ s, i ≠ j → polar Q₁ (f₁ i) (f₁ j) = polar Q₂ (f₂ i) (f₂ j)) :
    Q₁ (∑ i ∈ s, f₁ i) = Q₂ (∑ i ∈ s, f₂ i) := by
  induction s using Finset.induction_on with
  | empty => simp
  | insert a s ha ih =>
    rw [Finset.sum_insert ha, Finset.sum_insert ha, QuadraticMap.map_add Q₁,
      QuadraticMap.map_add Q₂,
      ih (fun i hi => hQ i (Finset.mem_insert_of_mem hi))
        (fun i hi j hj hij => hB i (Finset.mem_insert_of_mem hi) j (Finset.mem_insert_of_mem hj) hij),
      hQ a (Finset.mem_insert_self a s), ← polarBilin_apply_apply, ← polarBilin_apply_apply,
      map_sum (polarBilin Q₁ (f₁ a)), map_sum (polarBilin Q₂ (f₂ a))]
    congr 1
    refine Finset.sum_congr rfl fun j hj => ?_
    rw [polarBilin_apply_apply, polarBilin_apply_apply]
    exact hB a (Finset.mem_insert_self a s) j (Finset.mem_insert_of_mem hj)
      (fun h => ha (h ▸ hj))

theorem quad_sum_smul_eq_of_gram {M₁ M₂ : Type*} [AddCommGroup M₁] [Module F M₁]
    [AddCommGroup M₂] [Module F M₂] (Q₁ : QuadraticForm F M₁) (Q₂ : QuadraticForm F M₂)
    (w₁ : ι → M₁) (w₂ : ι → M₂) (hQ : ∀ i, Q₁ (w₁ i) = Q₂ (w₂ i))
    (hB : ∀ i j, i ≠ j → polar Q₁ (w₁ i) (w₁ j) = polar Q₂ (w₂ i) (w₂ j)) (v : ι → F) :
    Q₁ (∑ i, v i • w₁ i) = Q₂ (∑ i, v i • w₂ i) := by
  refine quad_sum_eq_of_gram Q₁ Q₂ _ _ _ (fun i _ => ?_) (fun i _ j _ hij => ?_)
  · rw [QuadraticMap.map_smul, QuadraticMap.map_smul, hQ i]
  · rw [polar_smul_left, polar_smul_right, polar_smul_left, polar_smul_right, hB i j hij]

theorem eq_sum_smul_single (v : ι → F) : v = ∑ l, v l • Pi.single l (1 : F) := by
  funext s
  simp [Finset.sum_apply, Pi.single_apply]

end Gram

section Stated

variable {F : Type} [Field F] {m : ℕ}

theorem polar_quadPlus_eq_sum (u u' : Fin m ⊕ Fin m → F) :
    polar (quadPlus m F) u u' = ∑ s, u (Sum.swap s) * u' s := by
  simp only [QuadraticMap.polar, quadPlus_apply, Pi.add_apply, Fintype.sum_sum_type, Sum.swap_inl,
    Sum.swap_inr]
  rw [← Finset.sum_sub_distrib, ← Finset.sum_sub_distrib, ← Finset.sum_add_distrib]
  exact Finset.sum_congr rfl fun i _ => by ring

theorem quadPlus_single (s : Fin m ⊕ Fin m) : quadPlus m F (Pi.single s 1) = 0 := by
  rcases s with k | k <;> simp [quadPlus_apply, Pi.single_apply]

theorem polar_quadPlus_single (l l' : Fin m ⊕ Fin m) :
    polar (quadPlus m F) (Pi.single l 1) (Pi.single l' 1) = if l' = Sum.swap l then 1 else 0 := by
  rw [polar_quadPlus_eq_sum, Finset.sum_eq_single l']
  · simp only [Pi.single_eq_same, mul_one, Pi.single_apply]
    by_cases h : l' = Sum.swap l
    · have h' : Sum.swap l' = l := by rw [h, Sum.swap_swap]
      simp [h, h']
    · have h' : Sum.swap l' ≠ l := fun h' => h (by rw [← h', Sum.swap_swap])
      simp [h, h']
  · intro s _ hs
    rw [Pi.single_eq_of_ne hs, mul_zero]
  · intro h
    exact absurd (Finset.mem_univ l') h

theorem exists_gl_of_hypBasis (w : Fin m ⊕ Fin m → Fin m ⊕ Fin m → F)
    (hQ : ∀ l, quadPlus m F (w l) = 0)
    (hB : ∀ l l', polar (quadPlus m F) (w l) (w l') = if l' = Sum.swap l then 1 else 0) :
    ∃ P : GL (Fin m ⊕ Fin m) F, (∀ s l, (P : Matrix (Fin m ⊕ Fin m) (Fin m ⊕ Fin m) F) s l = w l s) ∧
      P ∈ isometryClosure F m := by
  set P : Matrix (Fin m ⊕ Fin m) (Fin m ⊕ Fin m) F := Matrix.of fun s l => w l s with hP
  set P' : Matrix (Fin m ⊕ Fin m) (Fin m ⊕ Fin m) F :=
    Matrix.of fun l s => w (Sum.swap l) (Sum.swap s) with hP'
  have h1 : P' * P = 1 := by
    ext l l'
    have h := hB (Sum.swap l) l'
    rw [polar_quadPlus_eq_sum] at h
    rw [Matrix.mul_apply, Matrix.one_apply]
    simp only [hP, hP', Matrix.of_apply]
    rw [h, Sum.swap_swap]
    by_cases hl : l = l'
    · simp [hl]
    · simp [hl, Ne.symm hl]
  have h2 : P * P' = 1 := mul_eq_one_comm.mp h1
  refine ⟨⟨P, P', h2, h1⟩, fun s l => rfl, Subgroup.subset_closure fun v => ?_⟩
  have hPv : P *ᵥ v = ∑ l, v l • w l := by
    funext s
    simp [hP, Matrix.mulVec, dotProduct, Finset.sum_apply, mul_comm]
  change StatedQuadPlus m F (P *ᵥ v) = StatedQuadPlus m F v
  rw [hPv, ← coe_quadPlus]
  conv_rhs => rw [eq_sum_smul_single v]
  refine quad_sum_smul_eq_of_gram _ _ _ _ (fun l => by rw [hQ, quadPlus_single])
    (fun l l' _ => by rw [hB, polar_quadPlus_single]) v

theorem inv_mul_mul_eq_of_eigen {ι : Type*} [Fintype ι] [DecidableEq ι] (P M D : GL ι F)
    (μ : ι → F) (hD : (D : Matrix ι ι F) = diagonal μ)
    (h : ∀ l, (M : Matrix ι ι F) *ᵥ (fun s => (P : Matrix ι ι F) s l) =
      μ l • fun s => (P : Matrix ι ι F) s l) :
    P⁻¹ * M * P = D := by
  have hMP : M * P = P * D := by
    apply Units.ext
    ext s l
    rw [Units.val_mul, Units.val_mul, hD, Matrix.mul_diagonal, Matrix.mul_apply]
    have := congrFun (h l) s
    simp only [Matrix.mulVec, dotProduct, Pi.smul_apply, smul_eq_mul] at this
    rw [this, mul_comm]
  rw [mul_assoc, hMP, ← mul_assoc, inv_mul_cancel, one_mul]

end Stated

end CFSG.SeitzReduction.OmegaPilot
