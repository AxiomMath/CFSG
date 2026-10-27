module

public import CFSG.LocalAnalysis.ComponentInitial.OrthogonalTailRootData
public import CFSG.LocalAnalysis.ComponentInitial.OrthogonalAnisotropicPlaneRegular

public noncomputable section

namespace CFSG.LocalAnalysis.ComponentInitial.OrthogonalTail

open QuadraticMap CFSG.ClassicalGroups.Orthogonal CFSG.LieType.Universal.Spin Module

variable {K : Type*} [Field K]

section Equiv

@[expose] def tailModelEquiv (r : ℕ) (K : Type*) [Field K] (κ : Type*) :
    ((Fin r ⊕ Fin r → K) × (κ → K)) ≃ₗ[K] (Fin r ⊕ Fin r ⊕ κ → K) where
  toFun v := Sum.elim (fun i => v.1 (.inl i)) (Sum.elim (fun i => v.1 (.inr i)) v.2)
  invFun w := (Sum.elim (fun i => w (.inl i)) (fun i => w (.inr (.inl i))),
    fun j => w (.inr (.inr j)))
  map_add' v w := by
    funext x
    rcases x with i | i | j <;> rfl
  map_smul' c v := by
    funext x
    rcases x with i | i | j <;> rfl
  left_inv v := by
    refine Prod.ext (funext fun x => ?_) rfl
    rcases x with i | i <;> rfl
  right_inv w := by
    funext x
    rcases x with i | i | j <;> rfl

variable {r : ℕ} {κ : Type*}

theorem tailModelEquiv_inl (v : (Fin r ⊕ Fin r → K) × (κ → K)) (i : Fin r) :
    tailModelEquiv r K κ v (.inl i) = v.1 (.inl i) :=
  rfl

theorem tailModelEquiv_inr_inl (v : (Fin r ⊕ Fin r → K) × (κ → K)) (i : Fin r) :
    tailModelEquiv r K κ v (.inr (.inl i)) = v.1 (.inr i) :=
  rfl

theorem tailModelEquiv_inr_inr (v : (Fin r ⊕ Fin r → K) × (κ → K)) (j : κ) :
    tailModelEquiv r K κ v (.inr (.inr j)) = v.2 j :=
  rfl

theorem tailModelEquiv_hypVec_inl [DecidableEq κ] (i : Fin r) :
    tailModelEquiv r K κ (hypVec K (κ → K) (.inl i)) = Pi.single (.inl i) 1 := by
  funext x
  rcases x with j | j | j
  · rw [tailModelEquiv_inl, hypVec]
    by_cases h : j = i
    · subst h
      simp
    · simp [h]
  · rw [tailModelEquiv_inr_inl, hypVec]
    simp
  · rw [tailModelEquiv_inr_inr, hypVec]
    simp

end Equiv

section Isometry

variable {r : ℕ} {κ : Type*} {q : QuadraticForm K (κ → K)}
  {Q : QuadraticForm K (Fin r ⊕ Fin r ⊕ κ → K)}

@[expose] def tailModelIsometry
    (hQ : ∀ v, Q v = ∑ i, v (.inl i) * v (.inr (.inl i)) + q (fun j => v (.inr (.inr j)))) :
    (quadTail r q).IsometryEquiv Q where
  toLinearEquiv := tailModelEquiv r K κ
  map_app' v := by
    rw [hQ, quadTail_apply, quadPlus_apply]
    rfl

theorem tailModelIsometry_apply
    (hQ : ∀ v, Q v = ∑ i, v (.inl i) * v (.inr (.inl i)) + q (fun j => v (.inr (.inr j))))
    (v : (Fin r ⊕ Fin r → K) × (κ → K)) :
    tailModelIsometry hQ v = tailModelEquiv r K κ v :=
  rfl

end Isometry

section Odd

variable (K) in
@[expose] def oddTailForm : QuadraticForm K (Unit → K) :=
  LinearMap.BilinMap.toQuadraticMap (LinearMap.mk₂ K (fun a b : Unit → K => a () * b ())
    (fun _ _ _ => by simp [add_mul]) (fun _ _ _ => by simp [mul_assoc])
    (fun _ _ _ => by simp [mul_add]) (fun _ _ _ => by simp [mul_left_comm]))

theorem oddTailForm_apply (a : Unit → K) : oddTailForm K a = a () ^ 2 := by
  simp only [oddTailForm, LinearMap.BilinMap.toQuadraticMap_apply, LinearMap.mk₂_apply]
  ring

theorem polar_oddTailForm (a b : Unit → K) : polar (oddTailForm K) a b = 2 * (a () * b ()) := by
  rw [oddTailForm, LinearMap.BilinMap.polar_toQuadraticMap]
  simp only [LinearMap.mk₂_apply]
  ring

theorem anisotropic_oddTailForm : (oddTailForm K).Anisotropic := fun a ha => by
  rw [oddTailForm_apply, pow_eq_zero_iff two_ne_zero] at ha
  funext u
  exact ha

theorem nondegenerate_oddTailForm (h2 : (2 : K) ≠ 0) :
    (polarBilin (oddTailForm K)).Nondegenerate := by
  refine nondegenerate_polarBilin_of_forall fun a ha => funext fun u => ?_
  have h := ha fun _ => 1
  rw [polar_oddTailForm, mul_one] at h
  exact (mul_eq_zero.1 h).resolve_left h2

theorem finrank_unit_fun : finrank K (Unit → K) = 1 := by
  simp

@[expose] def oddTailIsometry (n : ℕ) (K : Type*) [Field K] :
    (quadTail n (oddTailForm K)).IsometryEquiv (quadOdd n K) :=
  tailModelIsometry fun v => by rw [quadOdd_apply, oddTailForm_apply]

end Odd

section Minus

variable (K) in
@[expose] def minusTailForm (b c : K) : QuadraticForm K (Fin 2 → K) :=
  LinearMap.BilinMap.toQuadraticMap
    (LinearMap.mk₂ K (fun a a' : Fin 2 → K => a 0 * a' 0 + b * a 0 * a' 1 + c * a 1 * a' 1)
      (fun _ _ _ => by simp only [Pi.add_apply]; ring)
      (fun _ _ _ => by simp only [Pi.smul_apply, smul_eq_mul]; ring)
      (fun _ _ _ => by simp only [Pi.add_apply]; ring)
      (fun _ _ _ => by simp only [Pi.smul_apply, smul_eq_mul]; ring))

theorem minusTailForm_apply (b c : K) (a : Fin 2 → K) :
    minusTailForm K b c a = a 0 ^ 2 + b * a 0 * a 1 + c * a 1 ^ 2 := by
  simp only [minusTailForm, LinearMap.BilinMap.toQuadraticMap_apply, LinearMap.mk₂_apply]
  ring

theorem anisotropic_minusTailForm {b c : K} (hirr : ∀ s : K, s ^ 2 + b * s + c ≠ 0) :
    (minusTailForm K b c).Anisotropic := fun a ha => by
  rw [minusTailForm_apply] at ha
  by_cases h1 : a 1 = 0
  · have h0 : a 0 = 0 := by
      rw [h1] at ha
      have : a 0 ^ 2 = 0 := by linear_combination ha
      exact pow_eq_zero_iff two_ne_zero |>.1 this
    funext j
    fin_cases j
    · exact h0
    · exact h1
  · exfalso
    apply hirr (a 0 / a 1)
    field_simp
    linear_combination ha

theorem finrank_fin_two_fun : finrank K (Fin 2 → K) = 2 := by
  simp

theorem nondegenerate_minusTailForm [Finite K] {b c : K}
    (hirr : ∀ s : K, s ^ 2 + b * s + c ≠ 0) : (polarBilin (minusTailForm K b c)).Nondegenerate :=
  finite_anisotropic_plane_regular finrank_fin_two_fun.ge fun a ha =>
    fun h => ha (anisotropic_minusTailForm hirr a h)

@[expose] def minusTailIsometry (n : ℕ) (K : Type*) [Field K] (b c : K) :
    (quadTail (n - 1) (minusTailForm K b c)).IsometryEquiv (quadMinus n K b c) :=
  tailModelIsometry fun v => by
    rw [quadMinus_apply, minusTailForm_apply]
    ring

end Minus

end CFSG.LocalAnalysis.ComponentInitial.OrthogonalTail
