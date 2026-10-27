module

public import Certificates.Certificate3260
public import Mathlib.RingTheory.PiTensorProduct
public import Mathlib.Tactic.Polynomial.Basic

public section

namespace CFSG.EvenSmallLie.UnitarySix.YamadaD

open CFSG.EvenSmallLie.UnitarySix.YamadaPar Matrix

section Cert

theorem wedgeCheckNW_eq_true : wedgeCheckNW = true :=
  Certificates.certificate3260.1

theorem wedgeCheckWW_eq_true : wedgeCheckWW = true :=
  Certificates.certificate3260.2

variable {n m : ℕ} {M : Fin m → Matrix (Fin n) (Fin n) (ZMod 2)} {Q : Array ℕ}

theorem wedgeQ_mul (hM : wedgeCheckWith n m M Q = true) :
    toMat (n * (n * n)) (m * (n * (n * n)) + n * (n * n)) Q * wedgeEq M = 1 := by
  have := toMat_eq_one_of_bIsId hM
  rwa [toMat_bmul, wedgeR, toMat_matBits] at this

theorem wedgeQP_mul (hM : wedgeCheckWith n m M Q = true) :
    (toMat (n * (n * n)) (m * (n * (n * n)) + n * (n * n)) Q).submatrix (eCol n) (eRow n m) *
      wedgeEqP M = 1 := by
  have e : wedgeEqP M = (wedgeEq M).submatrix (eRow n m) (eCol n) := by
    ext ρ c
    simp [wedgeEq, reindex_apply, submatrix_apply]
  rw [e, submatrix_mul_equiv, wedgeQ_mul hM, submatrix_one_equiv]

theorem eq_zero_of_wedgeEqP (hM : wedgeCheckWith n m M Q = true) {c : WCol n → ZMod 2}
    (hc : wedgeEqP M *ᵥ c = 0) : c = 0 := by
  have e := congrArg (· *ᵥ c) (wedgeQP_mul hM)
  simp only [← mulVec_mulVec, hc, mulVec_zero, one_mulVec] at e
  exact e.symm

end Cert

section Bilin

variable {n : ℕ} (β : (Fin n → ZMod 2) → (Fin n → ZMod 2) → (Fin n → ZMod 2))
  (hadd₁ : ∀ x x' y, β (x + x') y = β x y + β x' y)
  (hadd₂ : ∀ x y y', β x (y + y') = β x y + β x y')

include hadd₁ in
theorem bil_zero_left (y : Fin n → ZMod 2) : β 0 y = 0 := by
  have := hadd₁ 0 0 y
  rw [add_zero] at this
  exact (add_eq_left.mp this.symm)

include hadd₂ in
theorem bil_zero_right (x : Fin n → ZMod 2) : β x 0 = 0 := by
  have := hadd₂ x 0 0
  rw [add_zero] at this
  exact (add_eq_left.mp this.symm)

include hadd₁ in
theorem bil_smul_left (a : ZMod 2) (x y : Fin n → ZMod 2) : β (a • x) y = a • β x y := by
  rcases (show ∀ b : ZMod 2, b = 0 ∨ b = 1 by decide) a with rfl | rfl
  · rw [zero_smul, zero_smul, bil_zero_left β hadd₁]
  · rw [one_smul, one_smul]

include hadd₂ in
theorem bil_smul_right (a : ZMod 2) (x y : Fin n → ZMod 2) : β x (a • y) = a • β x y := by
  rcases (show ∀ b : ZMod 2, b = 0 ∨ b = 1 by decide) a with rfl | rfl
  · rw [zero_smul, zero_smul, bil_zero_right β hadd₂]
  · rw [one_smul, one_smul]

include hadd₁ in
theorem bil_sum_left (f : Fin n → Fin n → ZMod 2) (y : Fin n → ZMod 2) :
    β (∑ k, f k) y = ∑ k, β (f k) y := by
  let φ : (Fin n → ZMod 2) →+ (Fin n → ZMod 2) :=
    AddMonoidHom.mk' (fun x => β x y) fun x x' => hadd₁ x x' y
  exact map_sum φ f Finset.univ

include hadd₂ in
theorem bil_sum_right (x : Fin n → ZMod 2) (f : Fin n → Fin n → ZMod 2) :
    β x (∑ l, f l) = ∑ l, β x (f l) := by
  let φ : (Fin n → ZMod 2) →+ (Fin n → ZMod 2) :=
    AddMonoidHom.mk' (fun y => β x y) fun y y' => hadd₂ x y y'
  exact map_sum φ f Finset.univ

include hadd₁ hadd₂ in
theorem bil_expand (x y : Fin n → ZMod 2) :
    β x y = ∑ k, ∑ l, (x k * y l) • β (Pi.single k 1) (Pi.single l 1) := by
  conv_lhs => rw [pi_eq_sum_univ' x, pi_eq_sum_univ' y]
  rw [bil_sum_left β hadd₁]
  refine Finset.sum_congr rfl fun k _ => ?_
  rw [bil_smul_left β hadd₁, bil_sum_right β hadd₂, Finset.smul_sum]
  refine Finset.sum_congr rfl fun l _ => ?_
  rw [bil_smul_right β hadd₂, smul_smul]

end Bilin

section Main

theorem sum_WCol {n : ℕ} (f : WCol n → ZMod 2) : ∑ p, f p = ∑ k, ∑ l, ∑ s, f (k, l, s) := by
  rw [Fintype.sum_prod_type]
  simp only [Fintype.sum_prod_type]

theorem hom_wedge_gen {n m : ℕ} {M : Fin m → Matrix (Fin n) (Fin n) (ZMod 2)} {Q : Array ℕ}
    (hM : wedgeCheckWith n m M Q = true)
    (β : (Fin n → ZMod 2) → (Fin n → ZMod 2) → (Fin n → ZMod 2))
    (hadd₁ : ∀ x x' y, β (x + x') y = β x y + β x' y)
    (hadd₂ : ∀ x y y', β x (y + y') = β x y + β x y') (halt : ∀ x, β x x = 0)
    (hequiv : ∀ (g : Fin m) (x y : Fin n → ZMod 2), β (M g *ᵥ x) (M g *ᵥ y) = M g *ᵥ β x y)
    (x y : Fin n → ZMod 2) : β x y = 0 := by
  have hanti : ∀ k l : Fin n, β (Pi.single k 1) (Pi.single l 1) +
      β (Pi.single l 1) (Pi.single k 1) = 0 := by
    intro k l
    have h1 := halt (Pi.single k 1 + Pi.single l 1)
    rw [hadd₁, hadd₂, hadd₂, halt, halt, zero_add, add_zero] at h1
    exact h1
  set c : WCol n → ZMod 2 := fun p => β (Pi.single p.1 1) (Pi.single p.2.1 1) p.2.2 with hc
  have hc0 : c = 0 := by
    apply eq_zero_of_wedgeEqP hM
    funext ρ
    rcases ρ with ⟨g, i, j, r⟩ | ⟨k₀, l₀, s₀⟩
    · simp only [mulVec, dotProduct, wedgeEqP, Pi.zero_apply]
      rw [sum_WCol]
      simp only [add_mul, Finset.sum_add_distrib, ite_mul, zero_mul, Finset.sum_ite_eq',
        Finset.mem_univ, ite_true, ite_and, Finset.sum_ite_irrel, Finset.sum_const_zero]
      have h1 := congrFun (hequiv g (Pi.single i 1) (Pi.single j 1)) r
      rw [bil_expand β hadd₁ hadd₂] at h1
      simp only [Finset.sum_apply, Pi.smul_apply, smul_eq_mul, mulVec, dotProduct,
        Pi.single_apply, mul_ite, mul_one, mul_zero, Finset.sum_ite_eq', Finset.mem_univ,
        ite_true] at h1
      simp only [hc]
      rw [h1]
      exact CharTwo.add_self_eq_zero _
    · simp only [mulVec, dotProduct, wedgeEqP, Pi.zero_apply]
      rw [sum_WCol]
      simp only [ite_mul, one_mul, zero_mul, ite_and, Finset.sum_ite_eq', Finset.mem_univ,
        ite_true]
      by_cases hkl : k₀ = l₀
      · subst hkl
        simp only [or_self, ite_and, Finset.sum_ite_irrel, Finset.sum_const_zero,
          Finset.sum_ite_eq', Finset.mem_univ, ite_true, hc, halt, Pi.zero_apply]
      · have hsplit : ∀ a b : Fin n,
            (if a = k₀ ∧ b = l₀ ∨ a = l₀ ∧ b = k₀ then c (a, b, s₀) else 0) =
            (if a = k₀ ∧ b = l₀ then c (a, b, s₀) else 0) +
              (if a = l₀ ∧ b = k₀ then c (a, b, s₀) else 0) := by
          intro a b
          by_cases h1 : a = k₀ ∧ b = l₀
          · have h2 : ¬ (a = l₀ ∧ b = k₀) := fun h2 => hkl (h1.1.symm.trans h2.1)
            simp [h1, hkl]
          · by_cases h2 : a = l₀ ∧ b = k₀ <;> simp [h1, h2, hkl, Ne.symm hkl]
        rw [Finset.sum_congr rfl fun a _ => Finset.sum_congr rfl fun b _ => hsplit a b]
        simp only [Finset.sum_add_distrib, ite_and, Finset.sum_ite_irrel,
          Finset.sum_const_zero, Finset.sum_ite_eq', Finset.mem_univ, ite_true, hc]
        simpa using congrFun (hanti k₀ l₀) s₀
  rw [bil_expand β hadd₁ hadd₂]
  refine Finset.sum_eq_zero fun k _ => Finset.sum_eq_zero fun l _ => ?_
  have : β (Pi.single k 1) (Pi.single l 1) = 0 := funext fun s => congrFun hc0 (k, l, s)
  rw [this, smul_zero]
end Main

theorem hom_wedge_N
    (β : (Fin 8 → ZMod 2) → (Fin 8 → ZMod 2) → (Fin 8 → ZMod 2))
    (hadd₁ : ∀ x x' y, β (x + x') y = β x y + β x' y)
    (hadd₂ : ∀ x y y', β x (y + y') = β x y + β x y') (halt : ∀ x, β x x = 0)
    (hequiv : ∀ (g : Fin 5) (x y : Fin 8 → ZMod 2),
      β (wedgeMatN g *ᵥ x) (wedgeMatN g *ᵥ y) = wedgeMatN g *ᵥ β x y)
    (x y : Fin 8 → ZMod 2) : β x y = 0 :=
  hom_wedge_gen wedgeCheckNW_eq_true β hadd₁ hadd₂ halt hequiv x y

theorem hom_wedge_W
    (β : (Fin 4 → ZMod 2) → (Fin 4 → ZMod 2) → (Fin 4 → ZMod 2))
    (hadd₁ : ∀ x x' y, β (x + x') y = β x y + β x' y)
    (hadd₂ : ∀ x y y', β x (y + y') = β x y + β x y') (halt : ∀ x, β x x = 0)
    (hequiv : ∀ (g : Fin 3) (x y : Fin 4 → ZMod 2),
      β (wedgeMatW g *ᵥ x) (wedgeMatW g *ᵥ y) = wedgeMatW g *ᵥ β x y)
    (x y : Fin 4 → ZMod 2) : β x y = 0 :=
  hom_wedge_gen wedgeCheckWW_eq_true β hadd₁ hadd₂ halt hequiv x y

end CFSG.EvenSmallLie.UnitarySix.YamadaD
