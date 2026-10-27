module

public import CFSG.ClassicalGroups.Symplectic.StandardForm

public section

namespace CFSG.ClassicalGroups.Symplectic

open CFSG.Open Matrix

variable {m : ℕ} {K : Type} [Field K] [Finite K] [CharP K 2]

theorem eq_of_tensor_eq (hm : 1 ≤ m) {E : Type*} [AddCommGroup E] [Module K E]
    {W₁ W₂ : Submodule K E} (hdisj : W₁ ⊓ W₂ = ⊥)
    (e₁ : W₁ ≃ₗ[K] (Fin m ⊕ Fin m → K)) (e₂ : W₂ ≃ₗ[K] (Fin m ⊕ Fin m → K))
    {s s' : GL (Fin m ⊕ Fin m) K} (hs : s ∈ StatedSp m K) (hs' : s' ∈ StatedSp m K)
    {h₁₁ h₁₂ h₂₁ h₂₂ h₁₁' h₁₂' h₂₁' h₂₂' : K}
    (h₁ : ∀ x : Fin m ⊕ Fin m → K,
      ((e₁.symm (h₁₁ • ((s : Matrix (Fin m ⊕ Fin m) (Fin m ⊕ Fin m) K) *ᵥ x)) : W₁) : E) +
        ((e₂.symm (h₂₁ • ((s : Matrix (Fin m ⊕ Fin m) (Fin m ⊕ Fin m) K) *ᵥ x)) : W₂) : E) =
      ((e₁.symm (h₁₁' • ((s' : Matrix (Fin m ⊕ Fin m) (Fin m ⊕ Fin m) K) *ᵥ x)) : W₁) : E) +
        ((e₂.symm (h₂₁' • ((s' : Matrix (Fin m ⊕ Fin m) (Fin m ⊕ Fin m) K) *ᵥ x)) : W₂) : E))
    (h₂ : ∀ x : Fin m ⊕ Fin m → K,
      ((e₁.symm (h₁₂ • ((s : Matrix (Fin m ⊕ Fin m) (Fin m ⊕ Fin m) K) *ᵥ x)) : W₁) : E) +
        ((e₂.symm (h₂₂ • ((s : Matrix (Fin m ⊕ Fin m) (Fin m ⊕ Fin m) K) *ᵥ x)) : W₂) : E) =
      ((e₁.symm (h₁₂' • ((s' : Matrix (Fin m ⊕ Fin m) (Fin m ⊕ Fin m) K) *ᵥ x)) : W₁) : E) +
        ((e₂.symm (h₂₂' • ((s' : Matrix (Fin m ⊕ Fin m) (Fin m ⊕ Fin m) K) *ᵥ x)) : W₂) : E))
    (hne : h₁₁ ≠ 0 ∨ h₁₂ ≠ 0 ∨ h₂₁ ≠ 0 ∨ h₂₂ ≠ 0) :
    s = s' ∧ h₁₁ = h₁₁' ∧ h₁₂ = h₁₂' ∧ h₂₁ = h₂₁' ∧ h₂₂ = h₂₂' := by
  classical
  have key : ∀ a a' b b' : Fin m ⊕ Fin m → K,
      ((e₁.symm a : W₁) : E) + ((e₂.symm b : W₂) : E) =
        ((e₁.symm a' : W₁) : E) + ((e₂.symm b' : W₂) : E) → a = a' ∧ b = b' := by
    intro a a' b b' hab
    have hsum : ((e₁.symm (a - a') : W₁) : E) + ((e₂.symm (b - b') : W₂) : E) = 0 := by
      rw [map_sub, map_sub, Submodule.coe_sub, Submodule.coe_sub]
      calc _ = (((e₁.symm a : W₁) : E) + ((e₂.symm b : W₂) : E)) -
            (((e₁.symm a' : W₁) : E) + ((e₂.symm b' : W₂) : E)) := by abel
        _ = 0 := sub_eq_zero.mpr hab
    have hmem : ((e₁.symm (a - a') : W₁) : E) ∈ W₁ ⊓ W₂ := ⟨(e₁.symm (a - a')).2, by
      have : ((e₁.symm (a - a') : W₁) : E) = -((e₂.symm (b - b') : W₂) : E) :=
        eq_neg_of_add_eq_zero_left hsum
      rw [this]
      exact W₂.neg_mem (e₂.symm (b - b')).2⟩
    rw [hdisj, Submodule.mem_bot] at hmem
    have h1 : a - a' = 0 := by
      have : e₁.symm (a - a') = 0 := Subtype.ext hmem
      exact (LinearEquiv.map_eq_zero_iff e₁.symm).mp this
    have h2 : b - b' = 0 := by
      have h3 : ((e₂.symm (b - b') : W₂) : E) = 0 := by
        rw [hmem, zero_add] at hsum
        exact hsum
      have : e₂.symm (b - b') = 0 := Subtype.ext h3
      exact (LinearEquiv.map_eq_zero_iff e₂.symm).mp this
    exact ⟨sub_eq_zero.mp h1, sub_eq_zero.mp h2⟩
  have c1 : ∀ x : Fin m ⊕ Fin m → K,
      h₁₁ • ((s : Matrix (Fin m ⊕ Fin m) (Fin m ⊕ Fin m) K) *ᵥ x) =
        h₁₁' • ((s' : Matrix (Fin m ⊕ Fin m) (Fin m ⊕ Fin m) K) *ᵥ x) ∧
      h₂₁ • ((s : Matrix (Fin m ⊕ Fin m) (Fin m ⊕ Fin m) K) *ᵥ x) =
        h₂₁' • ((s' : Matrix (Fin m ⊕ Fin m) (Fin m ⊕ Fin m) K) *ᵥ x) :=
    fun x => key _ _ _ _ (h₁ x)
  have c2 : ∀ x : Fin m ⊕ Fin m → K,
      h₁₂ • ((s : Matrix (Fin m ⊕ Fin m) (Fin m ⊕ Fin m) K) *ᵥ x) =
        h₁₂' • ((s' : Matrix (Fin m ⊕ Fin m) (Fin m ⊕ Fin m) K) *ᵥ x) ∧
      h₂₂ • ((s : Matrix (Fin m ⊕ Fin m) (Fin m ⊕ Fin m) K) *ᵥ x) =
        h₂₂' • ((s' : Matrix (Fin m ⊕ Fin m) (Fin m ⊕ Fin m) K) *ᵥ x) :=
    fun x => key _ _ _ _ (h₂ x)
  let i0 : Fin m := ⟨0, hm⟩
  let x₀ : Fin m ⊕ Fin m → K := Pi.single (Sum.inl i0) 1
  let y₀ : Fin m ⊕ Fin m → K := Pi.single (Sum.inr i0) 1
  have h0 : spForm m K x₀ y₀ = 1 := by rw [spForm_single_inl_inr]; simp
  have hss : ∀ l l' : K, l ≠ 0 →
      (∀ x : Fin m ⊕ Fin m → K, l • ((s : Matrix (Fin m ⊕ Fin m) (Fin m ⊕ Fin m) K) *ᵥ x) =
        l' • ((s' : Matrix (Fin m ⊕ Fin m) (Fin m ⊕ Fin m) K) *ᵥ x)) → s = s' ∧ l = l' := by
    intro l l' hl hx
    have hsc : ∀ x : Fin m ⊕ Fin m → K,
        (s : Matrix (Fin m ⊕ Fin m) (Fin m ⊕ Fin m) K) *ᵥ x =
          (l⁻¹ * l') • ((s' : Matrix (Fin m ⊕ Fin m) (Fin m ⊕ Fin m) K) *ᵥ x) := by
      intro x
      rw [mul_smul, ← hx x, smul_smul, inv_mul_cancel₀ hl, one_smul]
    have hc2 : (l⁻¹ * l') * (l⁻¹ * l') = 1 := by
      have e1 := (mem_statedSp_iff_forall s).mp hs x₀ y₀
      have e2 := (mem_statedSp_iff_forall s').mp hs' x₀ y₀
      rw [hsc x₀, hsc y₀, LinearMap.map_smul₂, map_smul, smul_eq_mul, smul_eq_mul, e2, h0] at e1
      simpa using e1
    have hc1 : l⁻¹ * l' = 1 := by
      have h2c : (2 : K) = 0 := CharTwo.two_eq_zero
      have : (l⁻¹ * l' - 1) * (l⁻¹ * l' - 1) = 0 := by
        linear_combination hc2 + (1 - l⁻¹ * l') * h2c
      exact sub_eq_zero.mp (mul_self_eq_zero.mp this)
    have hll : l = l' := by
      have : l' = l := by
        calc l' = l * (l⁻¹ * l') := by rw [← mul_assoc, mul_inv_cancel₀ hl, one_mul]
          _ = l := by rw [hc1, mul_one]
      exact this.symm
    refine ⟨?_, hll⟩
    apply Units.ext
    ext i j
    have := congrFun (hsc (Pi.single j 1)) i
    rw [hc1, one_smul] at this
    simpa [Matrix.mulVec_single_one] using this
  have hcancel : ∀ μ μ' : K, (∀ x : Fin m ⊕ Fin m → K,
      μ • ((s : Matrix (Fin m ⊕ Fin m) (Fin m ⊕ Fin m) K) *ᵥ x) =
        μ' • ((s : Matrix (Fin m ⊕ Fin m) (Fin m ⊕ Fin m) K) *ᵥ x)) → μ = μ' := by
    intro μ μ' hμ
    have h1 := hμ (((s⁻¹ : GL (Fin m ⊕ Fin m) K) : Matrix (Fin m ⊕ Fin m) (Fin m ⊕ Fin m) K) *ᵥ
      x₀)
    rw [Matrix.mulVec_mulVec, ← Units.val_mul, mul_inv_cancel, Units.val_one,
      Matrix.one_mulVec] at h1
    have := congrFun h1 (Sum.inl i0)
    simpa [x₀] using this
  have hsame : s = s' := by
    rcases hne with h | h | h | h
    · exact (hss h₁₁ h₁₁' h fun x => (c1 x).1).1
    · exact (hss h₁₂ h₁₂' h fun x => (c2 x).1).1
    · exact (hss h₂₁ h₂₁' h fun x => (c1 x).2).1
    · exact (hss h₂₂ h₂₂' h fun x => (c2 x).2).1
  subst hsame
  exact ⟨rfl, hcancel _ _ fun x => (c1 x).1, hcancel _ _ fun x => (c2 x).1,
    hcancel _ _ fun x => (c1 x).2, hcancel _ _ fun x => (c2 x).2⟩

end CFSG.ClassicalGroups.Symplectic

