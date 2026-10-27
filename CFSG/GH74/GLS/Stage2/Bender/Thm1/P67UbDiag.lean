module

public import CFSG.ClassicalGroups.Unitary.Form

public section

namespace CFSG.GH74.GLS.Stage2.Bender.Thm1.Ub

open CFSG.LieType.Universal.Unitary CFSG.ClassicalGroups.Unitary

variable {K : Type*} [Field K] {σ : K ≃+* K} {n : ℕ}

structure DiagOn (σ : K ≃+* K) {n : ℕ} (x : SUid σ n) (e₁ f₁ e₂ f₂ z : Fin n → K) (α β : K) :
    Prop where
  e1 : x • e₁ = α • e₁
  f1 : x • f₁ = α⁻¹ • f₁
  e2 : x • e₂ = β • e₂
  f2 : x • f₂ = β⁻¹ • f₂
  z : x • z = z

variable {e₁ f₁ e₂ f₂ z : Fin n → K}

theorem DiagOn.one : DiagOn σ (1 : SUid σ n) e₁ f₁ e₂ f₂ z 1 1 := by
  refine ⟨?_, ?_, ?_, ?_, ?_⟩ <;> simp

theorem DiagOn.mul {x y : SUid σ n} {α β α' β' : K} (hx : DiagOn σ x e₁ f₁ e₂ f₂ z α β)
    (hy : DiagOn σ y e₁ f₁ e₂ f₂ z α' β') : DiagOn σ (x * y) e₁ f₁ e₂ f₂ z (α * α') (β * β') := by
  refine ⟨?_, ?_, ?_, ?_, ?_⟩
  · rw [mul_smul, hy.e1, smul_comm x α' e₁, hx.e1, smul_smul, mul_comm]
  · rw [mul_smul, hy.f1, smul_comm x α'⁻¹ f₁, hx.f1, smul_smul, mul_inv, mul_comm]
  · rw [mul_smul, hy.e2, smul_comm x β' e₂, hx.e2, smul_smul, mul_comm]
  · rw [mul_smul, hy.f2, smul_comm x β'⁻¹ f₂, hx.f2, smul_smul, mul_inv, mul_comm]
  · rw [mul_smul, hy.z, hx.z]

theorem DiagOn.pow {x : SUid σ n} {α β : K} (hx : DiagOn σ x e₁ f₁ e₂ f₂ z α β) (m : ℕ) :
    DiagOn σ (x ^ m) e₁ f₁ e₂ f₂ z (α ^ m) (β ^ m) := by
  induction m with
  | zero => simpa using (DiagOn.one (σ := σ) (e₁ := e₁) (f₁ := f₁) (e₂ := e₂) (f₂ := f₂) (z := z))
  | succ m ih => simpa [pow_succ] using ih.mul hx

end CFSG.GH74.GLS.Stage2.Bender.Thm1.Ub
