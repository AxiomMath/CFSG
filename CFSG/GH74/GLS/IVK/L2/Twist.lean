module

public import CFSG.GH74.GLS.IVK.L2.Transport

public section

namespace CFSG.GH74.GLS.IVK

variable {F : Type} [Field F] [Finite F] {K : Type} [Group K]

@[expose] def twistEquiv (e : K ≃* L2 F) (α : MulAut K) : K ≃* L2 F := α.trans e

omit [Finite F] in
theorem toPSL_twist (e : K ≃* L2 F) (α : MulAut K) (k : K) :
    toPSL (twistEquiv e α) k = toPSL e (α k) := rfl

omit [Finite F] in
theorem fieldAutHom_twist (e : K ≃* L2 F) (α : MulAut K) (σ : F ≃+* F) :
    fieldAutHom (twistEquiv e α) σ = α⁻¹ * fieldAutHom e σ * α := by
  ext k
  apply α.injective
  apply (toPSL e).injective
  have h1 := toPSL_fieldAutHom (twistEquiv e α) σ k
  have h2 := toPSL_fieldAutHom e σ (α k)
  rw [toPSL_twist, toPSL_twist] at h1
  have h3 : α ((α⁻¹ * fieldAutHom e σ * α) k) = fieldAutHom e σ (α k) := by
    simp [MulAut.mul_apply]
  rw [h3, h2]
  exact h1

end CFSG.GH74.GLS.IVK
