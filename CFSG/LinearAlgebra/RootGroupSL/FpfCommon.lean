module

public import CFSG.LinearAlgebra.RootGroupSL.Normalizer

public section

namespace CFSG.LinearAlgebra.RootGroupSL

variable {k E X : Type} [Field k] [Field E] [Algebra k E] [AddCommGroup X] [Module k X]

theorem blockDiag_conj_unipElt_eq_iff (a : E ≃ₗ[k] E) (g : X ≃ₗ[k] X) (b : E ≃ₗ[k] E)
    (φ : X →ₗ[k] E) (χ : E →ₗ[k] X) (ψ : E →ₗ[k] E) :
    blockDiag a g b * unipElt φ χ ψ * (blockDiag a g b)⁻¹ = unipElt φ χ ψ ↔
      a.toLinearMap ∘ₗ φ = φ ∘ₗ g.toLinearMap ∧ g.toLinearMap ∘ₗ χ = χ ∘ₗ b.toLinearMap ∧
        a.toLinearMap ∘ₗ ψ = ψ ∘ₗ b.toLinearMap := by
  rw [blockDiag_mul_unipElt_mul_inv, unipElt_inj]
  constructor
  · rintro ⟨h1, h2, h3⟩
    refine ⟨?_, ?_, ?_⟩
    · ext x
      have h := congrArg (fun f : X →ₗ[k] E => f (g x)) h1
      simpa [LinearMap.comp_apply] using h
    · ext y
      have h := congrArg (fun f : E →ₗ[k] X => f (b y)) h2
      simpa [LinearMap.comp_apply] using h
    · ext y
      have h := congrArg (fun f : E →ₗ[k] E => f (b y)) h3
      simpa [LinearMap.comp_apply] using h
  · rintro ⟨h1, h2, h3⟩
    refine ⟨?_, ?_, ?_⟩
    · ext x
      have h := congrArg (fun f : X →ₗ[k] E => f (g.symm x)) h1
      simpa [LinearMap.comp_apply] using h
    · ext y
      have h := congrArg (fun f : E →ₗ[k] X => f (b.symm y)) h2
      simpa [LinearMap.comp_apply] using h
    · ext y
      have h := congrArg (fun f : E →ₗ[k] E => f (b.symm y)) h3
      simpa [LinearMap.comp_apply] using h

lemma blockDiag_pow (a : E ≃ₗ[k] E) (g : X ≃ₗ[k] X) (b : E ≃ₗ[k] E) (n : ℕ) :
    (blockDiag a g b) ^ n = blockDiag (a ^ n) (g ^ n) (b ^ n) := by
  induction n with
  | zero => simp [blockDiag_one]
  | succ n ih => rw [pow_succ, ih, blockDiag_mul, ← pow_succ, ← pow_succ, ← pow_succ]

variable [Finite k] [Finite E] [Module.Finite k X] [CharP k 2]

lemma blockSL_conj_rootElt (a : E ≃ₗ[k] E) (g : X ≃ₗ[k] X) (b : E ≃ₗ[k] E)
    (hdet : LinearEquiv.det a * LinearEquiv.det g * LinearEquiv.det b = 1) (t : E)
    (hconj : a.toLinearMap ∘ₗ LinearMap.mulLeft k t ∘ₗ b.symm.toLinearMap =
      LinearMap.mulLeft k t) :
    blockSL a g b hdet * rootElt k X t * (blockSL a g b hdet)⁻¹ = rootElt k X t := by
  apply Subtype.ext
  change blockDiag a g b * rootEquiv k X t * (blockDiag a g b)⁻¹ = rootEquiv k X t
  rw [rootEquiv, blockDiag_mul_shearE_mul_inv, hconj]

lemma blockDiag_conj_of_centralizer {h g' : SpecialLinearGroup k (DSpace E X)}
    (hcent : h * g' * h⁻¹ = g')
    {a : E ≃ₗ[k] E} {g : X ≃ₗ[k] X} {b : E ≃ₗ[k] E}
    (hh : (h : DSpace E X ≃ₗ[k] DSpace E X) = blockDiag a g b)
    {φ : X →ₗ[k] E} {χ : E →ₗ[k] X} {ψ : E →ₗ[k] E}
    (hg' : (g' : DSpace E X ≃ₗ[k] DSpace E X) = unipElt φ χ ψ) :
    blockDiag a g b * unipElt φ χ ψ * (blockDiag a g b)⁻¹ = unipElt φ χ ψ := by
  have h := congrArg (fun z : SpecialLinearGroup k (DSpace E X) =>
    (z : DSpace E X ≃ₗ[k] DSpace E X)) hcent
  simp only [SpecialLinearGroup.coe_mul, SpecialLinearGroup.coe_inv] at h
  rw [hh, hg'] at h
  simpa using h

end CFSG.LinearAlgebra.RootGroupSL
