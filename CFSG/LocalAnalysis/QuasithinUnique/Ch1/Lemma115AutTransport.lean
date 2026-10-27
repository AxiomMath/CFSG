module

public import CFSG.LocalAnalysis.QuasithinUnique.Ch1.Lemma115Datum

public section

namespace CFSG.QuasithinUnique.Ch1

open CFSG.ComponentClassification.OuterAutomorphisms

variable {K : Type} {N : Type*} [Group K] [Group N]

@[expose] def transAut (ψ : K ≃* N) (β : K ≃* K) : MulAut N := (ψ.symm.trans β).trans ψ

theorem transAut_apply (ψ : K ≃* N) (β : K ≃* K) (x : K) : transAut ψ β (ψ x) = ψ (β x) := by
  simp [transAut]

theorem isInnerAut_of_transAut_mem_inner (ψ : K ≃* N) (β : K ≃* K)
    (h : transAut ψ β ∈ inner N) : IsInnerAut β := by
  obtain ⟨g, hg⟩ := h
  refine ⟨ψ.symm g⁻¹, fun x => ?_⟩
  apply ψ.injective
  have h1 := congrArg (fun f : MulAut N => f (ψ x)) hg
  simp only [MulAut.conj_apply, transAut_apply] at h1
  rw [← h1]
  simp [map_mul, map_inv]

theorem transAut_mul_self (ψ : K ≃* N) (β : K ≃* K) (hβ : ∀ x, β (β x) = x) :
    transAut ψ β * transAut ψ β = 1 := by
  ext y
  obtain ⟨x, rfl⟩ := ψ.surjective y
  simp [MulAut.mul_apply, transAut_apply, hβ]

end CFSG.QuasithinUnique.Ch1
