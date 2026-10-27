module

public import CFSG.HardMathSupport.Solomon.Coordinator.ChevQ.KernelPosNormalize
public import CFSG.HardMathSupport.Solomon.Coordinator.ChevQ.E8NonToralDefs

public noncomputable section

namespace CFSG.HardMathSupport.Solomon.Coordinator.ChevQ.E8NonToral

open CFSG.Blueprint CFSG.Blueprint.Chevalley CFSG.LieType.Chevalley CFSG.LieType.Steinberg.Adjoint
  CFSG.HardMathSupport.Timmesfeld.Torality CFSG.LocalAnalysis.ComponentInitial.FourGroupChevalley

section Generic

variable
  {τ : Tag} {K : Type} [Field K] {ι : Type}

theorem exists_kernelWeyl_conj_posStable (a : ι → Fin τ.rank → Kˣ) {u : WeylGroup τ}
    (hustab : ∀ γ ∈ familyKernel a, u • γ ∈ familyKernel a) (hu3 : u ^ 3 = 1)
    (hsum : ∀ γ ∈ familyKernel a, γ + u • γ + u ^ 2 • γ ≠ 0) :
    ∃ ρ ∈ Subgroup.closure (rootReflection '' familyKernel a),
      KernelPosStable a (ρ * u * ρ⁻¹) := by
  have hker : kernelRoots (familyChar a) = familyKernel a := kernelRoots_familyChar a
  obtain ⟨ρ, hρ, h⟩ := KernelPos.exists_conj_smul_mem_posRoots (χ := familyChar a)
    (by rw [hker]; exact hustab) hu3 (by rw [hker]; exact hsum)
  refine ⟨ρ, ?_, fun γ hγ hpos => ?_⟩
  · rw [← hker, ← kernelWeylGroup_eq_closure]
    exact hρ
  · rw [hker] at h
    exact h γ ⟨hγ, hpos⟩

theorem exists_kernelWeyl_mul_posStable (a : ι → Fin τ.rank → Kˣ) {x : WeylGroup τ}
    (hx : (fun α => x • α) '' familyKernel a = familyKernel a) :
    ∃ ρ ∈ Subgroup.closure (rootReflection '' familyKernel a), KernelPosStable a (ρ * x) := by
  have hker : kernelRoots (familyChar a) = familyKernel a := kernelRoots_familyChar a
  obtain ⟨ρ, hρ, h⟩ := KernelPos.exists_mul_smul_mem_posRoots (χ := familyChar a)
    (by rw [hker]; exact hx)
  refine ⟨ρ, ?_, fun γ hγ hpos => ?_⟩
  · rw [← hker, ← kernelWeylGroup_eq_closure]
    exact hρ
  · rw [hker] at h
    exact h γ ⟨hγ, hpos⟩

end Generic

section Orth

variable
  {L : Type} [Field L]

theorem orbitSum_ne_zero_of_e8D4OrthOrbit {a : Fin 2 → Fin Tag.E8.rank → Lˣ}
    {w : WeylGroup Tag.E8} (hw3 : w ^ 3 = 1) (h : E8D4OrthOrbit a w) :
    ∀ γ ∈ familyKernel a, γ + w • γ + w ^ 2 • γ ≠ 0 := fun γ hγ =>
  KernelPos.orbitSum_ne_zero_of_fixed_or_orth hw3 hγ.1 (h.2.1 γ hγ)

end Orth

end CFSG.HardMathSupport.Solomon.Coordinator.ChevQ.E8NonToral

end
