module

public import CFSG.ClassicalInvolution.ModelFacts.ClassicalIsFundamentalTrialityD4CubeOrbit
public import CFSG.LieType.Chevalley.RationalToralSignDiagramCheck

public section

namespace CFSG.ClassicalInvolution.ModelFacts

open CFSG.Blueprint.Chevalley CFSG.LieType.Chevalley CFSG.LieType.Chevalley.ToralSign
  CFSG.LieType.Steinberg.Adjoint

section Check

variable {τ : Tag} (C : RootCertificate τ)

@[expose] def orthogonalKernelCheck (m : ℕ) : Bool :=
  (List.range C.roots.length).all fun k => !inKernel C m k ||
    (List.range C.roots.length).all fun k' => !inKernel C m k' ||
      decide (C.root k' = C.root k) || decide (C.root k' = -C.root k) ||
        decide (cpair (C.root k) (C.root k') = 0)

variable {C}

theorem orthogonal_of_check (hC : C.check = true) (hS : τ.symmetrizedCartan = τ.cartan) {m : ℕ}
    (h : orthogonalKernelCheck C m = true) :
    ∀ α ∈ kernelRoots (signMaskChar τ m), ∀ β ∈ kernelRoots (signMaskChar τ m),
      β = α ∨ β = -α ∨ iform α β = 0 := by
  intro α hα β hβ
  obtain ⟨k, hk, rfl, hker⟩ := (mem_kernelRoots_iff hC).1 hα
  obtain ⟨k', hk', rfl, hker'⟩ := (mem_kernelRoots_iff hC).1 hβ
  simp only [orthogonalKernelCheck, List.all_eq_true, List.mem_range, Bool.or_eq_true,
    Bool.not_eq_true', decide_eq_true_eq] at h
  rcases h k hk with h0 | h1
  · rw [hker] at h0
    exact absurd h0 (by simp)
  rcases h1 k' hk' with ((h0 | h1) | h2) | h3
  · rw [hker'] at h0
    exact absurd h0 (by simp)
  · exact Or.inl h1
  · exact Or.inr (Or.inl h2)
  · exact Or.inr (Or.inr ((iform_eq_cpair hS _ _).trans h3))

end Check

theorem d4_symmetrizedCartan : Tag.D4.symmetrizedCartan = Tag.D4.cartan := by
  change Tag.D4.symmetrizer * Tag.D4.cartan = Tag.D4.cartan
  rw [show Tag.D4.symmetrizer = 1 from rfl, one_mul]

theorem d4_orthogonalCheck_four : orthogonalKernelCheck d4Certificate 4 = true := by
  decide +kernel

theorem d4_orthogonal_four :
    ∀ α ∈ kernelRoots (signMaskChar Tag.D4 4), ∀ β ∈ kernelRoots (signMaskChar Tag.D4 4),
      β = α ∨ β = -α ∨ iform α β = 0 :=
  orthogonal_of_check d4Certificate_check d4_symmetrizedCartan d4_orthogonalCheck_four

theorem d4_hclass_four (a b : kernelRoots (signMaskChar Tag.D4 4))
    (hab : (⟦a⟧ : KernelComponent (signMaskChar Tag.D4 4)) = ⟦b⟧) :
    (b : Fin Tag.D4.rank → ℤ) = a ∨ (b : Fin Tag.D4.rank → ℤ) = -a :=
  hclass_of_orthogonal d4_orthogonal_four a b hab

end CFSG.ClassicalInvolution.ModelFacts
