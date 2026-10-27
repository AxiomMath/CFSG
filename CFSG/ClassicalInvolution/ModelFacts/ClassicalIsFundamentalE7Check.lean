module

public import CFSG.LieType.Chevalley.OrthogonalUnionBruhat
public import CFSG.LieType.Chevalley.RationalToralSignDiagramCheck

public section

namespace CFSG.ClassicalInvolution.ModelFacts

open CFSG.Blueprint.Chevalley CFSG.LieType.Chevalley CFSG.LieType.Steinberg.Adjoint
  CFSG.LieType.Chevalley.ToralSign

section Classes

variable {τ : Tag} {M : Type*} [CommGroup M] {χ : Multiplicative (Fin τ.rank → ℤ) →* M}

theorem false_of_unionSimpleRoots_eq_singleton
    (hτ : τ = .D4 ∨ τ = .E6 ∨ τ = .E7 ∨ τ = .E8) {J' : Set (KernelComponent χ)}
    {β₀ : Fin τ.rank → ℤ} (h : unionSimpleRoots χ J' = {β₀})
    (hnon : ∀ β ∈ kernelRoots χ, ∃ γ ∈ kernelRoots χ, iform β γ = 1) : False := by
  have hβ₀ : β₀ ∈ unionSimpleRoots χ J' := by rw [h]; exact Set.mem_singleton β₀
  obtain ⟨i, hi, hβ₀i⟩ := hβ₀
  have hβ₀Ψ : β₀ ∈ componentRoots χ i := simpleRoots_subset hβ₀i
  obtain ⟨hβ₀K, hclass⟩ := hβ₀Ψ
  obtain ⟨γ, hγK, hγ⟩ := hnon β₀ hβ₀K
  have hsame : (⟦⟨γ, hγK⟩⟧ : KernelComponent χ) = i := by
    rw [← hclass]
    refine mk_eq_of_iform_ne_zero ?_
    change iform γ β₀ ≠ 0
    rw [iform_comm, hγ]
    exact one_ne_zero
  have hγΨ : γ ∈ componentRoots χ i := ⟨hγK, hsame⟩
  have hsimple : ∀ β ∈ simpleRoots (componentRoots χ i), β = β₀ := fun β hβ => by
    have : β ∈ unionSimpleRoots χ J' := ⟨i, hi, hβ⟩
    rwa [h, Set.mem_singleton_iff] at this
  obtain ⟨w, hw, β, hβ, hγw⟩ := exists_smul_simpleRoot (isRootComponent_componentRoots i) hγΨ
  obtain rfl := hsimple β hβ
  have hr : IsRoot τ β := simpleRoots_isRoot hβ
  have hW : ∀ w ∈ componentWeylGroup (componentRoots χ i), w • β = β ∨ w • β = -β := by
    intro w hw
    induction hw using Subgroup.closure_induction with
    | mem x hx =>
      obtain ⟨β', hβ', rfl⟩ := hx
      obtain rfl := hsimple β' hβ'
      exact Or.inr (rootReflection_smul_self hr)
    | one => exact Or.inl (one_smul _ _)
    | mul x y _ _ hx hy =>
      rw [mul_smul]
      rcases hy with hy | hy
      · rw [hy]
        exact hx
      · rw [hy, smul_neg]
        rcases hx with hx | hx
        · exact Or.inr (by rw [hx])
        · exact Or.inl (by rw [hx, neg_neg])
    | inv x _ hx =>
      rcases hx with hx | hx
      · left
        calc x⁻¹ • β = x⁻¹ • (x • β) := by rw [hx]
          _ = β := inv_smul_smul x β
      · right
        have : x⁻¹ • (x • β) = x⁻¹ • -β := by rw [hx]
        rw [inv_smul_smul, smul_neg] at this
        exact neg_eq_iff_eq_neg.1 this.symm
  have hβ2 : iform β β = 2 := by
    rw [← dotProduct_mulVec_eq_iform]
    exact rootForm_self hτ hr
  rcases hW w hw with h1 | h1
  · rw [hγw, h1, hβ2] at hγ
    omega
  · have h2 : iform β (-β) = - iform β β := by
      rw [← neg_one_smul ℤ β, iform_smul_right]
      ring
    rw [hγw, h1, h2, hβ2] at hγ
    omega

end Classes

section Check

variable {τ : Tag} (C : RootCertificate τ)

@[expose] def nonIsolatedCheck (m : ℕ) : Bool :=
  (List.range C.roots.length).all fun k => !inKernel C m k ||
    (List.range C.roots.length).any fun k' =>
      inKernel C m k' && decide (cpair (C.root k) (C.root k') = 1)

variable {C}

theorem nonIsolated_of_check (hC : C.check = true) (hS : τ.symmetrizedCartan = τ.cartan) {m : ℕ}
    (h : nonIsolatedCheck C m = true) :
    ∀ β ∈ kernelRoots (signMaskChar τ m), ∃ γ ∈ kernelRoots (signMaskChar τ m), iform β γ = 1 := by
  intro β hβ
  obtain ⟨k, hk, rfl, hker⟩ := (mem_kernelRoots_iff hC).1 hβ
  simp only [nonIsolatedCheck, List.all_eq_true, List.mem_range, Bool.or_eq_true,
    Bool.not_eq_true', List.any_eq_true, Bool.and_eq_true, decide_eq_true_eq] at h
  rcases h k hk with h0 | ⟨k', hk', hker', hform⟩
  · rw [hker] at h0
    exact absurd h0 (by simp)
  · exact ⟨C.root k', (mem_kernelRoots_iff hC).2 ⟨k', hk', rfl, hker'⟩,
      (iform_eq_cpair hS _ _).trans hform⟩

end Check

theorem e7_nonIsolated_two : nonIsolatedCheck e7Certificate 2 = true := by decide +kernel

theorem e7_nonIsolated_three : nonIsolatedCheck e7Certificate 3 = true := by decide +kernel

theorem e7_symmetrizedCartan : Tag.E7.symmetrizedCartan = Tag.E7.cartan := by
  change Tag.E7.symmetrizer * Tag.E7.cartan = Tag.E7.cartan
  rw [show Tag.E7.symmetrizer = 1 from rfl, one_mul]

theorem e7_forall_exists_iform_two :
    ∀ β ∈ kernelRoots (signMaskChar Tag.E7 2),
      ∃ γ ∈ kernelRoots (signMaskChar Tag.E7 2), iform β γ = 1 :=
  nonIsolated_of_check e7Certificate_check e7_symmetrizedCartan e7_nonIsolated_two

theorem e7_forall_exists_iform_three :
    ∀ β ∈ kernelRoots (signMaskChar Tag.E7 3),
      ∃ γ ∈ kernelRoots (signMaskChar Tag.E7 3), iform β γ = 1 :=
  nonIsolated_of_check e7Certificate_check e7_symmetrizedCartan e7_nonIsolated_three

theorem e7_kernelRoots_nonempty_two : (kernelRoots (signMaskChar Tag.E7 2)).Nonempty := by
  have h : (List.range e7Certificate.roots.length).any (inKernel e7Certificate 2) = true := by
    decide +kernel
  simp only [List.any_eq_true, List.mem_range] at h
  obtain ⟨k, hk, hker⟩ := h
  exact ⟨_, (mem_kernelRoots_iff e7Certificate_check).2 ⟨k, hk, rfl, hker⟩⟩

theorem e7_kernelRoots_nonempty_three : (kernelRoots (signMaskChar Tag.E7 3)).Nonempty := by
  have h : (List.range e7Certificate.roots.length).any (inKernel e7Certificate 3) = true := by
    decide +kernel
  simp only [List.any_eq_true, List.mem_range] at h
  obtain ⟨k, hk, hker⟩ := h
  exact ⟨_, (mem_kernelRoots_iff e7Certificate_check).2 ⟨k, hk, rfl, hker⟩⟩

end CFSG.ClassicalInvolution.ModelFacts
