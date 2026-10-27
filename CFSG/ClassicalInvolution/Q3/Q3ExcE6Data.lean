module

public import CFSG.ClassicalInvolution.Q3.Q3ExcE7Data

public section

namespace CFSG.ClassicalInvolution.Q3

open CFSG.Blueprint.Chevalley CFSG.LieType.Chevalley CFSG.LieType.Chevalley.ToralSign
  CFSG.LieType.Steinberg.Adjoint CFSG.ClassicalInvolution.ModelFacts

section Check

variable {τ : Tag} (C : RootCertificate τ)

@[expose] def isolatedFixedCheck (ρ : Equiv.Perm (Fin τ.rank)) (m k₀ : ℕ) : Bool :=
  inKernel C m k₀ && (List.ofFn (permLattice ρ (C.root k₀)) == List.ofFn (C.root k₀)) &&
    (List.range C.roots.length).all fun k => !inKernel C m k ||
      (cpair (C.root k₀) (C.root k) == 0) || (List.ofFn (C.root k) == List.ofFn (C.root k₀)) ||
        (List.ofFn (C.root k) == List.ofFn (-C.root k₀))

@[expose] def restConnectedCheck (m k₀ k₁ : ℕ) : Bool :=
  decide (k₁ < C.roots.length) && inKernel C m k₁ &&
    (List.ofFn (C.root k₁) != List.ofFn (C.root k₀)) &&
    (List.ofFn (C.root k₁) != List.ofFn (-C.root k₀)) &&
    (List.range C.roots.length).all fun k => !inKernel C m k ||
      (List.ofFn (C.root k) == List.ofFn (C.root k₀)) ||
      (List.ofFn (C.root k) == List.ofFn (-C.root k₀)) ||
      (cpair (C.root k₁) (C.root k) != 0) ||
      (List.range C.roots.length).any fun k' => inKernel C m k' &&
        (cpair (C.root k₁) (C.root k') != 0) && (cpair (C.root k') (C.root k) != 0)

@[expose] def restPairCheck (m k₀ : ℕ) : Bool :=
  (List.range C.roots.length).any fun k => inKernel C m k &&
    (List.ofFn (C.root k) != List.ofFn (C.root k₀)) &&
    (List.ofFn (C.root k) != List.ofFn (-C.root k₀)) &&
    (List.range C.roots.length).any fun k' => inKernel C m k' &&
      (cpair (C.root k) (C.root k') == 1)

@[expose] def twoClassCheck (ρ : Equiv.Perm (Fin τ.rank)) (m k₁ : ℕ) : Bool :=
  (List.range C.roots.length).any fun k₀ => isolatedFixedCheck C ρ m k₀ &&
    restConnectedCheck C m k₀ k₁ && restPairCheck C m k₀

variable {C}

theorem exists_twoClass_of_check (hC : C.check = true) (hS : τ.symmetrizedCartan = τ.cartan)
    {ρ : Equiv.Perm (Fin τ.rank)} {m k₁ : ℕ} (h : twoClassCheck C ρ m k₁ = true) :
    ∃ (β₀ γ₁ : Fin τ.rank → ℤ) (_ : β₀ ∈ kernelRoots (signMaskChar τ m))
      (hγ₁ : γ₁ ∈ kernelRoots (signMaskChar τ m)), permLattice ρ β₀ = β₀ ∧
      (∀ γ ∈ kernelRoots (signMaskChar τ m), iform β₀ γ ≠ 0 → γ = β₀ ∨ γ = -β₀) ∧
      γ₁ ≠ β₀ ∧ γ₁ ≠ -β₀ ∧
      (∀ (γ : Fin τ.rank → ℤ) (hγ : γ ∈ kernelRoots (signMaskChar τ m)), γ ≠ β₀ → γ ≠ -β₀ →
        (⟦⟨γ₁, hγ₁⟩⟧ : KernelComponent (signMaskChar τ m)) = ⟦⟨γ, hγ⟩⟧) ∧
      ∃ γ ∈ kernelRoots (signMaskChar τ m), ∃ γ' ∈ kernelRoots (signMaskChar τ m),
        γ ≠ β₀ ∧ γ ≠ -β₀ ∧ iform γ γ' = 1 := by
  simp only [twoClassCheck, List.any_eq_true, List.mem_range, Bool.and_eq_true] at h
  obtain ⟨k₀, hk₀, ⟨hiso, hrest⟩, hpair⟩ := h
  simp only [isolatedFixedCheck, Bool.and_eq_true, List.all_eq_true, List.mem_range,
    Bool.or_eq_true, Bool.not_eq_true', beq_iff_eq] at hiso
  obtain ⟨⟨hker₀, hfix⟩, hisoall⟩ := hiso
  simp only [restConnectedCheck, Bool.and_eq_true, List.all_eq_true, List.mem_range,
    Bool.or_eq_true, Bool.not_eq_true', beq_iff_eq, bne_iff_ne, ne_eq, List.any_eq_true,
    decide_eq_true_eq] at hrest
  obtain ⟨⟨⟨⟨hk₁, hker₁⟩, hne₁⟩, hne₁'⟩, hrestall⟩ := hrest
  simp only [restPairCheck, List.any_eq_true, List.mem_range, Bool.and_eq_true, bne_iff_ne, ne_eq,
    beq_iff_eq] at hpair
  have hβ₀ : C.root k₀ ∈ kernelRoots (signMaskChar τ m) :=
    (mem_kernelRoots_iff hC).2 ⟨k₀, hk₀, rfl, hker₀⟩
  have hγ₁ : C.root k₁ ∈ kernelRoots (signMaskChar τ m) :=
    (mem_kernelRoots_iff hC).2 ⟨k₁, hk₁, rfl, hker₁⟩
  have hform : ∀ x y : Fin τ.rank → ℤ, iform x y = cpair x y := fun x y => iform_eq_cpair hS x y
  refine ⟨C.root k₀, C.root k₁, hβ₀, hγ₁, List.ofFn_injective hfix, ?_, fun h => hne₁ (by rw [h]),
    fun h => hne₁' (by rw [h]), ?_, ?_⟩
  · intro γ hγ hγ0
    obtain ⟨k, hk, rfl, hker⟩ := (mem_kernelRoots_iff hC).1 hγ
    rcases hisoall k hk with ((h | h) | h) | h
    · rw [hker] at h
      exact absurd h (by simp)
    · exact absurd (by rw [hform, h]) hγ0
    · exact Or.inl (List.ofFn_injective h)
    · exact Or.inr (List.ofFn_injective h)
  · intro γ hγ h1 h2
    obtain ⟨k, hk, rfl, hker⟩ := (mem_kernelRoots_iff hC).1 hγ
    rcases hrestall k hk with (((h | h) | h) | h) | ⟨k', hk', ⟨hker', h3⟩, h4⟩
    · rw [hker] at h
      exact absurd h (by simp)
    · exact absurd (List.ofFn_injective h) h1
    · exact absurd (List.ofFn_injective h) h2
    · refine mk_eq_of_iform_ne_zero (α := ⟨C.root k₁, hγ₁⟩) (β := ⟨C.root k, hγ⟩) ?_
      change iform (C.root k₁) (C.root k) ≠ 0
      rw [hform]
      exact h
    · have hk'm : C.root k' ∈ kernelRoots (signMaskChar τ m) :=
        (mem_kernelRoots_iff hC).2 ⟨k', hk', rfl, hker'⟩
      have e1 : (⟦⟨C.root k₁, hγ₁⟩⟧ : KernelComponent (signMaskChar τ m)) =
          ⟦⟨C.root k', hk'm⟩⟧ := by
        refine mk_eq_of_iform_ne_zero ?_
        change iform (C.root k₁) (C.root k') ≠ 0
        rw [hform]
        exact h3
      have e2 : (⟦⟨C.root k', hk'm⟩⟧ : KernelComponent (signMaskChar τ m)) =
          ⟦⟨C.root k, hγ⟩⟧ := by
        refine mk_eq_of_iform_ne_zero ?_
        change iform (C.root k') (C.root k) ≠ 0
        rw [hform]
        exact h4
      exact e1.trans e2
  · obtain ⟨k, hk, ⟨⟨hker, hne⟩, hne'⟩, k', hk', hker', hcp⟩ := hpair
    exact ⟨C.root k, (mem_kernelRoots_iff hC).2 ⟨k, hk, rfl, hker⟩, C.root k',
      (mem_kernelRoots_iff hC).2 ⟨k', hk', rfl, hker'⟩, fun h => hne (by rw [h]),
      fun h => hne' (by rw [h]), by rw [hform]; exact hcp⟩


end Check

theorem e6_symmetrizedCartan : Tag.E6.symmetrizedCartan = Tag.E6.cartan := by
  change Tag.E6.symmetrizer * Tag.E6.cartan = Tag.E6.cartan
  rw [show Tag.E6.symmetrizer = 1 from rfl, one_mul]

theorem e6_twoClassCheck_two : twoClassCheck e6Certificate TwistTag.E6.perm 2 0 = true := by
  decide +kernel

theorem e6_twoClass_two :
    ∃ (β₀ γ₁ : Fin Tag.E6.rank → ℤ) (_ : β₀ ∈ kernelRoots (signMaskChar Tag.E6 2))
      (hγ₁ : γ₁ ∈ kernelRoots (signMaskChar Tag.E6 2)), permLattice TwistTag.E6.perm β₀ = β₀ ∧
      (∀ γ ∈ kernelRoots (signMaskChar Tag.E6 2), iform β₀ γ ≠ 0 → γ = β₀ ∨ γ = -β₀) ∧
      γ₁ ≠ β₀ ∧ γ₁ ≠ -β₀ ∧
      (∀ (γ : Fin Tag.E6.rank → ℤ) (hγ : γ ∈ kernelRoots (signMaskChar Tag.E6 2)), γ ≠ β₀ →
        γ ≠ -β₀ → (⟦⟨γ₁, hγ₁⟩⟧ : KernelComponent (signMaskChar Tag.E6 2)) = ⟦⟨γ, hγ⟩⟧) ∧
      ∃ γ ∈ kernelRoots (signMaskChar Tag.E6 2), ∃ γ' ∈ kernelRoots (signMaskChar Tag.E6 2),
        γ ≠ β₀ ∧ γ ≠ -β₀ ∧ iform γ γ' = 1 :=
  exists_twoClass_of_check e6Certificate_check e6_symmetrizedCartan e6_twoClassCheck_two

theorem e6_connectedCheck_twenty : connectedCheck e6Certificate 20 = true := by decide +kernel

theorem e6_subsingleton_twenty : Subsingleton (KernelComponent (signMaskChar Tag.E6 20)) :=
  subsingleton_of_connectedCheck e6Certificate_check e6_symmetrizedCartan e6_connectedCheck_twenty

theorem e6_nonIsolated_twenty : nonIsolatedCheck e6Certificate 20 = true := by decide +kernel

theorem e6_forall_exists_iform_twenty :
    ∀ β ∈ kernelRoots (signMaskChar Tag.E6 20),
      ∃ γ ∈ kernelRoots (signMaskChar Tag.E6 20), iform β γ = 1 :=
  nonIsolated_of_check e6Certificate_check e6_symmetrizedCartan e6_nonIsolated_twenty

end CFSG.ClassicalInvolution.Q3
