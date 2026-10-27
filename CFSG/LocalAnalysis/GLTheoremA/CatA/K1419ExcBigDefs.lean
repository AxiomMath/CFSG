module

public import CFSG.LieType.Chevalley.KernelComponentRoots
public import CFSG.Blueprint.ChevalleyRootArtifact

public section

namespace CFSG.LocalAnalysis.GLTheoremA.K1419E

open CFSG.Blueprint.Chevalley CFSG.LieType.Chevalley CFSG.LieType.Steinberg.Adjoint

theorem k1419e_natCast_three_ne_zero (L : Type) [Field L] [CharP L 2] : ((3 : ℕ) : L) ≠ 0 := by
  intro h
  have h2 : ((2 : ℕ) : L) = 0 := CharP.cast_eq_zero L 2
  have h3 : ((3 : ℕ) : L) = ((2 : ℕ) : L) + 1 := by push_cast; ring
  rw [h3, h2, zero_add] at h
  exact one_ne_zero h

@[expose] def k1419eStrongOrth (τ : Tag) (β γ : Fin τ.rank → ℤ) : Prop :=
  iform β γ = 0 ∧ ¬ IsRoot τ (β + γ) ∧ ¬ IsRoot τ (β - γ)

@[expose] def k1419eHasTriple (τ : Tag) (Ψ : Set (Fin τ.rank → ℤ)) : Prop :=
  ∃ β₁ ∈ Ψ, ∃ β₂ ∈ Ψ, ∃ β₃ ∈ Ψ, k1419eStrongOrth τ β₁ β₂ ∧ k1419eStrongOrth τ β₁ β₃ ∧
    k1419eStrongOrth τ β₂ β₃

@[expose] def k1419eSoList (τ : Tag) (β γ : Fin τ.rank → ℤ) : Prop :=
  iform β γ = 0 ∧ List.ofFn (β + γ) ∉ τ.artifactRoots ∧ List.ofFn (β - γ) ∉ τ.artifactRoots

instance (τ : Tag) (β γ : Fin τ.rank → ℤ) : Decidable (k1419eSoList τ β γ) := by
  unfold k1419eSoList
  infer_instance

theorem k1419eSoList.strongOrth {τ : Tag} {β γ : Fin τ.rank → ℤ}
    (h : k1419eSoList τ β γ) : k1419eStrongOrth τ β γ :=
  ⟨h.1, fun hr => h.2.1 (isRoot_iff_mem_artifactRoots.1 hr),
    fun hr => h.2.2 (isRoot_iff_mem_artifactRoots.1 hr)⟩

theorem k1419eStrongOrth.smul
    {τ : Tag} {β γ : Fin τ.rank → ℤ} (h : k1419eStrongOrth τ β γ) (v : WeylGroup τ) :
    k1419eStrongOrth τ (v • β) (v • γ) := by
  obtain ⟨h0, hp, hm⟩ := h
  refine ⟨by rw [iform_smul]; exact h0, fun hr => hp ?_, fun hr => hm ?_⟩
  · rw [← smul_add] at hr
    simpa using IsRoot.smul hr v⁻¹
  · rw [← smul_sub] at hr
    simpa using IsRoot.smul hr v⁻¹

theorem k1419eHasTriple.mono {τ : Tag} {Ψ Ψ' : Set (Fin τ.rank → ℤ)} (h : k1419eHasTriple τ Ψ)
    (hΨ : Ψ ⊆ Ψ') : k1419eHasTriple τ Ψ' := by
  obtain ⟨β₁, h₁, β₂, h₂, β₃, h₃, o₁₂, o₁₃, o₂₃⟩ := h
  exact ⟨β₁, hΨ h₁, β₂, hΨ h₂, β₃, hΨ h₃, o₁₂, o₁₃, o₂₃⟩

theorem k1419eHasTriple.image_smul
    {τ : Tag} {Ψ : Set (Fin τ.rank → ℤ)} (h : k1419eHasTriple τ Ψ) (v : WeylGroup τ) :
    k1419eHasTriple τ ((fun α => v • α) '' Ψ) := by
  obtain ⟨β₁, h₁, β₂, h₂, β₃, h₃, o₁₂, o₁₃, o₂₃⟩ := h
  exact ⟨v • β₁, ⟨β₁, h₁, rfl⟩, v • β₂, ⟨β₂, h₂, rfl⟩, v • β₃, ⟨β₃, h₃, rfl⟩,
    o₁₂.smul v, o₁₃.smul v, o₂₃.smul v⟩

end CFSG.LocalAnalysis.GLTheoremA.K1419E

end
