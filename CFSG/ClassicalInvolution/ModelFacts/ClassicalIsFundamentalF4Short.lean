module

public import CFSG.LieType.Chevalley.SignCharacterMasks
public import CFSG.Assembly.LowTwoRankDefs

public section

namespace CFSG.ClassicalInvolution.ModelFacts

open CFSG.Blueprint.Chevalley CFSG.LieType.Chevalley CFSG.LieType.Steinberg.Adjoint

theorem iform_self_F4 {γ : Fin Tag.F4.rank → ℤ} (hγ : IsRoot .F4 γ) :
    iform γ γ = 2 ∨ iform γ γ = 4 := by
  have h : ∀ γ ∈ rootFinset .F4, iform γ γ = 2 ∨ iform γ γ = 4 := by decide +kernel
  exact h γ (mem_rootFinset.2 hγ)

theorem maskChar_ofAdd_eq_one_iff {τ : Tag} (m : Fin τ.rank → Bool) (v : Fin τ.rank → ℤ) :
    maskChar m (Multiplicative.ofAdd v) = 1 ↔ Even (maskPairing m v) := by
  rw [maskChar_apply]
  exact neg_one_zpow_eq_one_iff _

theorem F4_short_root_has_nonorthogonal_kernel_root (m : Fin Tag.F4.rank → Bool)
    {γ : Fin Tag.F4.rank → ℤ} (hγ : IsRoot .F4 γ) (hshort : iform γ γ = 2)
    (hker : maskChar m (Multiplicative.ofAdd γ) = 1) :
    ∃ δ : Fin Tag.F4.rank → ℤ, IsRoot .F4 δ ∧ δ ≠ γ ∧ δ ≠ -γ ∧
      maskChar m (Multiplicative.ofAdd δ) = 1 ∧ iform γ δ ≠ 0 := by
  have h : ∀ γ ∈ rootFinset .F4, iform γ γ = 2 → ∀ m : Fin Tag.F4.rank → Bool,
      Even (maskPairing m γ) → ∃ δ ∈ rootFinset .F4, δ ≠ γ ∧ δ ≠ -γ ∧
        Even (maskPairing m δ) ∧ iform γ δ ≠ 0 := by decide +kernel
  obtain ⟨δ, hδ, h1, h2, h3, h4⟩ := h γ (mem_rootFinset.2 hγ) hshort m
    ((maskChar_ofAdd_eq_one_iff m γ).1 hker)
  exact ⟨δ, mem_rootFinset.1 hδ, h1, h2, (maskChar_ofAdd_eq_one_iff m δ).2 h3, h4⟩

end CFSG.ClassicalInvolution.ModelFacts
