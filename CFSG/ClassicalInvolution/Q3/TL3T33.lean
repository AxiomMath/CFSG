module

public import CFSG.ClassicalInvolution.Q3.TL3T32
public import CFSG.ClassicalInvolution.Q3.TL4D1ML32D

public section

namespace CFSG.ClassicalInvolution.Q3.TC.Thin

open CFSG CFSG.Open CFSG.ClassicalInvolution CFSG.ClassicalInvolution.Generic
open CFSG.ClassicalInvolution.Q3.AE CFSG.ClassicalInvolution.Q3.TL4 Matrix

@[expose] def mat9 (a b c d e f g h i : ZMod 2) : Matrix (Fin 3) (Fin 3) (ZMod 2) :=
  !![a, b, c; d, e, f; g, h, i]

theorem fix_mem_fanoLines_mat : ∀ a b c d e f g h i : ZMod 2,
    mat9 a b c d e f g h i * mat9 a b c d e f g h i = 1 → mat9 a b c d e f g h i ≠ 1 →
    (Finset.univ.filter fun x : Fin 7 => fanoIdx (mat9 a b c d e f g h i *ᵥ fanoVec x) = x) ∈
      fanoLines := by
  decide +kernel

theorem fix_mem_fanoLines {σ : Equiv.Perm (Fin 7)} (hσ : σ ∈ l32) (h2 : σ * σ = 1)
    (h1 : σ ≠ 1) : (Finset.univ.filter fun x => σ x = x) ∈ fanoLines := by
  obtain ⟨A, rfl⟩ := exists_lpermHom_eq hσ
  have hA2 : A * A = 1 := lpermHom_injective (by rw [map_mul, map_one]; exact h2)
  have hA1 : A ≠ 1 := fun h => h1 (by rw [h, map_one])
  have key := fix_mem_fanoLines_mat (A.1 0 0) (A.1 0 1) (A.1 0 2) (A.1 1 0) (A.1 1 1) (A.1 1 2)
    (A.1 2 0) (A.1 2 1) (A.1 2 2)
  have hA : mat9 (A.1 0 0) (A.1 0 1) (A.1 0 2) (A.1 1 0) (A.1 1 1) (A.1 1 2) (A.1 2 0) (A.1 2 1)
      (A.1 2 2) = A.1 := (eta_fin_three A.1).symm
  rw [hA] at key
  exact key (congrArg Subtype.val hA2) fun h => hA1 (Subtype.ext h)

theorem exists_e64Sets_invariant {σ τ : Equiv.Perm (Fin 7)} (hσ : σ ∈ l32) (hσσ : σ * σ = 1)
    (hστ : σ * τ = τ * σ) (hσ1 : σ ≠ 1) :
    ∃ γ ∈ e64Sets, ∃ _ : γ.card = 4, (∀ x ∈ γ, σ x ∈ γ) ∧ (∀ x ∈ γ, τ x ∈ γ) ∧
      ∃ x ∈ γ, σ x ≠ x ∨ τ x ≠ x := by
  have hℓ := fix_mem_fanoLines hσ hσσ hσ1
  have hmem : ∀ x, x ∈ (Finset.univ.filter fun x => σ x = x)ᶜ ↔ σ x ≠ x := fun x => by simp
  have hσσx : ∀ x, σ (σ x) = x := fun x => by
    have := congrArg (fun f : Equiv.Perm (Fin 7) => f x) hσσ
    simpa [Equiv.Perm.mul_apply] using this
  have hc : ∀ x, σ (τ x) = τ (σ x) := fun x => by
    have := congrArg (fun f : Equiv.Perm (Fin 7) => f x) hστ
    simpa [Equiv.Perm.mul_apply] using this
  have hcard := fanoLines_compl_card _ hℓ
  obtain ⟨x₀, hx₀⟩ : (Finset.univ.filter fun x => σ x = x)ᶜ.Nonempty := by
    rw [← Finset.card_pos, hcard]
    norm_num
  refine ⟨_, ⟨_, hℓ, rfl⟩, hcard, fun x hx => ?_, fun x hx => ?_, x₀, hx₀,
    Or.inl ((hmem x₀).mp hx₀)⟩
  · rw [hmem] at hx ⊢
    rw [hσσx]
    exact fun h => hx h.symm
  · rw [hmem] at hx ⊢
    rw [hc]
    exact fun h => hx (τ.injective h)

theorem modelTwCore_e64 : ModelTwCore e64Sets e64Sub := by
  show ModelTwCore e64Sets (aeBarOver l32)
  exact modelTwCore_aeBarOver (by norm_num)
    (fun σ hσ => Equiv.Perm.mem_alternatingGroup.mpr (l32_sign σ hσ)) l32_normal_two
    fun σ hσ τ _ hσσ _ hστ hσ1 _ _ => exists_e64Sets_invariant hσ hσσ hστ hσ1

end CFSG.ClassicalInvolution.Q3.TC.Thin
