module

public import CFSG.LocalAnalysis.EvenSporadicStandard.M22Std.P21FieldA

public section

namespace CFSG.EvenSporadicStandard.M22Std.P21Field

open Module

variable {S : Type*} [AddCommGroup S] [Module (ZMod 2) S] [Finite S]

theorem not_inv_conj {g : S →ₗ[ZMod 2] S} (hg : Irr g) (he : Odd (finrank (ZMod 2) S)) {ℓ : ℕ}
    (hℓ : ℓ.Prime) (hodd : Odd ℓ) (hgℓ : g ^ ℓ = 1) (hg1 : g ≠ 1) (τ : S ≃ₗ[ZMod 2] S)
    (hτ : τ.toLinearMap * g = g ^ (ℓ - 1) * τ.toLinearMap) : False := by
  have hℓ2 : 2 ≤ ℓ := hℓ.two_le
  have hgK' : g ^ (ℓ - 1) ∈ K g := pow_mem (g_mem_K g) _
  obtain ⟨σ, hσ⟩ := exists_ringAut_conj τ hgK' hτ
  set a₀ : K g := ⟨g, g_mem_K g⟩ with ha₀
  have key : ((σ a₀ : K g) : Module.End (ZMod 2) S) * τ.toLinearMap =
      g ^ (ℓ - 1) * τ.toLinearMap := by
    rw [hσ a₀]
    exact hτ
  have hσa : σ a₀ = a₀ ^ (ℓ - 1) := by
    apply Subtype.ext
    have : ((σ a₀ : K g) : Module.End (ZMod 2) S) = g ^ (ℓ - 1) := by
      ext v
      have := congrArg (fun T => T (τ.symm v)) key
      simpa using this
    rw [this]
    rfl
  have ha₀ℓ : a₀ ^ ℓ = 1 := Subtype.ext hgℓ
  have hσσ : σ (σ a₀) = a₀ := by
    rw [hσa, map_pow, hσa, ← pow_mul]
    have : (ℓ - 1) * (ℓ - 1) = ℓ * (ℓ - 2) + 1 := by
      obtain ⟨m, rfl⟩ : ∃ m, ℓ = m + 2 := ⟨ℓ - 2, by omega⟩
      have h1 : m + 2 - 1 = m + 1 := by omega
      have h2 : m + 2 - 2 = m := by omega
      rw [h1, h2]
      ring
    rw [this, pow_succ, pow_mul, ha₀ℓ, one_pow, one_mul]
  have hσ2 : σ.trans σ = AlgEquiv.refl :=
    algEquiv_ext_of_apply_g _ _ (by
      show σ (σ a₀) = a₀
      exact hσσ)
  have h1 := ringAut_eq_one_of_sq hg he σ.toRingEquiv (fun a => by
    have := congrArg (fun e : K g ≃ₐ[ZMod 2] K g => e a) hσ2
    exact this) a₀
  have h2 : σ a₀ = a₀ := h1
  rw [hσa] at h2
  have h3 : g ^ (ℓ - 1) = g := congrArg Subtype.val h2
  have h4 : g * g = 1 := by
    have : g ^ ℓ = g ^ (ℓ - 1) * g := by rw [← pow_succ, show ℓ - 1 + 1 = ℓ by omega]
    rw [h3] at this
    rw [← hgℓ, this]
  obtain ⟨k, hk⟩ := hodd
  apply hg1
  have : g ^ ℓ = (g * g) ^ k * g := by
    rw [hk, pow_succ, pow_mul, sq]
  rw [h4, one_pow, one_mul, hgℓ] at this
  exact this.symm

end CFSG.EvenSporadicStandard.M22Std.P21Field
