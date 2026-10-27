module

public import CFSG.LocalAnalysis.EvenSporadicStandard.HNRecog.Aschbacher.Fpf.Decomp
public import CFSG.LocalAnalysis.EvenSporadicStandard.HNRecog.Aschbacher.Fpf.NoStabilizer
public import CFSG.LocalAnalysis.EvenSporadicStandard.HNRecog.Aschbacher.Fpf.CaseOne
public import CFSG.LocalAnalysis.EvenSporadicStandard.HNRecog.Aschbacher.Fpf.FixedVector
public import CFSG.LocalAnalysis.EvenSporadicStandard.HNRecog.Aschbacher.Fpf.FixedFree
public import CFSG.LocalAnalysis.EvenSporadicStandard.HNRecog.Aschbacher.Fpf.StabilizerIso

public section

namespace CFSG.EvenSporadicStandard.HNRecog.Fpf

open Module

variable {V : Type} [AddCommGroup V] [Module (ZMod 2) V] [Finite V]

theorem fixedFree_of_irreducible (σ : A5 × A5 →* (V ≃ₗ[ZMod 2] V)) (hσ : Function.Injective σ)
    (h8 : finrank (ZMod 2) V = 8)
    (hirr : ∀ U : Submodule (ZMod 2) V, (∀ g : A5 × A5, ∀ u ∈ U, σ g u ∈ U) → U = ⊥ ∨ U = ⊤) :
    (∀ u : V, σ (a₀, 1) u = u → u = 0) ∧ (∀ u : V, σ (1, a₀) u = u → u = 0) := by
  constructor
  · intro u hu
    by_contra hne
    obtain ⟨VA, W, hc, h4A, h4W, hVA, hW, hB, hA⟩ :=
      exists_decomposition σ hσ h8 (Or.inl ⟨u, hne, hu⟩)
    rcases hirr VA hVA with h | h
    · rw [h] at h4A
      simp only [finrank_bot] at h4A
      omega
    · rw [h] at h4A
      rw [finrank_top, h8] at h4A
      omega
  · intro u hu
    by_contra hne
    obtain ⟨VA, W, hc, h4A, h4W, hVA, hW, hB, hA⟩ :=
      exists_decomposition σ hσ h8 (Or.inr ⟨u, hne, hu⟩)
    rcases hirr VA hVA with h | h
    · rw [h] at h4A
      simp only [finrank_bot] at h4A
      omega
    · rw [h] at h4A
      rw [finrank_top, h8] at h4A
      omega

theorem irreducible_of_fixedFree (σ : A5 × A5 →* (V ≃ₗ[ZMod 2] V)) (h8 : finrank (ZMod 2) V = 8)
    (hα : ∀ u : V, σ (a₀, 1) u = u → u = 0) (hβ : ∀ u : V, σ (1, a₀) u = u → u = 0) :
    ∀ U : Submodule (ZMod 2) V, (∀ g : A5 × A5, ∀ u ∈ U, σ g u ∈ U) → U = ⊥ ∨ U = ⊤ := by
  intro U hU
  let ρ : A5 × A5 →* Module.End (ZMod 2) V :=
    (Units.coeHom (Module.End (ZMod 2) V)).comp
      ((LinearMap.GeneralLinearGroup.generalLinearEquiv (ZMod 2) V).symm.toMonoidHom.comp σ)
  have hρa : ρ (a₀, 1) = (σ (a₀, 1) : V →ₗ[ZMod 2] V) := rfl
  have hρb : ρ (1, a₀) = (σ (1, a₀) : V →ₗ[ZMod 2] V) := rfl
  have hρn : ρ (1, n₀) = (σ (1, n₀) : V →ₗ[ZMod 2] V) := rfl
  have ha0 : (a₀ : A5) ^ 5 = 1 := by
    have h := pow_orderOf_eq_one a₀
    rwa [orderOf_a₀] at h
  have hp1 : ((a₀, 1) : A5 × A5) ^ 5 = 1 := by
    ext <;> simp [Prod.pow_fst, Prod.pow_snd, ha0]
  have hq1 : ((1, a₀) : A5 × A5) ^ 5 = 1 := by
    ext <;> simp [Prod.pow_fst, Prod.pow_snd, ha0]
  have hα5 : (ρ (a₀, 1)) ^ 5 = 1 := by rw [← map_pow, hp1, map_one]
  have hβ5 : (ρ (1, a₀)) ^ 5 = 1 := by rw [← map_pow, hq1, map_one]
  have hαβ : ρ (1, a₀) * ρ (a₀, 1) = ρ (a₀, 1) * ρ (1, a₀) := by
    have h : ((1, a₀) : A5 × A5) * (a₀, 1) = (a₀, 1) * (1, a₀) := by ext <;> simp
    simpa only [map_mul] using congrArg ρ h
  have hνα : ρ (1, n₀) * ρ (a₀, 1) = ρ (a₀, 1) * ρ (1, n₀) := by
    have h : ((1, n₀) : A5 × A5) * (a₀, 1) = (a₀, 1) * (1, n₀) := by ext <;> simp
    simpa only [map_mul] using congrArg ρ h
  have hνβ : ρ (1, n₀) * ρ (1, a₀) = ρ (1, a₀) ^ 4 * ρ (1, n₀) := by
    have h54 : (a₀ : A5) ^ 4 * a₀ = 1 := by rw [← pow_succ]; exact ha0
    have ha4 : (a₀ : A5) ^ 4 = a₀⁻¹ := eq_inv_of_mul_eq_one_left h54
    have key : ((1, n₀) : A5 × A5) * (1, a₀) * (1, n₀)⁻¹ = (1, a₀) ^ 4 := by
      ext <;> simp [Prod.pow_fst, Prod.pow_snd, n₀_mul_a₀_mul_inv, ha4]
    have hrel : ((1, n₀) : A5 × A5) * (1, a₀) = (1, a₀) ^ 4 * (1, n₀) := by
      rw [← key]; group
    simpa only [map_mul, map_pow] using congrArg ρ hrel
  have hν : Function.Injective (ρ (1, n₀)) := by
    intro x y hxy
    apply (σ (1, n₀)).injective
    simpa [hρn] using hxy
  have hαker : LinearMap.ker (ρ (a₀, 1) - 1) = ⊥ := by
    rw [LinearMap.ker_eq_bot']
    intro u hu
    have h1 : (σ (a₀, 1) : V →ₗ[ZMod 2] V) u - u = 0 := by simpa [hρa] using hu
    exact hα u (sub_eq_zero.mp h1)
  have hβker : LinearMap.ker (ρ (1, a₀) - 1) = ⊥ := by
    rw [LinearMap.ker_eq_bot']
    intro u hu
    have h1 : (σ (1, a₀) : V →ₗ[ZMod 2] V) u - u = 0 := by simpa [hρb] using hu
    exact hβ u (sub_eq_zero.mp h1)
  have hUα : ∀ u ∈ U, ρ (a₀, 1) u ∈ U := by
    intro u hu
    rw [hρa]
    exact hU (a₀, 1) u hu
  have hUβ : ∀ u ∈ U, ρ (1, a₀) u ∈ U := by
    intro u hu
    rw [hρb]
    exact hU (1, a₀) u hu
  have hUν : ∀ u ∈ U, ρ (1, n₀) u ∈ U := by
    intro u hu
    rw [hρn]
    exact hU (1, n₀) u hu
  exact eq_bot_or_eq_top_of_fixedFree (ρ (a₀, 1)) (ρ (1, a₀)) (ρ (1, n₀))
    hα5 hβ5 hαβ hνα hνβ hν h8 hαker hβker U hUα hUβ hUν

theorem irreducible_iff_exists_stabilizer (σ : A5 × A5 →* (V ≃ₗ[ZMod 2] V))
    (hσ : Function.Injective σ) (h8 : finrank (ZMod 2) V = 8) :
    (∀ U : Submodule (ZMod 2) V, (∀ g : A5 × A5, ∀ u ∈ U, σ g u ∈ U) → U = ⊥ ∨ U = ⊤) ↔
      ∃ v : V, v ≠ 0 ∧ ∃ S : Subgroup (A5 × A5), (∀ g, g ∈ S ↔ σ g v = v) ∧
        Nonempty (S ≃* A5) := by
  constructor
  · intro hirr
    obtain ⟨hα, hβ⟩ := fixedFree_of_irreducible σ hσ h8 hirr
    obtain ⟨v, hv, k, hk1, hk4, hvk⟩ := exists_fixed_vector σ h8 hα hβ
    let S : Subgroup (A5 × A5) :=
      { carrier := {g | σ g v = v}
        mul_mem' := by
          rintro a b (ha : σ a v = v) (hb : σ b v = v)
          show σ (a * b) v = v
          rw [map_mul, LinearEquiv.mul_apply, hb, ha]
        one_mem' := by
          show σ (1 : A5 × A5) v = v
          simp
        inv_mem' := by
          rintro a (ha : σ a v = v)
          show σ a⁻¹ v = v
          rw [map_inv]
          have h3 : (σ a)⁻¹ (σ a v) = v := by simp
          rwa [ha] at h3 }
    have hS : ∀ g : A5 × A5, g ∈ S ↔ σ g v = v := fun g => by simp [S]
    exact ⟨v, hv, S, hS,
      nonempty_mulEquiv_stabilizer σ h8 (fun y hy => fixedFree_of_orderOf_eq_five σ hα hβ hy)
        v hv k hk1 hk4 hvk S hS⟩
  · rintro ⟨v, hv, S, hS, ⟨e⟩⟩
    by_contra hnot
    have hcon : ¬ ((∀ u : V, σ (a₀, 1) u = u → u = 0) ∧
        (∀ u : V, σ (1, a₀) u = u → u = 0)) := by
      intro h
      exact hnot (irreducible_of_fixedFree σ h8 h.1 h.2)
    have hne : (∃ u : V, u ≠ 0 ∧ σ (a₀, 1) u = u) ∨
        (∃ u : V, u ≠ 0 ∧ σ (1, a₀) u = u) := by
      by_contra h
      apply hcon
      constructor
      · intro u hu
        by_contra hu0
        exact False.elim (h (Or.inl ⟨u, hu0, hu⟩))
      · intro u hu
        by_contra hu0
        exact False.elim (h (Or.inr ⟨u, hu0, hu⟩))
    obtain ⟨VA, W, hc, h4A, h4W, hVA, hW, hB, hA⟩ := exists_decomposition σ hσ h8 hne
    exact (isEmpty_mulEquiv_stabilizer σ VA W hc h4A h4W hVA hW hB hA v S hS).false e

end CFSG.EvenSporadicStandard.HNRecog.Fpf
