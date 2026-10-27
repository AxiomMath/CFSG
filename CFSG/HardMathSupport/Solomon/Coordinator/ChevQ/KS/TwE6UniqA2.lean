module

public import CFSG.HardMathSupport.Solomon.Coordinator.LieComp.Exc.TypeAOne
public import CFSG.HardMathSupport.Solomon.Coordinator.LieSemisimple.ExcTame.Order216

public section

namespace CFSG.HardMathSupport.Solomon.Coordinator.ChevQ

open CFSG.Blueprint.Chevalley CFSG.LieType.Chevalley CFSG.LieType.Steinberg.Adjoint
  CFSG.LocalAnalysis.ComponentInitial.FourGroupChevalley CFSG.LieType.AlgebraicGroups
  CFSG.HardMathSupport.Timmesfeld.LangTorus CFSG.HardMathSupport.Timmesfeld.CrossChar
  CFSG.HardMathSupport.Solomon.Coordinator.LieSemisimple
  CFSG.HardMathSupport.Solomon.Coordinator.LieComp
open scoped MatrixGroups

namespace TwE6UniqAbs

section A2


set_option linter.unusedSectionVars false

theorem orbit_ne_of_A2_quasisimple {L : Type} [Field L] [IsAlgClosed L] {p₀ : ℕ}
    (S : LangSetup Tag.E6 L p₀) {a : Fin Tag.E6.rank → Lˣ} (hq2 : S.D.q = 2)
    (hT : rootDiagUnit Tag.E6 a ∈ S.D.torus) (i : KernelComponent (rootCharHom a))
    (hframe : ∃ (ψ : SL(3, L) →* ModGL Tag.E6 L) (σ : Fin 3 → Fin 3 → Fin Tag.E6.rank → ℤ),
      IsSLFrame ψ σ ∧ (∀ x y, x ≠ y → iform (σ x y) (σ x y) = 2) ∧
        componentRoots (rootCharHom a) i = frameRoots σ)
    (hG : (∃ γ : Fin Tag.E6.rank → ℤ, IsRoot Tag.E6 γ ∧ rootChar a γ ≠ 1) ∧
      ∀ γ γ' : Fin Tag.E6.rank → ℤ, IsRoot Tag.E6 γ → IsRoot Tag.E6 γ' →
        (∀ δ ∈ componentRoots (rootCharHom a) i, iform γ δ = iform γ' δ) →
          rootChar a γ = rootChar a γ')
    (hQS : CFSG.IsQuasisimple (rationalComponent S.ρ S.Γ (rootCharHom a) i)) :
    (S.ρ : (Fin Tag.E6.rank → ℤ) → _) '' componentRoots (rootCharHom a) i ≠
      componentRoots (rootCharHom a) i := by
  classical
  intro hfix
  obtain ⟨ψ, σ, hψ, hnorm0, hΨ⟩ := hframe
  have hnorm : ∀ x y, x ≠ y → iform (σ x y) (σ x y) = 2 * 1 := fun x y hxy => by
    rw [hnorm0 x y hxy, mul_one]
  have hκ : (1 : ℤ) ≠ 0 := one_ne_zero
  obtain ⟨hs0, hs, -⟩ := outer_componentOrbitLength_spec S hT i
  set s := componentOrbitLength S.ρ (componentRoots (rootCharHom a) i)
  have hs1 : s = 1 := le_antisymm (Nat.sInf_le ⟨Nat.one_pos, by simpa using hfix⟩) hs0
  have hmaps : ∀ x y, x ≠ y →
      (S.ρ : (Fin Tag.E6.rank → ℤ) → _)^[s] (σ x y) ∈ frameRoots σ := by
    intro x y hxy
    have h1 : σ x y ∈ componentRoots (rootCharHom a) i := by
      rw [hΨ]
      exact ⟨x, y, hxy, rfl⟩
    have h2 : (S.ρ : (Fin Tag.E6.rank → ℤ) → _)^[s] (σ x y) ∈
        (S.ρ : (Fin Tag.E6.rank → ℤ) → _)^[s] '' componentRoots (rootCharHom a) i := ⟨_, h1, rfl⟩
    rw [hs, hΨ] at h2
    exact h2
  have hneg : ∀ (n : ℕ) (γ : Fin Tag.E6.rank → ℤ),
      (S.ρ : (Fin Tag.E6.rank → ℤ) → _)^[n] (-γ) = -(S.ρ : (Fin Tag.E6.rank → ℤ) → _)^[n] γ := by
    intro n
    induction n with
    | zero => exact fun γ => rfl
    | succ n ih =>
      intro γ
      rw [Function.iterate_succ_apply', Function.iterate_succ_apply', ih, S.frob.neg_eq]
  rcases hψ.aut_cases (le_refl 3) hκ hnorm ((S.ρ : (Fin Tag.E6.rank → ℤ) → _)^[s]) hmaps
      (hneg s) (iform_rho_iterate S s) with ⟨π, hπ⟩ | ⟨π, hπ⟩
  ·
    obtain ⟨w, hw, hwσ⟩ := hψ.exists_weyl_perm hκ hnorm π
    rw [hs1] at hπ
    have hρw : ∀ δ ∈ componentRoots (rootCharHom a) i, S.ρ δ = w • δ := by
      intro δ hδ
      rw [hΨ] at hδ
      obtain ⟨x, y, hxy, rfl⟩ := hδ
      have h1 := hπ x y hxy
      rw [Function.iterate_one] at h1
      rw [h1, hwσ]
    have hker : ∀ δ ∈ componentRoots (rootCharHom a) i, rootChar a δ = 1 := fun δ hδ => hδ.1.2
    let H : Subgroup (WeylGroup Tag.E6) :=
      { carrier := {u | ∀ x, rootChar a (u • x) = rootChar a x}
        mul_mem' := fun {u v} hu hv x => by
          rw [mul_smul, hu (v • x), hv x]
        one_mem' := fun x => by rw [one_smul]
        inv_mem' := fun {u} hu x => by
          have h := hu (u⁻¹ • x)
          rw [smul_inv_smul] at h
          exact h.symm }
    have hgen : Subgroup.closure {s : WeylGroup Tag.E6 | ∃ γ ∈ frameRoots σ,
        s = rootReflection γ} ≤ H := by
      rw [Subgroup.closure_le]
      rintro _ ⟨δ, hδ, rfl⟩ x
      have hδΨ : δ ∈ componentRoots (rootCharHom a) i := by
        rw [hΨ]
        exact hδ
      rw [rootReflection_smul (hψ.frameRoots_isRoot δ hδ) x,
        CFSG.LocalAnalysis.ComponentInitial.FourGroupChevalley.rootChar_sub,
        CFSG.LieType.Chevalley.rootChar_zsmul, hker δ hδΨ, one_zpow, inv_one, mul_one]
    have hwinv : ∀ x, rootChar a (w⁻¹ • x) = rootChar a x := hgen (Subgroup.inv_mem _ hw)
    obtain ⟨⟨γ, hγ, hγ1⟩, hG2⟩ := hG
    have hργ : IsRoot Tag.E6 (S.ρ γ) := (S.frob.isRoot_iff γ).2 hγ
    have hγ' : IsRoot Tag.E6 (w⁻¹ • S.ρ γ) := IsRoot.smul hργ w⁻¹
    have hform : ∀ δ ∈ componentRoots (rootCharHom a) i,
        iform γ δ = iform (w⁻¹ • S.ρ γ) δ := by
      intro δ hδ
      have h1 : iform (w⁻¹ • S.ρ γ) δ = iform (S.ρ γ) (w • δ) := by
        rw [← iform_smul w (w⁻¹ • S.ρ γ) δ, smul_inv_smul]
      rw [h1, ← hρw δ hδ, S.frob.iform_eq]
    have h1 := hG2 γ (w⁻¹ • S.ρ γ) hγ hγ' hform
    rw [hwinv, S.frob.rootChar_eq a hT γ hγ, hq2] at h1
    have h2 : rootChar a γ * rootChar a γ = rootChar a γ * 1 := by
      rw [mul_one, ← pow_two]
      exact h1.symm
    exact hγ1 (mul_left_cancel h2)
  ·
    obtain ⟨-, h2⟩ := rationalComponent_of_unitary_frame_T S hT i (le_refl 3) hψ hΨ π hπ
    have hQ : ((3 : ℕ), S.D.q ^ s) = (3, 2) := by
      rw [hs1, hq2]
      norm_num
    exact not_isSolvable_of_isQuasisimple hQS (isSolvable_of_card_dvd_216 (h2 hQ))

end A2

end TwE6UniqAbs

end CFSG.HardMathSupport.Solomon.Coordinator.ChevQ
