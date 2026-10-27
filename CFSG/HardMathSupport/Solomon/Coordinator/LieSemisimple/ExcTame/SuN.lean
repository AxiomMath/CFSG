module

public import CFSG.HardMathSupport.Timmesfeld.CrossChar.TwCompSU
public import CFSG.HardMathSupport.Solomon.Coordinator.LieSemisimple.ExcTame.Order216

public section

namespace CFSG.HardMathSupport.Solomon.Coordinator.LieSemisimple

open CFSG.Open CFSG.Blueprint.Chevalley CFSG.LieType.Chevalley CFSG.LieType.Steinberg.Adjoint
  CFSG.LocalAnalysis.ComponentInitial CFSG.LocalAnalysis.ComponentInitial.FourGroupChevalley
  CFSG.LieType.AlgebraicGroups CFSG.HardMathSupport.Timmesfeld.LangTorus
  CFSG.HardMathSupport.Timmesfeld.CrossChar
open scoped MatrixGroups

set_option linter.unusedSectionVars false


section Unitary

variable {τ : Tag} {L : Type} [Field L] [IsAlgClosed L] {p : ℕ} (S : LangSetup τ L p)
  {ta : Fin τ.rank → Lˣ}

theorem rationalComponent_suN_tame_of_frame_T (hT : rootDiagUnit τ ta ∈ S.D.torus)
    (i : KernelComponent (rootCharHom ta))
    (hkind : twistKind S.ρ (rootCharHom ta) i = .suN)
    {ν : ℕ} (hν : 3 ≤ ν) {ψ : SL(ν, L) →* ModGL τ L} {σ : Fin ν → Fin ν → Fin τ.rank → ℤ}
    (hψ : IsSLFrame ψ σ) {κ : ℤ} (hκ : κ ≠ 0)
    (hnorm : ∀ a b, a ≠ b → iform (σ a b) (σ a b) = 2 * κ)
    (hΨ : componentRoots (rootCharHom ta) i = frameRoots σ) :
    CFSG.IsQuasisimple (rationalComponent S.ρ S.Γ (rootCharHom ta) i) ∨
      Group.IsSolvable (rationalComponent S.ρ S.Γ (rootCharHom ta) i) := by
  classical
  obtain ⟨hs0, hs, -⟩ := outer_componentOrbitLength_spec S hT i
  set s := componentOrbitLength S.ρ (componentRoots (rootCharHom ta) i) with hsdef
  have hout : ¬ twistInner (componentRoots (rootCharHom ta) i)
      ((S.ρ : (Fin τ.rank → ℤ) → _)^[s]) := by
    intro h
    unfold twistKind at hkind
    rw [ite_eq_left_iff.2 (fun h' => absurd h h')] at hkind
    exact absurd hkind (by decide)
  have hmaps : ∀ a b, a ≠ b → (S.ρ : (Fin τ.rank → ℤ) → _)^[s] (σ a b) ∈ frameRoots σ := by
    intro a b hab
    have h1 : σ a b ∈ componentRoots (rootCharHom ta) i := by
      rw [hΨ]
      exact ⟨a, b, hab, rfl⟩
    have h2 : (S.ρ : (Fin τ.rank → ℤ) → _)^[s] (σ a b) ∈
        (S.ρ : (Fin τ.rank → ℤ) → _)^[s] '' componentRoots (rootCharHom ta) i := ⟨_, h1, rfl⟩
    rw [hs, hΨ] at h2
    exact h2
  have hneg : ∀ (n : ℕ) (γ : Fin τ.rank → ℤ),
      (S.ρ : (Fin τ.rank → ℤ) → _)^[n] (-γ) = -(S.ρ : (Fin τ.rank → ℤ) → _)^[n] γ := by
    intro n
    induction n with
    | zero => exact fun γ => rfl
    | succ n ih =>
      intro γ
      rw [Function.iterate_succ_apply', Function.iterate_succ_apply', ih, S.frob.neg_eq]
  rcases hψ.aut_cases hν hκ hnorm ((S.ρ : (Fin τ.rank → ℤ) → _)^[s]) hmaps (hneg s)
      (iform_rho_iterate S s) with ⟨π, hπ⟩ | ⟨π, hπ⟩
  · exfalso
    apply hout
    obtain ⟨w, hw, hwσ⟩ := hψ.exists_weyl_perm hκ hnorm π
    refine ⟨w, ?_, fun γ hγ => ?_⟩
    · rw [hΨ]
      exact hw
    · rw [hΨ] at hγ
      obtain ⟨a, b, hab, rfl⟩ := hγ
      rw [hπ a b hab, hwσ]
  · obtain ⟨h1, h2⟩ := rationalComponent_of_unitary_frame_T S hT i hν hψ hΨ π hπ
    by_cases hQ : (ν, S.D.q ^ s) = (3, 2)
    · exact Or.inr (isSolvable_of_card_dvd_216 (h2 hQ))
    · exact Or.inl (h1 hQ)

end Unitary

end CFSG.HardMathSupport.Solomon.Coordinator.LieSemisimple
