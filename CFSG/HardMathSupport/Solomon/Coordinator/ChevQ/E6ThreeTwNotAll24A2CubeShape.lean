module

public import CFSG.HardMathSupport.Dickson.Sec6.Up34Chev2Aux.InnExcCong
public import CFSG.HardMathSupport.Timmesfeld.CrossChar.TwCompSUAut
public import CFSG.HardMathSupport.Dickson.Sec6.I923Aux.Basic
public import CFSG.HardMathSupport.Dickson.Sec6.Up34Chev2Aux.InnExcRDE6
public import CFSG.HardMathSupport.Solomon.Coordinator.ChevQ.KS.TwE6UniqDefs
public import CFSG.HardMathSupport.Solomon.Coordinator.ChevQ.KS.TwE6UniqFacts
public import CFSG.HardMathSupport.Timmesfeld.LangTorus.InnerQuasisimple

public section

namespace CFSG.HardMathSupport.Solomon.Coordinator.ChevQ.E6Three

namespace KSNotAll24

open CFSG.Open CFSG.Blueprint CFSG.Blueprint.Chevalley CFSG.LieType.Chevalley
  CFSG.LieType.Steinberg.Adjoint CFSG.LieType.AlgebraicGroups
  CFSG.LocalAnalysis.ComponentInitial.FourGroupChevalley
  CFSG.HardMathSupport.Timmesfeld.LangTorus CFSG.HardMathSupport.Timmesfeld.CrossChar
  CFSG.HardMathSupport.Dickson.Sec6
  CFSG.HardMathSupport.Solomon.Coordinator.ChevQ.TwE6UniqAbs
open scoped MatrixGroups

set_option linter.unusedSectionVars false

section Shape


theorem pow_mod_three_of_odd {q s : ℕ} (hq : 3 ∣ q + 1) (hs : s % 2 = 1) : q ^ s % 3 = 2 := by
  obtain ⟨m, rfl⟩ : ∃ m, s = 2 * m + 1 := ⟨s / 2, by omega⟩
  have hq2 : q % 3 = 2 := by omega
  have h2 : q ^ 2 % 3 = 1 := by
    rw [Nat.pow_mod, hq2]
  rw [pow_succ, pow_mul, Nat.mul_mod, Nat.pow_mod, h2, hq2]
  simp

variable {L : Type} [Field L] [IsAlgClosed L] {p : ℕ} (S : LangSetup Tag.E6 L p)

theorem exists_unitary_perm_of_odd_orbit {a : Fin Tag.E6.rank → Lˣ}
    (hT : rootDiagUnit Tag.E6 a ∈ S.D.torus) (ha : ∀ j, a j ^ 3 = 1)
    (h1 : rootDiagUnit Tag.E6 a ≠ 1) (i : KernelComponent (rootCharHom a))
    (hi6 : (componentRoots (rootCharHom a) i).ncard = 6)
    {ψ : SL(3, L) →* ModGL Tag.E6 L} {σ : Fin 3 → Fin 3 → Fin Tag.E6.rank → ℤ}
    (hψ : IsSLFrame ψ σ) (hnorm : ∀ x y, x ≠ y → iform (σ x y) (σ x y) = 2)
    (hΨ : componentRoots (rootCharHom a) i = frameRoots σ)
    (hodd : componentOrbitLength S.ρ (componentRoots (rootCharHom a) i) % 2 = 1)
    (h3q : 3 ∣ S.D.q + 1) :
    ∃ π : Equiv.Perm (Fin 3), ∀ x y, x ≠ y →
      (S.ρ : (Fin Tag.E6.rank → ℤ) → _)^[componentOrbitLength S.ρ
        (componentRoots (rootCharHom a) i)] (σ x y) = σ (π y) (π x) := by
  classical
  obtain ⟨hs0, hs, -⟩ := outer_componentOrbitLength_spec S hT i
  set s := componentOrbitLength S.ρ (componentRoots (rootCharHom a) i) with hsdef
  have hnorm' : ∀ x y, x ≠ y → iform (σ x y) (σ x y) = 2 * 1 := fun x y hxy => by
    rw [mul_one]
    exact hnorm x y hxy
  have hmaps : ∀ x y, x ≠ y → (S.ρ : (Fin Tag.E6.rank → ℤ) → _)^[s] (σ x y) ∈ frameRoots σ := by
    intro x y hxy
    have h1' : σ x y ∈ componentRoots (rootCharHom a) i := by
      rw [hΨ]
      exact ⟨x, y, hxy, rfl⟩
    have h2 : (S.ρ : (Fin Tag.E6.rank → ℤ) → _)^[s] (σ x y) ∈
        (S.ρ : (Fin Tag.E6.rank → ℤ) → _)^[s] '' componentRoots (rootCharHom a) i :=
      ⟨_, h1', rfl⟩
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
  rcases hψ.aut_cases (by norm_num) one_ne_zero hnorm' ((S.ρ : (Fin Tag.E6.rank → ℤ) → _)^[s])
      hmaps (hneg s) (iform_rho_iterate S s) with ⟨π, hπ⟩ | ⟨π, hπ⟩
  · exfalso
    obtain ⟨w, hw, hwσ⟩ := hψ.exists_weyl_perm one_ne_zero hnorm' π
    have hinner : twistInner (componentRoots (rootCharHom a) i)
        ((S.ρ : (Fin Tag.E6.rank → ℤ) → _)^[s]) := by
      refine ⟨w, ?_, fun γ hγ => ?_⟩
      · rw [hΨ]
        exact hw
      · rw [hΨ] at hγ
        obtain ⟨x, y, hxy, rfl⟩ := hγ
        rw [hπ x y hxy, hwσ]
    obtain ⟨γ₁, γ₂, hP, hΨeq, hglueAll⟩ := Up34Exc.RD.glue_of_check2 Up34Exc.RD.noG2_E6 73
      Up34Exc.RD.okE6 (by norm_num) Up34Exc.RD.rdCheck2_E6 a ha i hi6
    have ha1 : ∃ j, a j ≠ 1 := by
      by_contra hcon
      push Not at hcon
      apply h1
      have : a = 1 := funext hcon
      rw [this, CFSG.LieType.Chevalley.rootDiagUnit_one]
    obtain ⟨j0, hj0⟩ := ha1
    obtain ⟨ε, hε, hglue⟩ := hglueAll (a j0) (ha j0) hj0
    have hmod := Up34Exc.q_pow_mod_three_of_inner_a2 S hT i hinner hP hΨeq (ha j0) hj0 hε hglue
      ⟨j0, hj0⟩
    have h2 := pow_mod_three_of_odd h3q hodd
    omega
  · exact ⟨π, hπ⟩

theorem exists_unitary_frame_of_odd_orbit (h3 : ((3 : ℕ) : L) ≠ 0) {a : Fin Tag.E6.rank → Lˣ}
    (hT : rootDiagUnit Tag.E6 a ∈ S.D.torus) (ha : ∀ j, a j ^ 3 = 1)
    (h1 : rootDiagUnit Tag.E6 a ≠ 1) (i : KernelComponent (rootCharHom a))
    (hi6 : (componentRoots (rootCharHom a) i).ncard = 6)
    (hodd : componentOrbitLength S.ρ (componentRoots (rootCharHom a) i) % 2 = 1)
    (h3q : 3 ∣ S.D.q + 1) :
    ∃ (ψ : SL(3, L) →* ModGL Tag.E6 L) (σ : Fin 3 → Fin 3 → Fin Tag.E6.rank → ℤ)
      (π : Equiv.Perm (Fin 3)), IsSLFrame ψ σ ∧
      componentRoots (rootCharHom a) i = frameRoots σ ∧
      ∀ x y, x ≠ y → (S.ρ : (Fin Tag.E6.rank → ℤ) → _)^[componentOrbitLength S.ρ
        (componentRoots (rootCharHom a) i)] (σ x y) = σ (π y) (π x) := by
  obtain ⟨ψ, σ, hψ, hnorm, hΨ⟩ := (kac_facts h3 ha).frame i hi6
  obtain ⟨π, hπ⟩ := exists_unitary_perm_of_odd_orbit S hT ha h1 i hi6 hψ hnorm hΨ hodd h3q
  exact ⟨ψ, σ, π, hψ, hΨ, hπ⟩

end Shape

end KSNotAll24

end CFSG.HardMathSupport.Solomon.Coordinator.ChevQ.E6Three
