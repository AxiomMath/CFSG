module

public import CFSG.HardMathSupport.Timmesfeld.CrossChar.TwCompSUAut
public import CFSG.CGT.PushingUpLit.Transport
public import CFSG.ClassicalInvolution.SmallCases.UpgradeCoverClassical
public import CFSG.HardMathSupport.Solomon.LocalBalance.Lemma54
public import CFSG.HardMathSupport.Timmesfeld.LangTorus.CentralizerTrivialOuterRoots
public import CFSG.LieType.SeitzGeneration.SubfieldPairSUPhan
public import CFSG.LocalAnalysis.AGLEmbedding.SeitzEqTwo.DescentE
public import CFSG.LocalAnalysis.RankTwoShapes.UnitaryFour.Bridge
public import CFSG.LocalAnalysis.SeitzReduction.EPilotPosition
public import CFSG.Quasithin.Vol2.Ch10SecKGA318
public import CFSG.Quasithin.Vol2.Ch11SecOE5B
public import CFSG.RankThree.PartTwo.KFacts.KS21Mult
public import CFSG.RankThree.PartTwo.Sec4.Census.Item44TwoCoverModels

public section

namespace CFSG.HardMathSupport.Solomon.Coordinator.ChevQ.E6Three

namespace KSConn

open CFSG.Blueprint.Chevalley CFSG.LieType.Chevalley CFSG.LieType.AlgebraicGroups
  CFSG.LieType.Steinberg.Adjoint CFSG.HardMathSupport.Timmesfeld.CrossChar
  CFSG.HardMathSupport.Timmesfeld.LangTorus
  CFSG.LocalAnalysis.ComponentInitial CFSG.LocalAnalysis.ComponentInitial.FourGroupChevalley
open scoped MatrixGroups

set_option linter.unusedSectionVars false


section Perm

variable {L : Type} [Field L] {ν : ℕ}

theorem exists_perm_of_mem_kernelReflectionGroup {a : Fin Tag.E6.rank → Lˣ}
    (i : KernelComponent (rootCharHom a)) {ψ : SL(ν, L) →* ModGL Tag.E6 L}
    {σ : Fin ν → Fin ν → Fin Tag.E6.rank → ℤ} (hψ : IsSLFrame ψ σ)
    (hnorm : ∀ x y, x ≠ y → iform (σ x y) (σ x y) = 2)
    (hΨ : componentRoots (rootCharHom a) i = frameRoots σ) {u : WeylGroup Tag.E6}
    (hu : u ∈ kernelReflectionGroup a) :
    ∃ π : Equiv.Perm (Fin ν), ∀ x y, x ≠ y → u • σ x y = σ (π x) (π y) := by
  have hnorm' : ∀ x y, x ≠ y → iform (σ x y) (σ x y) = 2 * 1 := by
    intro x y hxy
    rw [hnorm x y hxy, mul_one]
  induction hu using Subgroup.closure_induction with
  | mem r hr =>
    obtain ⟨w, j, hγ, rfl⟩ := hr
    rw [conj_simple_eq_rootReflection]
    set γ := w • (Pi.single j 1 : Fin Tag.E6.rank → ℤ) with hγdef
    have hγk : γ ∈ kernelRoots (rootCharHom a) := hγ
    by_cases hcls : (⟦⟨γ, hγk⟩⟧ : KernelComponent (rootCharHom a)) = i
    · have hγΨ : γ ∈ componentRoots (rootCharHom a) i := ⟨hγk, hcls⟩
      rw [hΨ] at hγΨ
      obtain ⟨x₀, y₀, hxy, hγσ⟩ := hγΨ
      rw [hγσ]
      exact ⟨Equiv.swap x₀ y₀, fun x y _ =>
        hψ.rootReflection_smul one_ne_zero hnorm' hxy x y⟩
    · refine ⟨1, fun x y hxy => ?_⟩
      have hσ : σ x y ∈ componentRoots (rootCharHom a) i := by
        rw [hΨ]
        exact ⟨x, y, hxy, rfl⟩
      have hσk : σ x y ∈ kernelRoots (rootCharHom a) := hσ.1
      have hi : (⟦⟨σ x y, hσk⟩⟧ : KernelComponent (rootCharHom a)) = i := hσ.2
      have horth : iform γ (σ x y) = 0 := by
        refine iform_eq_zero_of_mk_ne (α := ⟨γ, hγk⟩) (β := ⟨σ x y, hσk⟩) ?_
        rw [hi]
        exact hcls
      have hγr : IsRoot Tag.E6 γ := hγk.1
      rw [rootReflection_smul hγr, corootPair, horth]
      simp
  | one => exact ⟨1, fun x y _ => by simp⟩
  | mul u₁ u₂ _ _ h₁ h₂ =>
    obtain ⟨π₁, hπ₁⟩ := h₁
    obtain ⟨π₂, hπ₂⟩ := h₂
    refine ⟨π₁ * π₂, fun x y hxy => ?_⟩
    have hne : π₂ x ≠ π₂ y := fun h => hxy (π₂.injective h)
    rw [mul_smul, hπ₂ x y hxy, hπ₁ _ _ hne]
    rfl
  | inv u _ h =>
    obtain ⟨π, hπ⟩ := h
    refine ⟨π.symm, fun x y hxy => ?_⟩
    have hne : π.symm x ≠ π.symm y := fun h' => hxy (π.symm.injective h')
    rw [inv_smul_eq_iff, hπ _ _ hne]
    simp

theorem exists_unitary_perm_of_rho_eq_neg {a : Fin Tag.E6.rank → Lˣ}
    (i : KernelComponent (rootCharHom a)) {ψ : SL(ν, L) →* ModGL Tag.E6 L}
    {σ : Fin ν → Fin ν → Fin Tag.E6.rank → ℤ} (hψ : IsSLFrame ψ σ)
    (hnorm : ∀ x y, x ≠ y → iform (σ x y) (σ x y) = 2)
    (hΨ : componentRoots (rootCharHom a) i = frameRoots σ)
    (ρ : Equiv.Perm (Fin Tag.E6.rank → ℤ)) {u : WeylGroup Tag.E6}
    (hu : u ∈ kernelReflectionGroup a) (hρ : ∀ γ, IsRoot Tag.E6 γ → ρ γ = -(u • γ)) :
    ∃ π : Equiv.Perm (Fin ν), ∀ x y, x ≠ y → ρ (σ x y) = σ (π y) (π x) := by
  obtain ⟨π, hπ⟩ := exists_perm_of_mem_kernelReflectionGroup i hψ hnorm hΨ hu
  refine ⟨π, fun x y hxy => ?_⟩
  rw [hρ _ (hψ.isRoot x y hxy), hπ x y hxy, hψ.neg (π x) (π y)]

end Perm

end KSConn

end CFSG.HardMathSupport.Solomon.Coordinator.ChevQ.E6Three
