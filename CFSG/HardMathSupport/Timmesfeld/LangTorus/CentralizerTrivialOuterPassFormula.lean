module

public import CFSG.HardMathSupport.Timmesfeld.LangTorus.CentralizerTrivialOuterLang

public section

namespace CFSG.HardMathSupport.Timmesfeld.LangTorus

open CFSG.Open CFSG.HardMathSupport.Solomon.LocalBalance CFSG.HardMathSupport.Timmesfeld.Coordinator
  CFSG.HardMathSupport.Timmesfeld.CrossChar CFSG.HardMathSupport.Timmesfeld.LocalTwo
  CFSG.Blueprint CFSG.Blueprint.Chevalley CFSG.LieType.Chevalley CFSG.LieType.AlgebraicGroups
  CFSG.RankThree.PartOne.KE CFSG.HardMathSupport.Timmesfeld.DefChar CFSG.RankThree.Chevalley
  CFSG.LocalAnalysis.ComponentInitial CFSG.LocalAnalysis.ComponentInitial.FourGroupChevalley
  CFSG.RankThree.Classical CFSG.LieType.Steinberg.Adjoint CFSG.HardMathSupport.Timmesfeld.RootAut
open scoped MatrixGroups


variable {τ : Tag} {L : Type} [Field L] [IsAlgClosed L] {p : ℕ} (S : LangSetup τ L p)
  {Ψ : Set (Fin τ.rank → ℤ)}

private structure LangData {a : Fin τ.rank → Lˣ}
    (i : KernelComponent (rootCharHom a)) where
  w : WeylGroup τ
  hw : w ∈ componentWeylGroup (componentRoots (rootCharHom a) i)
  f : (Fin τ.rank → ℤ) → Fin τ.rank → ℤ
  z₀ : ModGL τ L
  φ₁ : ModGL τ L →* ModGL τ L
  hf : IsIsometry (componentRoots (rootCharHom a) i) f
  hpos : ∀ γ ∈ posRoots (componentRoots (rootCharHom a) i),
    f γ ∈ posRoots (componentRoots (rootCharHom a) i)
  hpin : OuterPinned φ₁ f
    (S.D.q ^ componentOrbitLength S.ρ (componentRoots (rootCharHom a) i))
  hz₀n : ∀ g, g ∈ rootSpan τ L (componentRoots (rootCharHom a) i) ↔
    z₀ * g * z₀⁻¹ ∈ rootSpan τ L (componentRoots (rootCharHom a) i)
  hφ₁ : ∀ g ∈ rootSpan τ L (componentRoots (rootCharHom a) i),
    iterHom S.D.step (componentOrbitLength S.ρ (componentRoots (rootCharHom a) i))
      (z₀ * g * z₀⁻¹) = z₀ * φ₁ g * z₀⁻¹
  hφ₁S : ∀ g ∈ rootSpan τ L (componentRoots (rootCharHom a) i),
    φ₁ g ∈ rootSpan τ L (componentRoots (rootCharHom a) i)
  hform : ∀ γ, f γ = Nat.iterate (S.ρ : (Fin τ.rank → ℤ) → Fin τ.rank → ℤ)
    (componentOrbitLength S.ρ (componentRoots (rootCharHom a) i)) (w • γ)
  hne : ¬ twistInner (componentRoots (rootCharHom a) i)
    (Nat.iterate (S.ρ : (Fin τ.rank → ℤ) → Fin τ.rank → ℤ)
      (componentOrbitLength S.ρ (componentRoots (rootCharHom a) i))) →
    ∃ γ ∈ componentRoots (rootCharHom a) i, f γ ≠ γ

private theorem iterHom_step_mem_rootSpan (hΨ : IsRootComponent Ψ) {s : ℕ}
    (hs : (S.ρ : (Fin τ.rank → ℤ) → Fin τ.rank → ℤ)^[s] '' Ψ = Ψ) :
    ∀ g ∈ rootSpan τ L Ψ, iterHom S.D.step s g ∈ rootSpan τ L Ψ := by
  have hmap : (rootSpan τ L Ψ).map (iterHom S.D.step s) ≤ rootSpan τ L Ψ := by
    refine map_rootSpan_le_of_forall fun γ hγ t => ?_
    obtain ⟨μ, -, hμ⟩ := iter_step_pinnedX S s (hΨ.isRoot γ hγ)
    rw [iterHom_eq_iterate, hμ]
    refine pinnedX_mem_rootSpan ?_ _
    rw [← hs]
    exact Set.mem_image_of_mem _ hγ
  exact fun g hg => hmap ⟨g, hg, rfl⟩

private theorem exists_ne_of_not_twistInner (hΨ : IsRootComponent Ψ) {w : WeylGroup τ}
    (hwW : w ∈ componentWeylGroup Ψ)
    (hout : ¬ twistInner Ψ ((S.ρ : (Fin τ.rank → ℤ) → Fin τ.rank → ℤ)^[
      componentOrbitLength S.ρ Ψ])) :
    ∃ γ ∈ Ψ, (S.ρ : (Fin τ.rank → ℤ) → Fin τ.rank → ℤ)^[
      componentOrbitLength S.ρ Ψ] (w • γ) ≠ γ := by
  by_contra hfix
  push Not at hfix
  apply hout
  refine ⟨w⁻¹, Subgroup.closure_mono ?_ (inv_mem hwW), fun γ hγ => ?_⟩
  · rintro _ ⟨β, hβ, rfl⟩
    exact ⟨β, simpleRoots_subset hβ, rfl⟩
  · have hβ := smul_mem_of_mem_componentWeylGroup hΨ (inv_mem hwW) γ hγ
    have h1 := hfix _ hβ
    simp only [smul_inv_smul] at h1
    exact h1

private theorem nonempty_langData {a : Fin τ.rank → Lˣ}
    (hT : rootDiagUnit τ a ∈ S.D.torus) (i : KernelComponent (rootCharHom a)) :
    Nonempty (LangData S i) := by
  classical
  obtain ⟨hs0, hs, -⟩ := outer_componentOrbitLength_spec S hT i
  set s := componentOrbitLength S.ρ (componentRoots (rootCharHom a) i) with hsdef
  have hΨ := isRootComponent_componentRoots (χ := rootCharHom a) i
  have hπ := outer_isIsometry_rho S hs
  obtain ⟨w, hwW, hwpos⟩ := exists_mem_componentWeylGroup_posRoots hΨ hπ
  have hf : IsIsometry (componentRoots (rootCharHom a) i)
      (fun γ => (S.ρ : (Fin τ.rank → ℤ) → _)^[s] (w • γ)) := hπ.comp_smul hΨ hwW
  have hwcl : w ∈ Subgroup.closure {r : WeylGroup τ |
      ∃ γ ∈ componentRoots (rootCharHom a) i, r = rootReflection γ} := by
    refine Subgroup.closure_mono ?_ hwW
    rintro _ ⟨β, hβ, rfl⟩
    exact ⟨β, simpleRoots_subset hβ, rfl⟩
  obtain ⟨c, hcS, hcN, hcw⟩ := exists_lift_mem_closure_reflections (L := L) i hwcl
  have hcK : c ∈ rootSpan τ L (kernelRoots (rootCharHom a)) :=
    rootSpan_mono (fun γ hγ => hγ.1) hcS
  obtain ⟨z₀, hz₀n, hz₀⟩ := outer_exists_lang_conj S hT hs0 hcK
  have hpin : OuterPinned ((iterHom S.D.step s).comp (MulAut.conj c).toMonoidHom)
      (fun γ => (S.ρ : (Fin τ.rank → ℤ) → _)^[s] (w • γ)) (S.D.q ^ s) := by
    have h1 := (outerPinned_conj hcN).comp (outerPinned_step S s)
    rw [weylQuotientHom_eq hcw, one_mul] at h1
    exact h1
  have hρS := iterHom_step_mem_rootSpan (S := S) hΨ hs
  let d : LangData S i :=
    { w := w
      hw := hwW
      f := fun γ => (S.ρ : (Fin τ.rank → ℤ) → _)^[s] (w • γ)
      z₀ := z₀
      φ₁ := (iterHom S.D.step s).comp (MulAut.conj c).toMonoidHom
      hf := hf
      hpos := hwpos
      hpin := hpin
      hz₀n := hz₀n i
      hφ₁ := fun g _ => hz₀ g
      hφ₁S := fun g hg => hρS _ (mul_mem (mul_mem hcS hg) (inv_mem hcS))
      hform := fun γ => by rw [hsdef]
      hne := exists_ne_of_not_twistInner (S := S) hΨ hwW }
  exact ⟨d⟩

theorem outer_exists_lang_data_formula {a : Fin τ.rank → Lˣ}
    (hT : rootDiagUnit τ a ∈ S.D.torus) (i : KernelComponent (rootCharHom a)) :
    ∃ (f : (Fin τ.rank → ℤ) → Fin τ.rank → ℤ) (z₀ : ModGL τ L) (φ₁ : ModGL τ L →* ModGL τ L),
      IsIsometry (componentRoots (rootCharHom a) i) f ∧
      (∀ γ ∈ posRoots (componentRoots (rootCharHom a) i),
        f γ ∈ posRoots (componentRoots (rootCharHom a) i)) ∧
      OuterPinned φ₁ f (S.D.q ^ componentOrbitLength S.ρ (componentRoots (rootCharHom a) i)) ∧
      (∀ g, g ∈ rootSpan τ L (componentRoots (rootCharHom a) i) ↔
        z₀ * g * z₀⁻¹ ∈ rootSpan τ L (componentRoots (rootCharHom a) i)) ∧
      (∀ g ∈ rootSpan τ L (componentRoots (rootCharHom a) i),
        iterHom S.D.step (componentOrbitLength S.ρ (componentRoots (rootCharHom a) i))
          (z₀ * g * z₀⁻¹) = z₀ * φ₁ g * z₀⁻¹) ∧
      (∀ g ∈ rootSpan τ L (componentRoots (rootCharHom a) i),
        φ₁ g ∈ rootSpan τ L (componentRoots (rootCharHom a) i)) ∧
      (¬ twistInner (componentRoots (rootCharHom a) i)
          ((S.ρ : (Fin τ.rank → ℤ) → _)^[componentOrbitLength S.ρ
            (componentRoots (rootCharHom a) i)]) →
        ∃ γ ∈ componentRoots (rootCharHom a) i, f γ ≠ γ) ∧
      ∃ w ∈ componentWeylGroup (componentRoots (rootCharHom a) i),
        ∀ γ, f γ = (S.ρ : (Fin τ.rank → ℤ) → _)^[componentOrbitLength S.ρ
          (componentRoots (rootCharHom a) i)] (w • γ) := by
  classical
  let d := Classical.choice (nonempty_langData S hT i)
  exact ⟨d.f, d.z₀, d.φ₁, d.hf, d.hpos, d.hpin, d.hz₀n, d.hφ₁, d.hφ₁S, d.hne,
    d.w, d.hw, d.hform⟩

end CFSG.HardMathSupport.Timmesfeld.LangTorus
