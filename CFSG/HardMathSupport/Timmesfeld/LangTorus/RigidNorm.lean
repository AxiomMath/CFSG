module

public import CFSG.HardMathSupport.Timmesfeld.LangTorus.InnerQuasisimple

public section

namespace CFSG.HardMathSupport.Timmesfeld.LangTorus

open CFSG.Open CFSG.Blueprint.Chevalley CFSG.LieType.Chevalley CFSG.LieType.Steinberg.Adjoint
  CFSG.LocalAnalysis.ComponentInitial
  CFSG.LocalAnalysis.ComponentInitial.FourGroupChevalley CFSG.LieType.AlgebraicGroups
  CFSG.HardMathSupport.Timmesfeld.CrossChar
open scoped commutatorElement

set_option linter.unusedSectionVars false

section NormMem

variable {τ : Tag} {L : Type} [Field L] [IsAlgClosed L] {p : ℕ} (S : LangSetup τ L p)
  {a : Fin τ.rank → Lˣ}

theorem norm_mem_rationalComponentT (hT : rootDiagUnit τ a ∈ S.D.torus)
    (i : KernelComponent (rootCharHom a)) {s : ℕ} [NeZero s]
    (hs : (S.ρ : (Fin τ.rank → ℤ) → _)^[s] '' componentRoots (rootCharHom a) i =
      componentRoots (rootCharHom a) i)
    (hmin : ∀ k, 0 < k → k < s →
      (S.ρ : (Fin τ.rank → ℤ) → _)^[k] '' componentRoots (rootCharHom a) i ≠
        componentRoots (rootCharHom a) i)
    (σ : L ≃+* L) (z : ModGL τ L)
    (hnorm : ∀ j : KernelComponent (rootCharHom a), ∀ g : ModGL τ L,
      g ∈ rootSpan τ L (componentRoots (rootCharHom a) j) ↔
        z * g * z⁻¹ ∈ rootSpan τ L (componentRoots (rootCharHom a) j))
    (hz : ∀ g ∈ rootSpan τ L (componentRoots (rootCharHom a) i),
      iterHom S.D.step s (z * g * z⁻¹) = z * frobGL σ g * z⁻¹)
    (hperfC : Group.IsPerfect (componentRootSpan (fixSubfield σ) (rootCharHom a) i)) :
    ∀ (x : componentRootSpan (fixSubfield σ) (rootCharHom a) i)
      (y : (outerOrbitFamily S hT i hs hmin).S 0),
    (y : ModGL τ L) = z * baseChangeGL (fixSubfield σ).subtype (x : ModGL τ (fixSubfield σ)) * z⁻¹ →
    (outerOrbitFamily S hT i hs hmin).norm y ∈
      rationalComponent S.ρ S.Γ (rootCharHom a) i := by
  classical
  set P := outerOrbitFamily S hT i hs hmin with hP
  set ι := baseChangeGL (τ := τ) (fixSubfield σ).subtype with hι
  set Cg := componentRootSpan (fixSubfield σ) (rootCharHom a) i with hCg
  have hP0 : P.S 0 = rootSpan τ L (componentRoots (rootCharHom a) i) := by
    rw [hP, outerOrbitFamily_S, ZMod.val_zero]
    simp only [Function.iterate_zero, id_eq, Set.image_id']
  have hιC : ∀ x ∈ Cg, ι x ∈ CQ σ i := by
    intro x hx
    rw [CQ_eq_map]
    exact ⟨x, hx, rfl⟩
  have hιS : ∀ x ∈ Cg, ι x ∈ rootSpan τ L (componentRoots (rootCharHom a) i) :=
    fun x hx => CQ_le_rootSpan σ i (hιC x hx)
  let θ₀ : Cg →* P.S 0 :=
    ((MulAut.conj z).toMonoidHom.comp (ι.comp Cg.subtype)).codRestrict (P.S 0) fun x => by
      rw [hP0]
      exact (hnorm i _).1 (hιS x.1 x.2)
  have hθ₀ : ∀ x : Cg, ((θ₀ x : P.S 0) : ModGL τ L) = z * ι x.1 * z⁻¹ := fun x => rfl
  have hfix : ∀ x : Cg, iterHom S.D.step s ((θ₀ x : P.S 0) : ModGL τ L) = (θ₀ x : P.S 0) := by
    intro x
    rw [hθ₀, hz _ (hιS x.1 x.2), frobGL_eq_self_of_mem_CQ σ i (hιC x.1 x.2)]
  intro x y hy
  rw [show y = θ₀ x from Subtype.ext hy]
  exact outer_norm_mem_rationalComponent S hT i hs hmin hperfC θ₀ hfix x

end NormMem

end CFSG.HardMathSupport.Timmesfeld.LangTorus
