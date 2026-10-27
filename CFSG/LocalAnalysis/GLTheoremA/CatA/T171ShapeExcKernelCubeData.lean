module

public import CFSG.LocalAnalysis.GLTheoremA.CatA.T171ShapeExcActOuterFix
public import CFSG.ClassicalInvolution.SmallCases.UpgradeCoverClassical
public import CFSG.HardMathSupport.Solomon.Coordinator.InndiagProxy
public import CFSG.HardMathSupport.Timmesfeld.LangTorus.InnerQuasisimpleOrbit
public import CFSG.Monster.B.Fischer.Fi22Order

public section

namespace CFSG.LocalAnalysis.GLTheoremA.T171Sh

open CFSG.Blueprint.Chevalley CFSG.LieType.Chevalley CFSG.LieType.Steinberg.Adjoint
  CFSG.LocalAnalysis.ComponentInitial CFSG.LocalAnalysis.ComponentInitial.FourGroupChevalley
  CFSG.HardMathSupport.Timmesfeld.CrossChar CFSG.HardMathSupport.Timmesfeld.LangTorus
  CFSG.HardMathSupport.Timmesfeld.RootAut CFSG.LieType.AlgebraicGroups
  CFSG.ComponentClassification.OuterAutomorphisms CFSG.GroupActions
  CFSG.ComponentClassification.PerfectAutomorphisms
open scoped Pointwise commutatorElement


theorem frobGL_mem_sup_torus_rootSpan {τ : Tag} {L : Type} [Field L] [IsAlgClosed L] [CharP L 2]
    {a : Fin τ.rank → Lˣ}
    {g : ModGL τ L}
    (hg : g ∈ torusGroup τ L ⊔ rootSpan τ L (kernelRoots (rootCharHom a))) :
    frobGL (τ := τ) (frobeniusEquiv L 2) g ∈
      torusGroup τ L ⊔ rootSpan τ L (kernelRoots (rootCharHom a)) := by
  have h1 : (torusGroup τ L).map (frobGL (τ := τ) (frobeniusEquiv L 2)) ≤ torusGroup τ L := by
    rintro _ ⟨x, hx, rfl⟩
    exact frobGL_mem_torusGroup (frobeniusEquiv L 2) hx
  have h2 : (rootSpan τ L (kernelRoots (rootCharHom a))).map
      (frobGL (τ := τ) (frobeniusEquiv L 2)) ≤ rootSpan τ L (kernelRoots (rootCharHom a)) := by
    rintro _ ⟨x, hx, rfl⟩
    exact frobGL_mem_rootSpan (frobeniusEquiv L 2) hx
  have hle : (torusGroup τ L ⊔ rootSpan τ L (kernelRoots (rootCharHom a))).map
      (frobGL (τ := τ) (frobeniusEquiv L 2)) ≤
      torusGroup τ L ⊔ rootSpan τ L (kernelRoots (rootCharHom a)) := by
    rw [Subgroup.map_sup]
    exact sup_le (h1.trans le_sup_left) (h2.trans le_sup_right)
  exact hle ⟨g, hg, rfl⟩

structure CubeTransferHyps {τ : Tag} {L : Type} [Field L] [IsAlgClosed L] [CharP L 2]
    {p : ℕ} (S : LangSetup τ L p) {a : Fin τ.rank → Lˣ}
    (hT : rootDiagUnit τ a ∈ S.D.torus) (i : KernelComponent (rootCharHom a))
    {s : ℕ} [NeZero s]
    (hs : (S.ρ : (Fin τ.rank → ℤ) → _)^[s] '' componentRoots (rootCharHom a) i =
      componentRoots (rootCharHom a) i)
    (hmin : ∀ k, 0 < k → k < s →
      (S.ρ : (Fin τ.rank → ℤ) → _)^[k] '' componentRoots (rootCharHom a) i ≠
        componentRoots (rootCharHom a) i)
    (hD : TwoDExcFixedData S a i s) : Prop where
  θS : ∀ c : ↥hD.C, (c : ModGL τ L) ∈ rootSpan τ L (componentRoots (rootCharHom a) i)
  θfix : ∀ c : ↥hD.C, iterHom S.D.step s (c : ModGL τ L) = (c : ModGL τ L)
  θY : ∀ g₁ g₁' : ModGL τ L,
    g₁ ∈ rootSpan τ L (componentRoots (rootCharHom a) i) →
    g₁' ∈ rootSpan τ L (componentRoots (rootCharHom a) i) →
    iterHom S.D.step s g₁ * g₁⁻¹ ∈ (outerOrbitFamily S hT i hs hmin).Z →
    iterHom S.D.step s g₁' * g₁'⁻¹ ∈ (outerOrbitFamily S hT i hs hmin).Z →
    ⁅g₁, g₁'⁆ ∈ hD.C.subtype.range
  θZ : ∀ c : ↥hD.C, (c : ModGL τ L) ∈ (outerOrbitFamily S hT i hs hmin).Z →
    c ∈ Subgroup.center ↥hD.C

structure CubeConjData {τ : Tag} {L : Type} [Field L] [IsAlgClosed L] [CharP L 2]
    {p : ℕ} (S : LangSetup τ L p) {a : Fin τ.rank → Lˣ}
    (i : KernelComponent (rootCharHom a)) {s : ℕ} (hD : TwoDExcFixedData S a i s)
    (y : ModGL τ L) where
  g : ModGL τ L
  mem : g ∈ rootSpan τ L (componentRoots (rootCharHom a) i)
  conj : ∀ x ∈ rootSpan τ L (componentRoots (rootCharHom a) i),
    y * x * y⁻¹ = g * x * g⁻¹
  pow_three_mem : g ^ 3 ∈ hD.C
  mul_frob_mem : g * frobGL (τ := τ) (frobeniusEquiv L 2) g ∈ hD.C

end CFSG.LocalAnalysis.GLTheoremA.T171Sh

end
