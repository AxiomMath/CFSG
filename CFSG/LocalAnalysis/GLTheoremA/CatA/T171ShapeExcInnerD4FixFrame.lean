module

public import CFSG.LocalAnalysis.GLTheoremA.CatA.T171ShapeExcActOuterFix
public import CFSG.HardMathSupport.Timmesfeld.LangTorus.InnerQuasisimple

public section

namespace CFSG.LocalAnalysis.GLTheoremA.T171Sh

open CFSG.Blueprint.Chevalley CFSG.LieType.Chevalley CFSG.LieType.AlgebraicGroups
  CFSG.LocalAnalysis.ComponentInitial CFSG.LocalAnalysis.ComponentInitial.FourGroupChevalley
  CFSG.HardMathSupport.Timmesfeld.LangTorus CFSG.HardMathSupport.Timmesfeld.CrossChar
  CFSG.HardMathSupport.Timmesfeld.RootAut CFSG.GroupActions
open scoped Pointwise commutatorElement


variable {τ : Tag} {L : Type} [Field L] [IsAlgClosed L] {p : ℕ} (S : LangSetup τ L p)
  {a : Fin τ.rank → Lˣ}

theorem fixedPointSubgroup_eq_map_CQ (i : KernelComponent (rootCharHom a)) {s : ℕ}
    {σ : L ≃+* L} {z : ModGL τ L}
    (hnorm : ∀ j : KernelComponent (rootCharHom a), ∀ g : ModGL τ L,
      g ∈ rootSpan τ L (componentRoots (rootCharHom a) j) ↔
        z * g * z⁻¹ ∈ rootSpan τ L (componentRoots (rootCharHom a) j))
    (hz : ∀ g ∈ rootSpan τ L (componentRoots (rootCharHom a) i),
      iterHom S.D.step s (z * g * z⁻¹) = z * frobGL σ g * z⁻¹)
    (hCQ : ∀ y ∈ rootSpan τ L (componentRoots (rootCharHom a) i), frobGL σ y = y →
      y ∈ CQ σ i) :
    fixedPointSubgroup (iterHom S.D.step s)
        (rootSpan τ L (componentRoots (rootCharHom a) i)) =
      (CQ σ i).map (MulAut.conj z).toMonoidHom := by
  ext x
  constructor
  · intro hx
    obtain ⟨hxU, hxF⟩ := hx
    obtain ⟨y₀, hy₀⟩ : ∃ y₀ : ModGL τ L, y₀ = z⁻¹ * x * z := ⟨_, rfl⟩
    have e : z * y₀ * z⁻¹ = x := by rw [hy₀]; group
    have hy₀U : y₀ ∈ rootSpan τ L (componentRoots (rootCharHom a) i) :=
      (hnorm i y₀).2 (by rw [e]; exact hxU)
    have h1 := hz y₀ hy₀U
    rw [e, hxF] at h1
    have hfix : frobGL σ y₀ = y₀ := by
      calc frobGL σ y₀ = z⁻¹ * (z * frobGL σ y₀ * z⁻¹) * z := by group
        _ = z⁻¹ * x * z := by rw [← h1]
        _ = y₀ := hy₀.symm
    exact ⟨y₀, hCQ y₀ hy₀U hfix, e⟩
  · rintro ⟨y, hyC, rfl⟩
    refine ⟨(hnorm i y).1 (CQ_le_rootSpan σ i hyC), ?_⟩
    have h := hz y (CQ_le_rootSpan σ i hyC)
    rw [frobGL_eq_self_of_mem_CQ σ i hyC] at h
    show iterHom S.D.step s (z * y * z⁻¹) = z * y * z⁻¹
    exact h

theorem twoDExcFixedPointsPerfect_of_isPerfect_CQ (i : KernelComponent (rootCharHom a))
    {s : ℕ} {σ : L ≃+* L} {z : ModGL τ L}
    (hnorm : ∀ j : KernelComponent (rootCharHom a), ∀ g : ModGL τ L,
      g ∈ rootSpan τ L (componentRoots (rootCharHom a) j) ↔
        z * g * z⁻¹ ∈ rootSpan τ L (componentRoots (rootCharHom a) j))
    (hz : ∀ g ∈ rootSpan τ L (componentRoots (rootCharHom a) i),
      iterHom S.D.step s (z * g * z⁻¹) = z * frobGL σ g * z⁻¹)
    (hCQ : ∀ y ∈ rootSpan τ L (componentRoots (rootCharHom a) i), frobGL σ y = y →
      y ∈ CQ σ i)
    (hperf : Group.IsPerfect ↥(CQ σ i)) :
    TwoDExcFixedPointsPerfect S a i s := by
  unfold TwoDExcFixedPointsPerfect
  rw [fixedPointSubgroup_eq_map_CQ S i hnorm hz hCQ]
  haveI := hperf
  let e := Subgroup.equivMapOfInjective (CQ σ i) (MulAut.conj z).toMonoidHom
    (MulAut.conj z).injective
  exact Group.IsPerfect.ofSurjective (f := e.toMonoidHom) e.surjective

end CFSG.LocalAnalysis.GLTheoremA.T171Sh

end
