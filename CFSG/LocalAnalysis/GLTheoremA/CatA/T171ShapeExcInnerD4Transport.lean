module

public import CFSG.LocalAnalysis.GLTheoremA.CatA.T171ShapeExcActNorm
public import CFSG.LocalAnalysis.ComponentClassification.OuterAutomorphismsCongr

public section

namespace CFSG.LocalAnalysis.GLTheoremA.T171Sh

open CFSG.Blueprint.Chevalley CFSG.LieType.Chevalley CFSG.LieType.Steinberg.Adjoint
  CFSG.LocalAnalysis.ComponentInitial CFSG.LocalAnalysis.ComponentInitial.FourGroupChevalley
  CFSG.HardMathSupport.Timmesfeld.CrossChar CFSG.HardMathSupport.Timmesfeld.LangTorus
  CFSG.LieType.AlgebraicGroups
  CFSG.ComponentClassification.OuterAutomorphisms
  CFSG.ComponentClassification.PerfectAutomorphisms
  CFSG.ComponentClassification.PerfectCentralQuotient CFSG.GroupActions
open scoped Pointwise commutatorElement

section Surjection

variable {C T : Type*} [Group C] [Group T]

theorem centerQuotientHom_mem_inner_iff_of_surjective [Group.IsPerfect C]
    (π : C →* T) (hπ : Function.Surjective π) (hker : π.ker ≤ Subgroup.center C)
    {α : MulAut C} {γ : MulAut T} (hαγ : ∀ c, γ (π c) = π (α c)) :
    centerQuotientHom T γ ∈ inner (T ⧸ Subgroup.center T) ↔
      centerQuotientHom C α ∈ inner (C ⧸ Subgroup.center C) := by
  rw [← congr_centerQuotientHom_of_surjective π hπ hker hαγ]
  exact congr_mem_inner_iff (equivalence π hπ hker) _

theorem centerQuotientHom_mem_inner_of_central_surjection [Group.IsPerfect C]
    (π : C →* T) (hπ : Function.Surjective π) (hker : π.ker ≤ Subgroup.center C)
    {α : MulAut C} {γ : MulAut T} (hα : α ∈ inner C) (hαγ : ∀ c, γ (π c) = π (α c)) :
    centerQuotientHom T γ ∈ inner (T ⧸ Subgroup.center T) :=
  (centerQuotientHom_mem_inner_iff_of_surjective π hπ hker hαγ).2
    (centerQuotient_inner_le hα)

end Surjection

section NormTransfer


variable {τ : Tag} {L : Type} [Field L] [IsAlgClosed L] {p : ℕ} (S : LangSetup τ L p)
  {a : Fin τ.rank → Lˣ}

private theorem exists_norm_hom_of_hom_T'
    (hT : rootDiagUnit τ a ∈ S.D.torus)
    (i : KernelComponent (rootCharHom a)) {s : ℕ} [NeZero s]
    (hs : (S.ρ : (Fin τ.rank → ℤ) → _)^[s] '' componentRoots (rootCharHom a) i =
      componentRoots (rootCharHom a) i)
    (hmin : ∀ k, 0 < k → k < s →
      (S.ρ : (Fin τ.rank → ℤ) → _)^[k] '' componentRoots (rootCharHom a) i ≠
        componentRoots (rootCharHom a) i)
    {C : Type*} [Group C] (θ : C →* ModGL τ L)
    (hθS : ∀ c, θ c ∈ rootSpan τ L (componentRoots (rootCharHom a) i))
    (hθfix : ∀ c, iterHom S.D.step s (θ c) = θ c)
    (hθY : ∀ g g' : ModGL τ L, g ∈ rootSpan τ L (componentRoots (rootCharHom a) i) →
      g' ∈ rootSpan τ L (componentRoots (rootCharHom a) i) →
      iterHom S.D.step s g * g⁻¹ ∈ (outerOrbitFamily S hT i hs hmin).Z →
      iterHom S.D.step s g' * g'⁻¹ ∈ (outerOrbitFamily S hT i hs hmin).Z → ⁅g, g'⁆ ∈ θ.range)
    (hθZ : ∀ c, θ c ∈ (outerOrbitFamily S hT i hs hmin).Z → c ∈ Subgroup.center C)
    {y : ModGL τ L}
    (hyZ : y ∈ torusGroup τ L ⊔ rootSpan τ L (kernelRoots (rootCharHom a)))
    (hyF : S.D.step y = y)
    {α : MulAut C} (hθα : ∀ c, θ (α c) = y * θ c * y⁻¹) :
    ∃ f : C →* ModGL τ L,
      rationalComponent S.ρ S.Γ (rootCharHom a) i ≤ f.range ∧
      f.ker ≤ Subgroup.center C ∧
      (Group.IsPerfect C → f.range ≤ rationalComponent S.ρ S.Γ (rootCharHom a) i) ∧
      (∀ c, f (α c) = y * f c * y⁻¹) := by
  classical
  set P := outerOrbitFamily S hT i hs hmin with hP
  set Ψ := componentRoots (rootCharHom a) i with hΨ
  have hP0 : P.S 0 = rootSpan τ L Ψ := by
    rw [hP, outerOrbitFamily_S, ZMod.val_zero]
    simp only [Function.iterate_zero, id_eq, Set.image_id']
    rfl
  let θ₀ : C →* P.S 0 := θ.codRestrict (P.S 0) fun c => by
    rw [hP0]
    exact hθS c
  have hθ₀ : ∀ c, ((θ₀ c : P.S 0) : ModGL τ L) = θ c := fun c => rfl
  let f : C →* ModGL τ L := P.norm.comp θ₀
  have hfix : ∀ c, iterHom S.D.step s ((θ₀ c : P.S 0) : ModGL τ L) = θ₀ c := fun c => by
    rw [hθ₀]; exact hθfix c
  have hYW : ⁅P.Y, P.Y⁆ ≤ θ.range := by
    rw [Subgroup.commutator_le]
    intro u hu u' hu'
    obtain ⟨hu0, huZ⟩ := P.mem_Y.1 hu
    obtain ⟨hu0', huZ'⟩ := P.mem_Y.1 hu'
    rw [hP0] at hu0 hu0'
    exact hθY u u' hu0 hu0' huZ huZ'
  have hΓM : S.Γ ≤ S.D.model := Subgroup.commutator_le_self _
  have hrsA : rationalSpan S.ρ S.Γ (rootCharHom a) i ≤ P.Afix := by
    intro x hx
    obtain ⟨hx1, hx2⟩ := Subgroup.mem_inf.1 hx
    refine ⟨?_, (hΓM hx2).2⟩
    rw [hP, outerOrbitFamily_A]
    exact hx1
  have hle : rationalComponent S.ρ S.Γ (rootCharHom a) i ≤ f.range := by
    intro g hg
    have h1 := P.commutator_Afix_le (Subgroup.commutator_mono hrsA hrsA hg)
    obtain ⟨y', hyY, rfl⟩ := P.mem_normImage.1 h1
    obtain ⟨c, hc⟩ := hYW hyY
    refine ⟨c, ?_⟩
    change P.norm (θ₀ c) = P.norm y'
    congr 1
    exact Subtype.ext hc
  have hker : f.ker ≤ Subgroup.center C := by
    intro c hc
    have h1 : P.norm (θ₀ c) = 1 := hc
    exact hθZ c (P.mem_Z_of_norm_eq_one h1)
  have hperf_le : Group.IsPerfect C →
      f.range ≤ rationalComponent S.ρ S.Γ (rootCharHom a) i := by
    intro hperf
    rintro _ ⟨x, rfl⟩
    exact outer_norm_mem_rationalComponent S hT i hs hmin hperf θ₀ hfix x
  have hfα : ∀ c, f (α c) = y * f c * y⁻¹ := by
    intro c
    change P.norm (θ₀ (α c)) = y * P.norm (θ₀ c) * y⁻¹
    refine cycFamily_norm_conj P hyF ?_
    rw [hθ₀ (α c), hθ₀ c, hθα c]
  exact ⟨f, hle, hker, hperf_le, hfα⟩

theorem centerQuotientHom_subgroupStabRestrict_mem_inner_of_norm
    (hT : rootDiagUnit τ a ∈ S.D.torus)
    (i : KernelComponent (rootCharHom a)) {s : ℕ} [NeZero s]
    (hs : (S.ρ : (Fin τ.rank → ℤ) → _)^[s] '' componentRoots (rootCharHom a) i =
      componentRoots (rootCharHom a) i)
    (hmin : ∀ k, 0 < k → k < s →
      (S.ρ : (Fin τ.rank → ℤ) → _)^[k] '' componentRoots (rootCharHom a) i ≠
        componentRoots (rootCharHom a) i)
    {C : Type*} [Group C] (θ : C →* ModGL τ L)
    (hθS : ∀ c, θ c ∈ rootSpan τ L (componentRoots (rootCharHom a) i))
    (hθfix : ∀ c, iterHom S.D.step s (θ c) = θ c)
    (hθY : ∀ g g' : ModGL τ L, g ∈ rootSpan τ L (componentRoots (rootCharHom a) i) →
      g' ∈ rootSpan τ L (componentRoots (rootCharHom a) i) →
      iterHom S.D.step s g * g⁻¹ ∈ (outerOrbitFamily S hT i hs hmin).Z →
      iterHom S.D.step s g' * g'⁻¹ ∈ (outerOrbitFamily S hT i hs hmin).Z → ⁅g, g'⁆ ∈ θ.range)
    (hθZ : ∀ c, θ c ∈ (outerOrbitFamily S hT i hs hmin).Z → c ∈ Subgroup.center C)
    (hperf : Group.IsPerfect C)
    {y : ModGL τ L}
    (hyZ : y ∈ torusGroup τ L ⊔ rootSpan τ L (kernelRoots (rootCharHom a)))
    (hyF : S.D.step y = y)
    (hyStab : MulAut.conj y ∈ CFSG.GroupActions.subgroupStabAut
      (rationalComponent S.ρ S.Γ (rootCharHom a) i))
    (α : MulAut C) (hα : α ∈ inner C)
    (hθα : ∀ c, θ (α c) = y * θ c * y⁻¹) :
    centerQuotientHom ↥(rationalComponent S.ρ S.Γ (rootCharHom a) i)
        (CFSG.GroupActions.subgroupStabRestrict
          (rationalComponent S.ρ S.Γ (rootCharHom a) i)
          ⟨MulAut.conj y, hyStab⟩) ∈
      inner (↥(rationalComponent S.ρ S.Γ (rootCharHom a) i) ⧸
        Subgroup.center ↥(rationalComponent S.ρ S.Γ (rootCharHom a) i)) := by
  classical
  set R := rationalComponent S.ρ S.Γ (rootCharHom a) i with hR
  obtain ⟨f, hle, hker, hperf_le, hfα⟩ := exists_norm_hom_of_hom_T' S hT i hs hmin θ
    hθS hθfix hθY hθZ hyZ hyF hθα
  have hfr : f.range = R := le_antisymm (hperf_le hperf) hle
  let π : C →* R := f.codRestrict R fun c => by
    rw [← hfr]
    exact ⟨c, rfl⟩
  have hπsurj : Function.Surjective π := by
    intro r
    have hr : (r : ModGL τ L) ∈ f.range := by
      rw [hfr]
      exact r.2
    obtain ⟨c, hc⟩ := hr
    exact ⟨c, Subtype.ext hc⟩
  have hπker : π.ker ≤ Subgroup.center C := by
    intro c hc
    apply hker
    have hc' : f c = 1 := by
      simpa [π] using congrArg Subtype.val hc
    exact MonoidHom.mem_ker.mpr hc'
  let γ : MulAut R := CFSG.GroupActions.subgroupStabRestrict R ⟨MulAut.conj y, hyStab⟩
  have hαγ : ∀ c, γ (π c) = π (α c) := by
    intro c
    apply Subtype.ext
    change ((γ (π c) : R) : ModGL τ L) = ((π (α c) : R) : ModGL τ L)
    change ((CFSG.GroupActions.subgroupStabRestrict R ⟨MulAut.conj y, hyStab⟩)
      (π c) : ModGL τ L) = ((π (α c) : R) : ModGL τ L)
    rw [CFSG.GroupActions.subgroupStabRestrict_apply]
    change (MulAut.conj y) ((π c : R) : ModGL τ L) = ((π (α c) : R) : ModGL τ L)
    rw [MulAut.conj_apply]
    exact (hfα c).symm
  change centerQuotientHom R
      (CFSG.GroupActions.subgroupStabRestrict R ⟨MulAut.conj y, hyStab⟩) ∈
    inner (R ⧸ Subgroup.center R)
  exact centerQuotientHom_mem_inner_of_central_surjection π hπsurj hπker hα hαγ

end NormTransfer

end CFSG.LocalAnalysis.GLTheoremA.T171Sh

end
