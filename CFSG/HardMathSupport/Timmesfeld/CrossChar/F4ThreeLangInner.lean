module

public import CFSG.HardMathSupport.Timmesfeld.Steinberg.ThreeCharF4
public import CFSG.HardMathSupport.Timmesfeld.LangTorus.InnerQuasisimple
public import CFSG.HardMathSupport.Timmesfeld.CrossChar.ExcInnerTwTorus
public import CFSG.HardMathSupport.Timmesfeld.Tables.T1b.WeylTorusAct

public section

namespace CFSG.HardMathSupport.Timmesfeld.CrossChar

open CFSG.Blueprint.Chevalley CFSG.LieType.Chevalley CFSG.HardMathSupport.Timmesfeld.LangTorus
  CFSG.LocalAnalysis.ComponentInitial CFSG.LocalAnalysis.ComponentInitial.FourGroupChevalley
  CFSG.LieType.AlgebraicGroups

set_option linter.unusedSectionVars false


section Restrict

variable {τ : Tag} {L : Type} [Field L]

theorem f4Three_smul_mem_component_iff {a : Fin τ.rank → Lˣ}
    (i : KernelComponent (rootCharHom a)) {x : WeylGroup τ}
    (hx : x ∈ Subgroup.closure {s : WeylGroup τ | ∃ γ ∈ componentRoots (rootCharHom a) i,
      s = rootReflection γ}) :
    ∀ γ, x • γ ∈ componentRoots (rootCharHom a) i ↔ γ ∈ componentRoots (rootCharHom a) i := by
  have hΨ := isRootComponent_componentRoots (χ := rootCharHom a) i
  induction hx using Subgroup.closure_induction with
  | mem x hx =>
    obtain ⟨δ, hδ, rfl⟩ := hx
    have hδr := hΨ.isRoot δ hδ
    intro γ
    constructor
    · intro h
      have h1 := hΨ.reflection_mem _ h δ hδ
      rwa [← mul_smul, rootReflection_mul_self hδr, one_smul] at h1
    · intro h
      exact hΨ.reflection_mem γ h δ hδ
  | one => intro γ; rw [one_smul]
  | mul x y _ _ hx hy => intro γ; rw [mul_smul, hx, hy]
  | inv x _ hx => intro γ; rw [← hx (x⁻¹ • γ), smul_inv_smul]

theorem f4Three_exists_restrict {a : Fin τ.rank → Lˣ} (i : KernelComponent (rootCharHom a))
    {u : WeylGroup τ} (hu : u ∈ kernelReflectionGroup a) :
    ∃ u' ∈ Subgroup.closure {s : WeylGroup τ | ∃ γ ∈ componentRoots (rootCharHom a) i,
        s = rootReflection γ},
      ∀ γ ∈ componentRoots (rootCharHom a) i, u • γ = u' • γ := by
  induction hu using Subgroup.closure_induction with
  | mem r hr =>
    obtain ⟨w, j, hwj, rfl⟩ := hr
    have hβk : w • (Pi.single j 1 : Fin τ.rank → ℤ) ∈ kernelRoots (rootCharHom a) := hwj
    rw [← rootReflection_eq_conj rfl]
    by_cases hβi : w • (Pi.single j 1 : Fin τ.rank → ℤ) ∈ componentRoots (rootCharHom a) i
    · exact ⟨_, Subgroup.subset_closure ⟨_, hβi, rfl⟩, fun γ _ => rfl⟩
    · refine ⟨1, one_mem _, fun γ hγ => ?_⟩
      rw [one_smul]
      refine rootReflection_smul_of_iform_eq_zero hβk.1 ?_
      by_contra hne
      obtain ⟨hγk, hγi⟩ := hγ
      exact hβi ⟨hβk, (mk_eq_of_iform_ne_zero (α := ⟨_, hβk⟩) (β := ⟨γ, hγk⟩) hne).trans hγi⟩
  | one => exact ⟨1, one_mem _, fun γ _ => rfl⟩
  | mul x y _ _ hx hy =>
    obtain ⟨x', hx'C, hx'⟩ := hx
    obtain ⟨y', hy'C, hy'⟩ := hy
    refine ⟨x' * y', mul_mem hx'C hy'C, fun γ hγ => ?_⟩
    rw [mul_smul, mul_smul, hy' γ hγ, hx' _ ((f4Three_smul_mem_component_iff i hy'C γ).2 hγ)]
  | inv x _ hx =>
    obtain ⟨x', hx'C, hx'⟩ := hx
    refine ⟨x'⁻¹, inv_mem hx'C, fun γ hγ => ?_⟩
    have h1 : x'⁻¹ • γ ∈ componentRoots (rootCharHom a) i :=
      (f4Three_smul_mem_component_iff i (inv_mem hx'C) γ).2 hγ
    have h2 := hx' _ h1
    rw [smul_inv_smul] at h2
    calc x⁻¹ • γ = x⁻¹ • (x • (x'⁻¹ • γ)) := by rw [h2]
      _ = x'⁻¹ • γ := inv_smul_smul x _

theorem f4Three_mem_rootCharStabilizer_of_roots {a : Fin τ.rank → Lˣ} {w : WeylGroup τ}
    (h : ∀ γ, IsRoot τ γ → rootChar a (w • γ) = rootChar a γ) :
    w ∈ rootCharStabilizerSubgroup a := by
  intro v
  rw [Tables.T1b.smul_eq_sum_single w v, rootChar_sum]
  conv_rhs => rw [Tables.T1b.eq_sum_single v, rootChar_sum]
  refine Finset.prod_congr rfl fun i _ => ?_
  rw [rootChar_zsmul, rootChar_zsmul, h _ (isRoot_single τ i)]

end Restrict

section Steinberg


variable {L : Type} [Field L] [IsAlgClosed L] (S : LangSetup Tag.F4 L 3) {w : WeylGroup Tag.F4}
  (hρ : ∀ γ, IsRoot Tag.F4 γ → S.ρ γ = w • γ) {a : Fin Tag.F4.rank → Lˣ}
  (hE : rootDiagUnit Tag.F4 a ∈ S.E)

include hE in
theorem f4Three_coord_pow_three (i : Fin Tag.F4.rank) : a i ^ 3 = 1 := by
  have h := rootChar_pow_eq_one_of_mem_E S hE (isRoot_single Tag.F4 i)
  rwa [Tables.T1b.rootChar_single] at h

include hρ hE in
theorem f4Three_rootChar_smul {γ : Fin Tag.F4.rank → ℤ} (hγ : IsRoot Tag.F4 γ) :
    rootChar a (w • γ) = rootChar a γ ^ S.D.q := by
  rw [← hρ γ hγ]
  exact S.frob.rootChar_eq a (Subgroup.mem_inf.1 (S.E_le hE)).1 γ hγ

include hρ hE in
theorem f4Three_mem_kernelReflectionGroup_one (hq : S.D.q % 3 = 1) :
    w ∈ kernelReflectionGroup a := by
  rw [← Steinberg.rootCharStabilizerSubgroup_eq_kernelReflectionGroup_F4_three a
    (f4Three_coord_pow_three S hE)]
  refine f4Three_mem_rootCharStabilizer_of_roots fun γ hγ => ?_
  rw [f4Three_rootChar_smul S hρ hE hγ,
    pow_eq_pow_mod _ (rootChar_pow_eq_one_of_mem_E S hE hγ), hq, pow_one]

include hρ hE in
theorem f4Three_mem_kernelReflectionGroup_two (hq : S.D.q % 3 = 2) :
    f4Neg * w ∈ kernelReflectionGroup a := by
  rw [← Steinberg.rootCharStabilizerSubgroup_eq_kernelReflectionGroup_F4_three a
    (f4Three_coord_pow_three S hE)]
  refine f4Three_mem_rootCharStabilizer_of_roots fun γ hγ => ?_
  have h3 := rootChar_pow_eq_one_of_mem_E S hE hγ
  rw [mul_smul, f4Neg_smul, show -(w • γ) = (-1 : ℤ) • (w • γ) by rw [neg_one_smul],
    rootChar_zsmul, zpow_neg_one, f4Three_rootChar_smul S hρ hE hγ, pow_eq_pow_mod _ h3, hq]
  calc (rootChar a γ ^ 2)⁻¹ = (rootChar a γ ^ 2)⁻¹ * rootChar a γ ^ 3 := by rw [h3, mul_one]
    _ = rootChar a γ := by group

include hρ hE in
theorem f4Three_twistInner_one (hq : S.D.q % 3 = 1) (i : KernelComponent (rootCharHom a)) :
    twistInner (componentRoots (rootCharHom a) i) ((S.ρ : (Fin Tag.F4.rank → ℤ) → _)^[1]) := by
  obtain ⟨u, huC, hu⟩ :=
    f4Three_exists_restrict i (f4Three_mem_kernelReflectionGroup_one S hρ hE hq)
  refine ⟨u, huC, fun γ hγ => ?_⟩
  rw [Function.iterate_one, hρ γ (isRoot_of_mem_componentRoots hγ), hu γ hγ]

include hρ hE in
theorem f4Three_twist_neg_two (hq : S.D.q % 3 = 2) (i : KernelComponent (rootCharHom a)) :
    ∃ u ∈ Subgroup.closure {s : WeylGroup Tag.F4 | ∃ γ ∈ componentRoots (rootCharHom a) i,
        s = rootReflection γ},
      ∀ γ ∈ componentRoots (rootCharHom a) i, S.ρ γ = -(u • γ) := by
  obtain ⟨u, huC, hu⟩ :=
    f4Three_exists_restrict i (f4Three_mem_kernelReflectionGroup_two S hρ hE hq)
  refine ⟨u, huC, fun γ hγ => ?_⟩
  have h := hu γ hγ
  rw [mul_smul, f4Neg_smul] at h
  rw [hρ γ (isRoot_of_mem_componentRoots hγ), ← h, neg_neg]

end Steinberg

end CFSG.HardMathSupport.Timmesfeld.CrossChar
