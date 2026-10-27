module

public import CFSG.LocalAnalysis.GLTheoremA.CatA.T171ShapeExcActOuterMain
import CFSG.LocalAnalysis.GLTheoremA.CatA.T171ShapeExcInnerD4Transport

public section

namespace CFSG.LocalAnalysis.GLTheoremA.T171Sh

open CFSG.Blueprint.Chevalley CFSG.LieType.Chevalley CFSG.LieType.Steinberg.Adjoint
  CFSG.LocalAnalysis.ComponentInitial CFSG.LocalAnalysis.ComponentInitial.FourGroupChevalley
  CFSG.HardMathSupport.Timmesfeld.CrossChar CFSG.HardMathSupport.Timmesfeld.LangTorus
  CFSG.HardMathSupport.Timmesfeld.RootAut CFSG.LieType.AlgebraicGroups
  CFSG.HardMathSupport.Timmesfeld.Proving
  CFSG.ComponentClassification.OuterAutomorphisms
  CFSG.ComponentClassification.PerfectAutomorphisms CFSG.GroupActions
open scoped Pointwise commutatorElement


variable {τ : Tag} {L : Type} [Field L] [IsAlgClosed L] [CharP L 2]
  {p : ℕ} (S : LangSetup τ L p) {a : Fin τ.rank → Lˣ}

theorem iterHom_step_s_mem_rootSpan
    (hT : rootDiagUnit τ a ∈ S.D.torus) (i : KernelComponent (rootCharHom a))
    {s : ℕ} [NeZero s]
    (hs : (S.ρ : (Fin τ.rank → ℤ) → _)^[s] '' componentRoots (rootCharHom a) i =
      componentRoots (rootCharHom a) i) :
    ∀ x ∈ rootSpan τ L (componentRoots (rootCharHom a) i),
      iterHom S.D.step s x ∈ rootSpan τ L (componentRoots (rootCharHom a) i) := by
  intro x hx
  have hpin_mem : ∀ γ ∈ componentRoots (rootCharHom a) i, ∀ c : L,
      iterHom S.D.step s (pinnedX τ L γ c) ∈ componentRootSpan L (rootCharHom a) i := by
    intro γ hγ c
    obtain ⟨μ, -, hμ⟩ := iter_step_pinnedX S s (isRoot_of_mem_componentRoots hγ)
    rw [show iterHom S.D.step s (pinnedX τ L γ c) = (S.D.step)^[s] (pinnedX τ L γ c) by
      rw [iterHom_eq_iterate]]
    rw [hμ]
    exact pinnedX_mem_rootSpan (by
      have hmem : (S.ρ : (Fin τ.rank → ℤ) → _)^[s] γ ∈
          (S.ρ : (Fin τ.rank → ℤ) → _)^[s] '' componentRoots (rootCharHom a) i :=
        Set.mem_image_of_mem _ hγ
      rwa [hs] at hmem) _
  exact map_mem_componentRootSpan_of_pinned i (iterHom S.D.step s) hpin_mem x hx

theorem exists_fixedData_conj_of_period
    (hT : rootDiagUnit τ a ∈ S.D.torus) (i : KernelComponent (rootCharHom a))
    {s : ℕ} [NeZero s]
    (hs : (S.ρ : (Fin τ.rank → ℤ) → _)^[s] '' componentRoots (rootCharHom a) i =
      componentRoots (rootCharHom a) i)
    (hZ : Subgroup.center (rootSpan τ L (componentRoots (rootCharHom a) i)) = ⊥)
    (D : TwoDExcFixedData S a i s)
    {y : ModGL τ L}
    (hyZ : y ∈ torusGroup τ L ⊔ rootSpan τ L (kernelRoots (rootCharHom a)))
    (hyF : S.D.step y = y) :
    ∃ g : ↥D.C, ∀ c : ↥D.C,
      ((MulAut.conj g) c : ModGL τ L) = y * (c : ModGL τ L) * y⁻¹ := by
  classical
  have hZ' : Subgroup.center (componentRootSpan L (rootCharHom a) i) = ⊥ := by
    change Subgroup.center (rootSpan τ L (componentRoots (rootCharHom a) i)) = ⊥
    exact hZ
  obtain ⟨g, hgU, hgconj⟩ := exists_mem_rootSpan_conj_eq_of_mem_Z (a := a) i hyZ
  have hgS : g ∈ rootSpan τ L (componentRoots (rootCharHom a) i) := by
    have h := hgU
    change g ∈ rootSpan τ L (unionRoots (rootCharHom a)
      ({i} : Set (KernelComponent (rootCharHom a)))) at h
    rw [unionRoots_singleton] at h
    exact h
  let F : ModGL τ L →* ModGL τ L := iterHom S.D.step s
  have hFmem : ∀ x ∈ rootSpan τ L (componentRoots (rootCharHom a) i),
      F x ∈ rootSpan τ L (componentRoots (rootCharHom a) i) :=
    iterHom_step_s_mem_rootSpan S hT i hs
  have hpin_surj : ∀ γ ∈ componentRoots (rootCharHom a) i, ∀ c : L,
      ∃ g' ∈ componentRootSpan L (rootCharHom a) i, F g' = pinnedX τ L γ c := by
    intro γ hγ c
    obtain ⟨δ, hδ, hδγ⟩ : ∃ δ ∈ componentRoots (rootCharHom a) i,
        (S.ρ : (Fin τ.rank → ℤ) → _)^[s] δ = γ := by
      have hmem : γ ∈ (S.ρ : (Fin τ.rank → ℤ) → _)^[s] '' componentRoots (rootCharHom a) i := by
        rw [hs]
        exact hγ
      obtain ⟨δ, hδ, rfl⟩ := hmem
      exact ⟨δ, hδ, rfl⟩
    obtain ⟨μ, hμ0, hμ⟩ := iter_step_pinnedX S s (isRoot_of_mem_componentRoots hδ)
    obtain ⟨c', hc'⟩ := IsAlgClosed.exists_pow_nat_eq (μ⁻¹ * c) (pow_pos S.q_pos s)
    refine ⟨pinnedX τ L δ c', pinnedX_mem_rootSpan hδ c', ?_⟩
    rw [show F (pinnedX τ L δ c') = (S.D.step)^[s] (pinnedX τ L δ c') by
      rw [iterHom_eq_iterate]]
    rw [hμ, hδγ, hc', ← mul_assoc, mul_inv_cancel₀ hμ0, one_mul]
  have hFsurj : ∀ x ∈ rootSpan τ L (componentRoots (rootCharHom a) i),
      ∃ x' ∈ rootSpan τ L (componentRoots (rootCharHom a) i), F x' = x := by
    intro x hx
    have hle := le_map_componentRootSpan_of_pinned i F hpin_surj
    exact hle hx
  have hFg : F g = g :=
    iterHom_step_fixed_of_center_eq_bot i hZ' F
      (iterHom_eq_self_of_fixed hyF s) hFmem hFsurj hgS hgconj
  have hgC : g ∈ D.C := D.full g hgS (by simpa [F] using hFg)
  refine ⟨⟨g, hgC⟩, fun c => ?_⟩
  exact (hgconj c.val (D.le c.2)).symm

theorem centerQuotientHom_mem_inner_twoDExcRankFour
    (hT : rootDiagUnit τ a ∈ S.D.torus) (i : KernelComponent (rootCharHom a))
    {s : ℕ} [NeZero s]
    (hs : (S.ρ : (Fin τ.rank → ℤ) → _)^[s] '' componentRoots (rootCharHom a) i =
      componentRoots (rootCharHom a) i)
    (hmin : ∀ k, 0 < k → k < s →
      (S.ρ : (Fin τ.rank → ℤ) → _)^[k] '' componentRoots (rootCharHom a) i ≠
        componentRoots (rootCharHom a) i)
    (hZ : Subgroup.center (rootSpan τ L (componentRoots (rootCharHom a) i)) = ⊥)
    (hperf : TwoDExcFixedPointsPerfect S a i s)
    {y : ModGL τ L}
    (hyZ : y ∈ torusGroup τ L ⊔ rootSpan τ L (kernelRoots (rootCharHom a)))
    (hyF : S.D.step y = y)
    (hyStab : MulAut.conj y ∈ CFSG.GroupActions.subgroupStabAut
      (rationalComponent S.ρ S.Γ (rootCharHom a) i)) :
    centerQuotientHom ↥(rationalComponent S.ρ S.Γ (rootCharHom a) i)
        (CFSG.GroupActions.subgroupStabRestrict
          (rationalComponent S.ρ S.Γ (rootCharHom a) i)
          ⟨MulAut.conj y, hyStab⟩) ∈
      inner (↥(rationalComponent S.ρ S.Γ (rootCharHom a) i) ⧸
        Subgroup.center ↥(rationalComponent S.ρ S.Γ (rootCharHom a) i)) := by
  classical
  let D : TwoDExcFixedData S a i s := twoDExcFixedData_of_perfect hperf
  obtain ⟨g, hgconj⟩ := exists_fixedData_conj_of_period S hT i hs hZ D hyZ hyF
  have hZ' : Subgroup.center (componentRootSpan L (rootCharHom a) i) = ⊥ := by
    change Subgroup.center (rootSpan τ L (componentRoots (rootCharHom a) i)) = ⊥
    exact hZ
  have hFmem : ∀ x ∈ rootSpan τ L (componentRoots (rootCharHom a) i),
      iterHom S.D.step s x ∈ rootSpan τ L (componentRoots (rootCharHom a) i) :=
    iterHom_step_s_mem_rootSpan S hT i hs
  have hP0 : (outerOrbitFamily S hT i hs hmin).S 0 =
      rootSpan τ L (componentRoots (rootCharHom a) i) := by
    rw [outerOrbitFamily_S, ZMod.val_zero]
    simp only [Function.iterate_zero, id_eq, Set.image_id']
  have hZA : (outerOrbitFamily S hT i hs hmin).Z ≤
      Subgroup.centralizer (rootSpan τ L (componentRoots (rootCharHom a) i) :
        Set (ModGL τ L)) := by
    intro z hz
    rw [Subgroup.mem_centralizer_iff]
    intro x hx
    exact (outerOrbitFamily S hT i hs hmin).mem_Z.1 hz x
      ((outerOrbitFamily S hT i hs hmin).S_le_A 0 (by
        rw [hP0]
        exact hx))
  have hθY : ∀ g₁ g₁' : ModGL τ L,
      g₁ ∈ rootSpan τ L (componentRoots (rootCharHom a) i) →
      g₁' ∈ rootSpan τ L (componentRoots (rootCharHom a) i) →
      iterHom S.D.step s g₁ * g₁⁻¹ ∈ (outerOrbitFamily S hT i hs hmin).Z →
      iterHom S.D.step s g₁' * g₁'⁻¹ ∈ (outerOrbitFamily S hT i hs hmin).Z →
      ⁅g₁, g₁'⁆ ∈ D.C := by
    intro g₁ g₁' h1 h2 hz1 hz2
    exact commutator_mem_of_twist_mem_centralizer
      (F := iterHom S.D.step s) (Z := (outerOrbitFamily S hT i hs hmin).Z)
      hZ' hFmem hZA D.full h1 h2 hz1 hz2
  have hθZ : ∀ c : ↥D.C, (c : ModGL τ L) ∈ (outerOrbitFamily S hT i hs hmin).Z →
      c ∈ Subgroup.center ↥D.C := by
    intro c hc
    rw [Subgroup.mem_center_iff]
    intro c'
    apply Subtype.ext
    have h := (outerOrbitFamily S hT i hs hmin).mem_Z.1 hc (c' : ModGL τ L)
      ((outerOrbitFamily S hT i hs hmin).S_le_A 0 (by rw [hP0]; exact D.le c'.2))
    exact h
  exact centerQuotientHom_subgroupStabRestrict_mem_inner_of_norm S hT i hs hmin
    D.C.subtype (fun c => D.le c.2) (fun c => D.fix c c.2)
    (fun g₁ g₁' h1 h2 hz1 hz2 => by
      have hmem := hθY g₁ g₁' h1 h2 hz1 hz2
      simpa [Subgroup.range_subtype] using hmem)
    hθZ D.perf hyZ hyF hyStab (MulAut.conj g) ⟨g, rfl⟩ hgconj

end CFSG.LocalAnalysis.GLTheoremA.T171Sh

end
