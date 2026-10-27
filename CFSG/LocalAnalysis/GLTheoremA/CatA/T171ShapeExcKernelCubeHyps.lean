module

public import CFSG.LocalAnalysis.GLTheoremA.CatA.T171ShapeExcKernelCubeData
public import CFSG.LocalAnalysis.GLTheoremA.CatA.T171ShapeExcKernelHighCube
import CFSG.LocalAnalysis.GLTheoremA.CatA.T171ShapeExcInnerD4TwoD
public import CFSG.LocalAnalysis.GLTheoremA.CatA.T171ShapeExcKernelCubeGeneric

public section

namespace CFSG.LocalAnalysis.GLTheoremA.T171Sh

open CFSG.Blueprint.Chevalley CFSG.LieType.Chevalley CFSG.LieType.Steinberg.Adjoint
  CFSG.LocalAnalysis.ComponentInitial CFSG.LocalAnalysis.ComponentInitial.FourGroupChevalley
  CFSG.HardMathSupport.Timmesfeld.CrossChar CFSG.HardMathSupport.Timmesfeld.LangTorus
  CFSG.HardMathSupport.Timmesfeld.RootAut CFSG.LieType.AlgebraicGroups
  CFSG.ComponentClassification.OuterAutomorphisms CFSG.GroupActions
  CFSG.ComponentClassification.PerfectAutomorphisms
open scoped Pointwise commutatorElement


theorem le_map_componentRootSpan_frobGL {τ : Tag} {L : Type} [Field L] [IsAlgClosed L] [CharP L 2]
    {a : Fin τ.rank → Lˣ} (i : KernelComponent (rootCharHom a)) :
    componentRootSpan L (rootCharHom a) i ≤
      (componentRootSpan L (rootCharHom a) i).map
        (frobGL (τ := τ) (frobeniusEquiv L 2)) := by
  apply le_map_componentRootSpan_of_pinned i
  intro γ hγ c
  refine ⟨pinnedX τ L γ ((frobeniusEquiv L 2).symm c), pinnedX_mem_rootSpan hγ _, ?_⟩
  rw [frobGL_pinnedX, RingEquiv.apply_symm_apply]

theorem iterHom_surj_componentRootSpan {τ : Tag} {L : Type} [Field L] [IsAlgClosed L] [CharP L 2]
    {p : ℕ} (S : LangSetup τ L p) {a : Fin τ.rank → Lˣ}
    (i : KernelComponent (rootCharHom a)) {s : ℕ} [NeZero s]
    (hs : (S.ρ : (Fin τ.rank → ℤ) → _)^[s] '' componentRoots (rootCharHom a) i =
      componentRoots (rootCharHom a) i) :
    ∀ x ∈ rootSpan τ L (componentRoots (rootCharHom a) i),
      ∃ x' ∈ rootSpan τ L (componentRoots (rootCharHom a) i),
        iterHom S.D.step s x' = x := by
  have hpin_surj : ∀ γ ∈ componentRoots (rootCharHom a) i, ∀ c : L,
      ∃ g' ∈ componentRootSpan L (rootCharHom a) i,
        iterHom S.D.step s g' = pinnedX τ L γ c := by
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
    rw [show iterHom S.D.step s (pinnedX τ L δ c') =
      (S.D.step)^[s] (pinnedX τ L δ c') by rw [iterHom_eq_iterate]]
    rw [hμ, hδγ, hc', ← mul_assoc, mul_inv_cancel₀ hμ0, one_mul]
  intro x hx
  have hle := le_map_componentRootSpan_of_pinned i (iterHom S.D.step s) hpin_surj
  exact hle hx

theorem cubeTransferHyps_of {τ : Tag} {L : Type} [Field L] [IsAlgClosed L] [CharP L 2]
    {p : ℕ} (S : LangSetup τ L p) {a : Fin τ.rank → Lˣ}
    (hT : rootDiagUnit τ a ∈ S.D.torus) (i : KernelComponent (rootCharHom a))
    {s : ℕ} [NeZero s]
    (hs : (S.ρ : (Fin τ.rank → ℤ) → _)^[s] '' componentRoots (rootCharHom a) i =
      componentRoots (rootCharHom a) i)
    (hmin : ∀ k, 0 < k → k < s →
      (S.ρ : (Fin τ.rank → ℤ) → _)^[k] '' componentRoots (rootCharHom a) i ≠
        componentRoots (rootCharHom a) i)
    (hD : TwoDExcFixedData S a i s) :
    CubeTransferHyps S hT i hs hmin hD := by
  classical
  have hP0 : (outerOrbitFamily S hT i hs hmin).S 0 =
      rootSpan τ L (componentRoots (rootCharHom a) i) := by
    rw [outerOrbitFamily_S, ZMod.val_zero]
    simp only [Function.iterate_zero, id_eq, Set.image_id']
  have hZA : (outerOrbitFamily S hT i hs hmin).Z ≤
      Subgroup.centralizer
        (rootSpan τ L (componentRoots (rootCharHom a) i) : Set (ModGL τ L)) := by
    intro z hz
    rw [Subgroup.mem_centralizer_iff]
    intro x hx
    exact (outerOrbitFamily S hT i hs hmin).mem_Z.1 hz x
      ((outerOrbitFamily S hT i hs hmin).S_le_A 0 (by rw [hP0]; exact hx))
  have hFmem : ∀ x ∈ rootSpan τ L (componentRoots (rootCharHom a) i),
      iterHom S.D.step s x ∈ rootSpan τ L (componentRoots (rootCharHom a) i) :=
    iterHom_step_s_mem_rootSpan S hT i hs
  refine ⟨fun c => hD.le c.2, fun c => hD.fix c c.2, ?_, ?_⟩
  · intro g₁ g₁' h1 h2 hz1 hz2
    have hmem := commutator_mem_of_twist_mem_centralizer_exp S i
      (F := iterHom S.D.step s) (Z := (outerOrbitFamily S hT i hs hmin).Z)
      hFmem hZA hD.full h1 h2 hz1 hz2
    simpa [Subgroup.range_subtype] using hmem
  · intro c hc
    rw [Subgroup.mem_center_iff]
    intro c'
    apply Subtype.ext
    exact (outerOrbitFamily S hT i hs hmin).mem_Z.1 hc (c' : ModGL τ L)
      ((outerOrbitFamily S hT i hs hmin).S_le_A 0 (by rw [hP0]; exact hD.le c'.2))

theorem exists_cubeConjData {τ : Tag} {L : Type} [Field L] [IsAlgClosed L] [CharP L 2]
    {p : ℕ} (S : LangSetup τ L p) {a : Fin τ.rank → Lˣ}
    (hT : rootDiagUnit τ a ∈ S.D.torus) (i : KernelComponent (rootCharHom a))
    (hExp : ∀ z : ↥(componentRootSpan L (rootCharHom a) i),
      z ∈ Subgroup.center (componentRootSpan L (rootCharHom a) i) →
      ((z : ModGL τ L) ^ 3 = 1))
    {s : ℕ} [NeZero s]
    (hs : (S.ρ : (Fin τ.rank → ℤ) → _)^[s] '' componentRoots (rootCharHom a) i =
      componentRoots (rootCharHom a) i)
    (hmin : ∀ k, 0 < k → k < s →
      (S.ρ : (Fin τ.rank → ℤ) → _)^[k] '' componentRoots (rootCharHom a) i ≠
        componentRoots (rootCharHom a) i)
    (hD : TwoDExcFixedData S a i s)
    {y : ModGL τ L}
    (hyZ : y ∈ torusGroup τ L ⊔ rootSpan τ L (kernelRoots (rootCharHom a)))
    (hyF : S.D.step y = y) :
    Nonempty (CubeConjData S i hD y) := by
  classical
  obtain ⟨g, hgU, hgconj⟩ := exists_mem_rootSpan_conj_eq_of_mem_Z (a := a) i hyZ
  have hgS : g ∈ rootSpan τ L (componentRoots (rootCharHom a) i) := by
    have h := hgU
    change g ∈ rootSpan τ L (unionRoots (rootCharHom a)
      ({i} : Set (KernelComponent (rootCharHom a)))) at h
    rw [unionRoots_singleton] at h
    exact h
  have hFmem : ∀ x ∈ rootSpan τ L (componentRoots (rootCharHom a) i),
      iterHom S.D.step s x ∈ rootSpan τ L (componentRoots (rootCharHom a) i) :=
    iterHom_step_s_mem_rootSpan S hT i hs
  have hFsurj : ∀ x ∈ rootSpan τ L (componentRoots (rootCharHom a) i),
      ∃ x' ∈ rootSpan τ L (componentRoots (rootCharHom a) i), iterHom S.D.step s x' = x :=
    iterHom_surj_componentRootSpan S i hs
  have hz0center : ∀ x ∈ rootSpan τ L (componentRoots (rootCharHom a) i),
      x * (g⁻¹ * iterHom S.D.step s g) = (g⁻¹ * iterHom S.D.step s g) * x :=
    displacement_central_of_conj_eq hgS hFmem hFsurj (iterHom_eq_self_of_fixed hyF s) hgconj
  have hz0S : g⁻¹ * iterHom S.D.step s g ∈
      rootSpan τ L (componentRoots (rootCharHom a) i) :=
    mul_mem (inv_mem hgS) (hFmem g hgS)
  have hz0cube : (g⁻¹ * iterHom S.D.step s g) ^ 3 = 1 :=
    pow_three_displacement_eq_one hExp hz0center hz0S
  have hFg : iterHom S.D.step s g = g * (g⁻¹ * iterHom S.D.step s g) := by group
  have hcomm : Commute g (g⁻¹ * iterHom S.D.step s g) := hz0center g hgS
  have hg3C : g ^ 3 ∈ hD.C := by
    refine hD.full (g ^ 3) (pow_mem hgS 3) ?_
    rw [map_pow, hFg, hcomm.mul_pow, hz0cube, mul_one]
  have hφgS : frobGL (τ := τ) (frobeniusEquiv L 2) g ∈
      rootSpan τ L (componentRoots (rootCharHom a) i) :=
    frobGL_mem_rootSpan (frobeniusEquiv L 2) hgS
  have hφz0 : frobGL (τ := τ) (frobeniusEquiv L 2) (g⁻¹ * iterHom S.D.step s g) =
      (g⁻¹ * iterHom S.D.step s g) ^ 2 :=
    frobGL_center_eq_sq i hz0S hz0center
  have hFh : iterHom S.D.step s (g * frobGL (τ := τ) (frobeniusEquiv L 2) g) =
      g * frobGL (τ := τ) (frobeniusEquiv L 2) g :=
    mul_fixed_of_step_frob hFg hz0cube hφz0
      (hz0center (frobGL (τ := τ) (frobeniusEquiv L 2) g) hφgS).symm
      (iterHom_frobGL_step S s g)
  exact ⟨⟨g, hgS, hgconj, hg3C, hD.full _ (mul_mem hgS hφgS) hFh⟩⟩

end CFSG.LocalAnalysis.GLTheoremA.T171Sh

end
