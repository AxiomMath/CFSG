module

public import CFSG.LocalAnalysis.GLTheoremA.CatA.T171ShapeExcActOuterCartan
public import CFSG.LocalAnalysis.GLTheoremA.CatA.T171ShapeExcActOuterFix
public import CFSG.LocalAnalysis.GLTheoremA.CatA.T171ShapeExcActTorus
public import CFSG.LocalAnalysis.GLTheoremA.CatA.T171ShapeExcActNorm
public import CFSG.HardMathSupport.Timmesfeld.LangTorus.CentralizerTrivialOuterLang

public section

namespace CFSG.LocalAnalysis.GLTheoremA.T171Sh

open CFSG.Blueprint.Chevalley CFSG.LieType.Chevalley CFSG.LieType.Steinberg.Adjoint
  CFSG.LocalAnalysis.ComponentInitial CFSG.LocalAnalysis.ComponentInitial.FourGroupChevalley
  CFSG.HardMathSupport.Timmesfeld.CrossChar CFSG.HardMathSupport.Timmesfeld.LangTorus
  CFSG.HardMathSupport.Timmesfeld.RootAut CFSG.LieType.AlgebraicGroups
  CFSG.HardMathSupport.Timmesfeld.Proving
  CFSG.ComponentClassification.OuterAutomorphisms
  CFSG.ComponentClassification.PerfectAutomorphisms
  CFSG.ComponentClassification.PerfectCentralQuotient CFSG.GroupActions
open scoped Pointwise commutatorElement

variable {τ : Tag} {L : Type} [Field L] [IsAlgClosed L] [CharP L 2]
  {p : ℕ} (S : LangSetup τ L p) {a : Fin τ.rank → Lˣ}
  (hT : rootDiagUnit τ a ∈ S.D.torus) (i : KernelComponent (rootCharHom a))

theorem map_mem_componentRootSpan_of_pinned
    (F : ModGL τ L →* ModGL τ L)
    (hpin : ∀ γ ∈ componentRoots (rootCharHom a) i, ∀ c : L,
      F (pinnedX τ L γ c) ∈ componentRootSpan L (rootCharHom a) i) :
    ∀ g ∈ componentRootSpan L (rootCharHom a) i,
      F g ∈ componentRootSpan L (rootCharHom a) i := by
  intro g hg
  have hmap : (componentRootSpan L (rootCharHom a) i).map F ≤
      componentRootSpan L (rootCharHom a) i := by
    apply map_rootSpan_le_of_forall
    exact hpin
  exact hmap ⟨g, hg, rfl⟩

theorem le_map_componentRootSpan_of_pinned
    (F : ModGL τ L →* ModGL τ L)
    (hpin : ∀ γ ∈ componentRoots (rootCharHom a) i, ∀ c : L,
      ∃ g ∈ componentRootSpan L (rootCharHom a) i, F g = pinnedX τ L γ c) :
    componentRootSpan L (rootCharHom a) i ≤
      (componentRootSpan L (rootCharHom a) i).map F := by
  rw [componentRootSpan]
  refine iSup₂_le fun γ hγ => ?_
  rw [rootSubgroup]
  refine (Subgroup.closure_le _).2 ?_
  rintro _ ⟨c, rfl⟩
  exact Subgroup.mem_map.2 (hpin γ hγ c)

theorem iterHom_step_fixed_of_center_eq_bot
    (hZ : Subgroup.center (componentRootSpan L (rootCharHom a) i) = ⊥)
    (F : ModGL τ L →* ModGL τ L)
    {y g : ModGL τ L} (hyF : F y = y)
    (hFmem : ∀ x ∈ componentRootSpan L (rootCharHom a) i,
      F x ∈ componentRootSpan L (rootCharHom a) i)
    (hFsurj : ∀ x ∈ componentRootSpan L (rootCharHom a) i,
      ∃ x' ∈ componentRootSpan L (rootCharHom a) i, F x' = x)
    (hg : g ∈ componentRootSpan L (rootCharHom a) i)
    (hconj : ∀ x ∈ componentRootSpan L (rootCharHom a) i, y * x * y⁻¹ = g * x * g⁻¹) :
    F g = g := by
  classical
  have hFg : F g ∈ componentRootSpan L (rootCharHom a) i := hFmem g hg
  set h : ModGL τ L := g⁻¹ * F g with hhdef
  have hhS : h ∈ componentRootSpan L (rootCharHom a) i := mul_mem (inv_mem hg) hFg
  have hcomm : ∀ x ∈ componentRootSpan L (rootCharHom a) i, h * x = x * h := by
    intro x hx
    obtain ⟨x', hx', rfl⟩ := hFsurj x hx
    have hFx' : F x' ∈ componentRootSpan L (rootCharHom a) i := hFmem x' hx'
    have h1 : y * x' * y⁻¹ = g * x' * g⁻¹ := hconj x' hx'
    have h2 : y * F x' * y⁻¹ = g * F x' * g⁻¹ := hconj (F x') hFx'
    have h3 : g * F x' * g⁻¹ = F g * F x' * (F g)⁻¹ := by
      have hmap := congrArg F h1
      simp only [map_mul, map_inv] at hmap
      rw [hyF] at hmap
      exact h2.symm.trans hmap
    have h4 : h * F x' * h⁻¹ = F x' := by
      rw [hhdef]
      rw [show (g⁻¹ * F g) * F x' * (g⁻¹ * F g)⁻¹ =
        g⁻¹ * (F g * F x' * (F g)⁻¹) * g by group]
      rw [← h3]
      group
    calc h * F x' = (h * F x' * h⁻¹) * h := by group
      _ = F x' * h := by rw [h4]
  have hhZ : (⟨h, hhS⟩ : ↥(componentRootSpan L (rootCharHom a) i)) ∈
      Subgroup.center (componentRootSpan L (rootCharHom a) i) := by
    rw [Subgroup.mem_center_iff]
    intro x
    exact Subtype.ext (hcomm x x.2).symm
  rw [hZ] at hhZ
  rw [Subgroup.mem_bot] at hhZ
  have h1 : h = 1 := congrArg Subtype.val hhZ
  exact (inv_mul_eq_one.mp h1).symm

theorem center_eq_bot_of_twistKind_twoD
    {p : ℕ} (S : LangSetup τ L p) {a : Fin τ.rank → Lˣ}
    (hT : rootDiagUnit τ a ∈ S.D.torus) (i : KernelComponent (rootCharHom a))
    (hkind : twistKind S.ρ (rootCharHom a) i = .twoD) :
    Subgroup.center (componentRootSpan L (rootCharHom a) i) = ⊥ := by
  obtain ⟨-, hs, -⟩ := outer_componentOrbitLength_spec S hT i
  obtain ⟨h4, hcard⟩ := shape_of_twistKind_twoD hkind
  refine center_eq_bot_of_cartan_det_eq_four i ?_
  exact det_cartan_eq_four_of_nonInner (isRootComponent_componentRoots i)
    _ (outer_isIsometry_rho S hs).bijOn (outer_isIsometry_rho S hs).iform_eq
    (outer_isIsometry_rho S hs).neg
    (not_twistInner_of_twistKind_twoD_exc (Or.inl hkind)) h4 hcard

theorem centerQuotientHom_mem_innAutDerived_twoDExcRankFour
    (hT : rootDiagUnit τ a ∈ S.D.torus)
    (hkind : TwoDOrExcRankFour S a i)
    {s : ℕ} [NeZero s]
    (hs : (S.ρ : (Fin τ.rank → ℤ) → _)^[s] '' componentRoots (rootCharHom a) i =
      componentRoots (rootCharHom a) i)
    (hmin : ∀ k, 0 < k → k < s →
      (S.ρ : (Fin τ.rank → ℤ) → _)^[k] '' componentRoots (rootCharHom a) i ≠
        componentRoots (rootCharHom a) i)
    (hperf : TwoDExcFixedPointsPerfect S a i s)
    {y : ModGL τ L}
    (hyZ : y ∈ torusGroup τ L ⊔ rootSpan τ L (kernelRoots (rootCharHom a)))
    (hyF : S.D.step y = y)
    (hyStab : MulAut.conj y ∈ subgroupStabAut
      (rationalComponent S.ρ S.Γ (rootCharHom a) i)) :
    centerQuotientHom ↥(rationalComponent S.ρ S.Γ (rootCharHom a) i)
        (subgroupStabRestrict (rationalComponent S.ρ S.Γ (rootCharHom a) i)
          ⟨MulAut.conj y, hyStab⟩) ∈
      innAutDerived (↥(rationalComponent S.ρ S.Γ (rootCharHom a) i) ⧸
        Subgroup.center ↥(rationalComponent S.ρ S.Γ (rootCharHom a) i)) := by
  classical
  obtain hD : TwoDExcFixedData S a i s := twoDExcFixedData_of_perfect hperf
  have hsOrbit : s = componentOrbitLength S.ρ (componentRoots (rootCharHom a) i) := by
    have hspec := outer_componentOrbitLength_spec S hT i
    have hpos : 0 < s := Nat.pos_of_ne_zero (NeZero.ne s)
    refine le_antisymm ?_ (Nat.sInf_le ⟨hpos, hs⟩)
    by_contra hlt
    push Not at hlt
    exact hmin (componentOrbitLength S.ρ (componentRoots (rootCharHom a) i)) hspec.1 hlt
      hspec.2.1
  have hdet : (Matrix.of fun β γ : simpleRoots (componentRoots (rootCharHom a) i) =>
      corootPair (β : Fin τ.rank → ℤ) γ).det = 4 := by
    rw [TwoDOrExcRankFour] at hkind
    rcases hkind with hk | ⟨hk, hr⟩
    · obtain ⟨h4, hcard⟩ := shape_of_twistKind_twoD hk
      refine det_cartan_eq_four_of_nonInner (isRootComponent_componentRoots i)
        _ (outer_isIsometry_rho S hs).bijOn (outer_isIsometry_rho S hs).iform_eq
        (outer_isIsometry_rho S hs).neg
        (by rw [hsOrbit]; exact not_twistInner_of_twistKind_twoD_exc (Or.inl hk)) h4 ?_
      exact hcard
    · have hcard : (componentRoots (rootCharHom a) i).ncard = 24 :=
        ncard_of_twistKind_exc_rank_four hk hr
      refine det_cartan_eq_four_of_nonInner (isRootComponent_componentRoots i)
        _ (outer_isIsometry_rho S hs).bijOn (outer_isIsometry_rho S hs).iform_eq
        (outer_isIsometry_rho S hs).neg
        (by rw [hsOrbit]; exact not_twistInner_of_twistKind_twoD_exc (Or.inr ⟨hk, hr⟩))
        (by omega) ?_
      simpa [hr] using hcard
  have hZ : Subgroup.center (componentRootSpan L (rootCharHom a) i) = ⊥ :=
    center_eq_bot_of_cartan_det_eq_four i hdet
  have hZ' : Subgroup.center (rootSpan τ L (componentRoots (rootCharHom a) i)) = ⊥ := by
    change Subgroup.center (componentRootSpan L (rootCharHom a) i) = ⊥
    exact hZ
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
        rw [show (outerOrbitFamily S hT i hs hmin).S 0 =
          rootSpan τ L (componentRoots (rootCharHom a) i) from hP0]
        exact hx))
  obtain ⟨g, hgU, hgconj⟩ := exists_mem_rootSpan_conj_eq_of_mem_Z (a := a) i hyZ
  have hgS : g ∈ componentRootSpan L (rootCharHom a) i := by
    have h := hgU
    change g ∈ rootSpan τ L (unionRoots (rootCharHom a)
      ({i} : Set (KernelComponent (rootCharHom a)))) at h
    rw [unionRoots_singleton] at h
    exact h
  let F : ModGL τ L →* ModGL τ L := iterHom S.D.step s
  have hpin_mem : ∀ γ ∈ componentRoots (rootCharHom a) i, ∀ c : L,
      F (pinnedX τ L γ c) ∈ componentRootSpan L (rootCharHom a) i := by
    intro γ hγ c
    obtain ⟨μ, -, hμ⟩ := iter_step_pinnedX S s (isRoot_of_mem_componentRoots hγ)
    rw [show F (pinnedX τ L γ c) = (S.D.step)^[s] (pinnedX τ L γ c) by
      rw [iterHom_eq_iterate]]
    rw [hμ]
    exact pinnedX_mem_rootSpan (by
      have hmem : (S.ρ : (Fin τ.rank → ℤ) → _)^[s] γ ∈
          (S.ρ : (Fin τ.rank → ℤ) → _)^[s] '' componentRoots (rootCharHom a) i :=
        Set.mem_image_of_mem _ hγ
      rwa [hs] at hmem) _
  have hFmem : ∀ x ∈ componentRootSpan L (rootCharHom a) i,
      F x ∈ componentRootSpan L (rootCharHom a) i :=
    map_mem_componentRootSpan_of_pinned i F hpin_mem
  have hFmem' : ∀ x ∈ rootSpan τ L (componentRoots (rootCharHom a) i),
      F x ∈ rootSpan τ L (componentRoots (rootCharHom a) i) := by
    change ∀ x ∈ componentRootSpan L (rootCharHom a) i,
      F x ∈ componentRootSpan L (rootCharHom a) i
    exact hFmem
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
  have hFsurj : ∀ x ∈ componentRootSpan L (rootCharHom a) i,
      ∃ x' ∈ componentRootSpan L (rootCharHom a) i, F x' = x := by
    intro x hx
    have hle := le_map_componentRootSpan_of_pinned i F hpin_surj
    exact hle hx
  have hFg : F g = g :=
    iterHom_step_fixed_of_center_eq_bot i hZ F
      (iterHom_eq_self_of_fixed hyF s) hFmem hFsurj hgS hgconj
  have hgC : g ∈ hD.C := hD.full g hgS (by simpa [F] using hFg)
  have hθS : ∀ c : ↥hD.C, (c : ModGL τ L) ∈ componentRootSpan L (rootCharHom a) i :=
    fun c => hD.le c.2
  have hθfix : ∀ c : ↥hD.C, iterHom S.D.step s (c : ModGL τ L) = c :=
    fun c => hD.fix c c.2
  have hθZ : ∀ c : ↥hD.C, (c : ModGL τ L) ∈
      (outerOrbitFamily S hT i hs hmin).Z → c ∈ Subgroup.center ↥hD.C := by
    intro c hc
    rw [Subgroup.mem_center_iff]
    intro c'
    apply Subtype.ext
    have h := (outerOrbitFamily S hT i hs hmin).mem_Z.1 hc (c' : ModGL τ L)
      ((outerOrbitFamily S hT i hs hmin).S_le_A 0 (by rw [hP0]; exact hD.le c'.2))
    exact h
  let α : MulAut ↥hD.C := MulAut.conj (⟨g, hgC⟩ : ↥hD.C)
  have hα : α ∈ innAutDerived ↥hD.C :=
    inner_le_innAutDerived ↥hD.C ⟨⟨g, hgC⟩, rfl⟩
  have hθα : ∀ c : ↥hD.C, (α c : ModGL τ L) = y * (c : ModGL τ L) * y⁻¹ := by
    intro c
    exact (hgconj c.val (hD.le c.2)).symm
  exact centerQuotientHom_subgroupStabRestrict_mem_innAutDerived_of_norm S hT i hs hmin
    hD.C.subtype hθS hθfix
    (fun g₁ g₁' h1 h2 h3 h4 => by
      have hmem := commutator_mem_of_twist_mem_centralizer
        (τ := τ) (L := L) (χ := rootCharHom a) (i := i)
        (F := iterHom S.D.step s) (Z := (outerOrbitFamily S hT i hs hmin).Z)
        hZ' (by simpa [F] using hFmem') hZA hD.full h1 h2 h3 h4
      simpa [Subgroup.range_subtype] using hmem)
    hθZ hD.perf hyZ hyF hyStab α hα hθα

end CFSG.LocalAnalysis.GLTheoremA.T171Sh

end
