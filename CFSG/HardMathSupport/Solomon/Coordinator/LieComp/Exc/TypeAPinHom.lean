module

public import CFSG.HardMathSupport.Solomon.Coordinator.ChevQ.E6ThreeTwNotAll24CentreHom

public section

namespace CFSG.HardMathSupport.Solomon.Coordinator.LieComp

open CFSG.Open CFSG.Blueprint.Chevalley CFSG.LieType.Chevalley CFSG.LieType.Steinberg.Adjoint
  CFSG.LocalAnalysis.ComponentInitial CFSG.LocalAnalysis.ComponentInitial.FourGroupChevalley
  CFSG.LieType.AlgebraicGroups CFSG.HardMathSupport.Timmesfeld.LangTorus
  CFSG.HardMathSupport.Timmesfeld.CrossChar
  CFSG.HardMathSupport.Solomon.Coordinator.ChevQ.E6Three
open Matrix CFSG.RankThree.Classical CFSG.RankThree.Classical2 CFSG.SectionRank.OddCover
  CFSG.Assembly.LowTwoRank CFSG.LocalAnalysis.GLTheoremB
open scoped commutatorElement MatrixGroups

theorem pinned_commutator_mem {G V U : Type*} [Group G] [Group V] [Group U] (Fs : G →* G)
    (Z : Subgroup G) (ψ : V →* G) (z : G) (T : V →* V) (ι : U →* V)
    (hconj : ∀ X, Fs (z * ψ X * z⁻¹) = z * ψ (T X) * z⁻¹)
    (hcent : ∀ X, z * ψ X * z⁻¹ ∈ Z → X ∈ Subgroup.center V)
    (hrange : ∀ Y, T Y = Y → ∃ u, ι u = Y) {X X' : V}
    (hgZ : Fs (z * ψ X * z⁻¹) * (z * ψ X * z⁻¹)⁻¹ ∈ Z)
    (hg'Z : Fs (z * ψ X' * z⁻¹) * (z * ψ X' * z⁻¹)⁻¹ ∈ Z) :
    ⁅z * ψ X * z⁻¹, z * ψ X' * z⁻¹⁆ ∈ ((MulAut.conj z).toMonoidHom.comp (ψ.comp ι)).range := by
  have hfixmod : ∀ Y : V, Fs (z * ψ Y * z⁻¹) * (z * ψ Y * z⁻¹)⁻¹ ∈ Z →
      T Y * Y⁻¹ ∈ Subgroup.center V := by
    intro Y hY
    have e : Fs (z * ψ Y * z⁻¹) * (z * ψ Y * z⁻¹)⁻¹ = z * ψ (T Y * Y⁻¹) * z⁻¹ := by
      rw [hconj, map_mul, map_inv]
      group
    rw [e] at hY
    exact hcent _ hY
  have hc := hfixmod X hgZ
  have hc' := hfixmod X' hg'Z
  set c := T X * X⁻¹ with hcdef
  set c' := T X' * X'⁻¹ with hc'def
  have hX : T X = c * X := by rw [hcdef, inv_mul_cancel_right]
  have hX' : T X' = c' * X' := by rw [hc'def, inv_mul_cancel_right]
  have hcomm : ∀ w ∈ Subgroup.center V, ∀ y : V, Commute w y := fun w hw y =>
    (Subgroup.mem_center_iff.1 hw y).symm
  have hfixc : T ⁅X, X'⁆ = ⁅X, X'⁆ := by
    rw [map_commutatorElement, hX, hX']
    exact CycFamily.commutatorElement_central_mul (hcomm c hc X) (hcomm c hc X')
      (hcomm c hc c') (hcomm c' hc' X) (hcomm c' hc' X')
  obtain ⟨u₀, hu₀⟩ := hrange _ hfixc
  refine ⟨u₀, ?_⟩
  simp only [MonoidHom.comp_apply, MulEquiv.coe_toMonoidHom, MulAut.conj_apply, hu₀]
  simp only [commutatorElement_def, map_mul, map_inv]
  group


theorem pinned_center_of_inj {U V : Type*} [Group U] [Group V] (ι : U →* V)
    (hinj : Function.Injective ι) {u : U} (h : ι u ∈ Subgroup.center V) :
    u ∈ Subgroup.center U := by
  rw [Subgroup.mem_center_iff]
  intro u'
  apply hinj
  rw [map_mul, map_mul]
  exact Subgroup.mem_center_iff.1 h (ι u')

section Frame

variable {τ : Tag} {L : Type}
  [Field L] {ta : Fin τ.rank → Lˣ}

theorem pinned_mem_rootSpan {i : KernelComponent (rootCharHom ta)} {ν : ℕ}
    {ψ : SL(ν, L) →* ModGL τ L} {σ : Fin ν → Fin ν → Fin τ.rank → ℤ} (hψ : IsSLFrame ψ σ)
    (hΨ : componentRoots (rootCharHom ta) i = frameRoots σ) (X : SL(ν, L)) :
    ψ X ∈ rootSpan τ L (componentRoots (rootCharHom ta) i) := by
  rw [hΨ, ← hψ.range]
  exact ⟨X, rfl⟩

theorem pinned_pre {i : KernelComponent (rootCharHom ta)} {ν : ℕ} {ψ : SL(ν, L) →* ModGL τ L}
    {σ : Fin ν → Fin ν → Fin τ.rank → ℤ} (hψ : IsSLFrame ψ σ)
    (hΨ : componentRoots (rootCharHom ta) i = frameRoots σ) {z : ModGL τ L}
    (hnorm : ∀ j : KernelComponent (rootCharHom ta), ∀ g : ModGL τ L,
      g ∈ rootSpan τ L (componentRoots (rootCharHom ta) j) ↔
        z * g * z⁻¹ ∈ rootSpan τ L (componentRoots (rootCharHom ta) j))
    {g : ModGL τ L} (hg : g ∈ rootSpan τ L (componentRoots (rootCharHom ta) i)) :
    ∃ X : SL(ν, L), g = z * ψ X * z⁻¹ := by
  have h1 : z⁻¹ * g * z ∈ rootSpan τ L (componentRoots (rootCharHom ta) i) := (hnorm i _).2 (by
    have e : z * (z⁻¹ * g * z) * z⁻¹ = g := by group
    rw [e]
    exact hg)
  rw [hΨ, ← hψ.range] at h1
  obtain ⟨X, hX⟩ := h1
  exact ⟨X, by rw [hX]; group⟩

end Frame

section Pinned


variable {τ : Tag} {L : Type} [Field L] [IsAlgClosed L] {p : ℕ} (S : LangSetup τ L p)
  {ta : Fin τ.rank → Lˣ}

theorem pinned_exists_lang (hT : rootDiagUnit τ ta ∈ S.D.torus)
    (i : KernelComponent (rootCharHom ta)) {s : ℕ} (hs0 : 0 < s) {ν : ℕ}
    {ψ : SL(ν, L) →* ModGL τ L} {σ : Fin ν → Fin ν → Fin τ.rank → ℤ} (hψ : IsSLFrame ψ σ)
    (hΨ : componentRoots (rootCharHom ta) i = frameRoots σ) {T : SL(ν, L) →* SL(ν, L)}
    {B : SL(ν, L)}
    (hstd : ∀ X : SL(ν, L), ψ B * iterHom S.D.step s (ψ X) * (ψ B)⁻¹ = ψ (T X)) :
    ∃ z : ModGL τ L, (∀ X : SL(ν, L),
        iterHom S.D.step s (z * ψ X * z⁻¹) = z * ψ (T X) * z⁻¹) ∧
      ∀ j : KernelComponent (rootCharHom ta), ∀ g : ModGL τ L,
        g ∈ rootSpan τ L (componentRoots (rootCharHom ta) j) ↔
          z * g * z⁻¹ ∈ rootSpan τ L (componentRoots (rootCharHom ta) j) := by
  have hy₁ : ψ B ∈ rootSpan τ L (kernelRoots (rootCharHom ta)) :=
    rootSpan_mono (fun γ hγ => hγ.1) (pinned_mem_rootSpan hψ hΨ B)
  obtain ⟨z, hz, hnorm⟩ := exists_lang_mul_T S hT hs0 hy₁
  refine ⟨z, fun X => ?_, hnorm⟩
  rw [← hstd X, map_mul, map_mul, map_inv, hz]
  group

theorem pinned_central (hT : rootDiagUnit τ ta ∈ S.D.torus)
    (i : KernelComponent (rootCharHom ta)) {s : ℕ} [NeZero s]
    (hs : (S.ρ : (Fin τ.rank → ℤ) → _)^[s] '' componentRoots (rootCharHom ta) i =
      componentRoots (rootCharHom ta) i)
    (hmin : ∀ k, 0 < k → k < s →
      (S.ρ : (Fin τ.rank → ℤ) → _)^[k] '' componentRoots (rootCharHom ta) i ≠
        componentRoots (rootCharHom ta) i)
    {ν : ℕ} (hν : 3 ≤ ν) {ψ : SL(ν, L) →* ModGL τ L} {σ : Fin ν → Fin ν → Fin τ.rank → ℤ}
    (hψ : IsSLFrame ψ σ) (hΨ : componentRoots (rootCharHom ta) i = frameRoots σ)
    {z : ModGL τ L}
    (hnorm : ∀ j : KernelComponent (rootCharHom ta), ∀ g : ModGL τ L,
      g ∈ rootSpan τ L (componentRoots (rootCharHom ta) j) ↔
        z * g * z⁻¹ ∈ rootSpan τ L (componentRoots (rootCharHom ta) j)) (X : SL(ν, L))
    (hX : z * ψ X * z⁻¹ ∈ (outerOrbitFamily S hT i hs hmin).Z) :
    X ∈ Subgroup.center SL(ν, L) := by
  classical
  set P := outerOrbitFamily S hT i hs hmin with hP
  have hP0 : P.S 0 = rootSpan τ L (componentRoots (rootCharHom ta) i) := by
    rw [hP, outerOrbitFamily_S, ZMod.val_zero]
    simp only [Function.iterate_zero, id_eq, Set.image_id']
  have hzA : ∀ y ∈ P.A, z * y * z⁻¹ ∈ P.A := by
    have h : P.A ≤ P.A.comap (MulAut.conj z).toMonoidHom := by
      refine iSup_le fun k => ?_
      obtain ⟨j, hj⟩ := outer_iterate_image_component S hT i k.val
      intro g hg
      have hg' : g ∈ rootSpan τ L (componentRoots (rootCharHom ta) j) := by rw [hj]; exact hg
      have h2 := (hnorm j g).1 hg'
      rw [hj] at h2
      exact P.S_le_A k h2
    exact fun y hy => h hy
  have hZconj : ∀ x : ModGL τ L, z * x * z⁻¹ ∈ P.Z → x ∈ P.Z := by
    intro x hx
    rw [CycFamily.mem_Z] at hx ⊢
    intro y hy
    have := hx _ (hzA y hy)
    have e1 : z * y * z⁻¹ * (z * x * z⁻¹) = z * (y * x) * z⁻¹ := by group
    have e2 : z * x * z⁻¹ * (z * y * z⁻¹) = z * (x * y) * z⁻¹ := by group
    rw [e1, e2] at this
    simpa using this
  have hker : ψ.ker ≠ ⊤ := by
    intro h
    have h01 : (⟨0, by omega⟩ : Fin ν) ≠ ⟨1, by omega⟩ := by simp
    obtain ⟨ε, hε⟩ := hψ.transv _ _ h01
    have h1 : Matrix.SpecialLinearGroup.transvection h01 (1 : L) ∈ ψ.ker := by
      rw [h]
      exact Subgroup.mem_top _
    rw [MonoidHom.mem_ker, hε, mul_one, ← pinnedX_zero τ L (σ _ _)] at h1
    exact Units.ne_zero _ (pinnedX_injective τ L _ h1)
  refine mem_center_SL_of_commute hν ψ hker fun Y => ?_
  have hYA : ψ Y ∈ P.A := P.S_le_A 0 (by rw [hP0]; exact pinned_mem_rootSpan hψ hΨ Y)
  exact ((CycFamily.mem_Z P).1 (hZconj _ hX) (ψ Y) hYA).symm

theorem exists_pinned_hom (hT : rootDiagUnit τ ta ∈ S.D.torus)
    (i : KernelComponent (rootCharHom ta)) {ν : ℕ} (hν : 3 ≤ ν) {ψ : SL(ν, L) →* ModGL τ L}
    {σ : Fin ν → Fin ν → Fin τ.rank → ℤ} (hψ : IsSLFrame ψ σ)
    (hΨ : componentRoots (rootCharHom ta) i = frameRoots σ) {T : SL(ν, L) →* SL(ν, L)}
    {B : SL(ν, L)}
    (hstd : ∀ X : SL(ν, L), ψ B * iterHom S.D.step
      (componentOrbitLength S.ρ (componentRoots (rootCharHom ta) i)) (ψ X) * (ψ B)⁻¹ = ψ (T X))
    {U : Type*} [Group U] (ι : U →* SL(ν, L)) (hinj : Function.Injective ι)
    (hfix : ∀ u, T (ι u) = ι u) (hrange : ∀ Y, T Y = Y → ∃ u, ι u = Y) :
    ∃ W : SL(ν, L) →* ModGL τ L,
      rationalComponent S.ρ S.Γ (rootCharHom ta) i ≤ (W.comp ι).range ∧
        (W.comp ι).ker ≤ Subgroup.center U ∧
        (Group.IsPerfect U →
          (W.comp ι).range ≤ rationalComponent S.ρ S.Γ (rootCharHom ta) i) := by
  classical
  obtain ⟨hs0, hs, hmin⟩ := outer_componentOrbitLength_spec S hT i
  set s := componentOrbitLength S.ρ (componentRoots (rootCharHom ta) i) with hsdef
  haveI : NeZero s := ⟨hs0.ne'⟩
  obtain ⟨z, hconj, hnorm⟩ := pinned_exists_lang S hT i hs0 hψ hΨ hstd
  have hcent := pinned_central S hT i hs hmin hν hψ hΨ hnorm
  set P := outerOrbitFamily S hT i hs hmin with hP
  have hP0 : P.S 0 = rootSpan τ L (componentRoots (rootCharHom ta) i) := by
    rw [hP, outerOrbitFamily_S, ZMod.val_zero]
    simp only [Function.iterate_zero, id_eq, Set.image_id']
  set θL : SL(ν, L) →* ModGL τ L := (MulAut.conj z).toMonoidHom.comp ψ with hθLdef
  have hθL : ∀ X, θL X = z * ψ X * z⁻¹ := fun X => rfl
  have hθLS : ∀ X, θL X ∈ rootSpan τ L (componentRoots (rootCharHom ta) i) := fun X => by
    rw [hθL]
    exact (hnorm i _).1 (pinned_mem_rootSpan hψ hΨ X)
  have hθS : ∀ u, (θL.comp ι) u ∈ rootSpan τ L (componentRoots (rootCharHom ta) i) :=
    fun u => hθLS _
  have hθfix : ∀ u, iterHom S.D.step s ((θL.comp ι) u) = (θL.comp ι) u := fun u => by
    simp only [MonoidHom.comp_apply, hθL, hconj, hfix]
  have hθY : ∀ g g' : ModGL τ L, g ∈ rootSpan τ L (componentRoots (rootCharHom ta) i) →
      g' ∈ rootSpan τ L (componentRoots (rootCharHom ta) i) →
      iterHom S.D.step s g * g⁻¹ ∈ P.Z → iterHom S.D.step s g' * g'⁻¹ ∈ P.Z →
        ⁅g, g'⁆ ∈ (θL.comp ι).range := by
    intro g g' hg hg' hgZ hg'Z
    obtain ⟨X, rfl⟩ := pinned_pre hψ hΨ hnorm hg
    obtain ⟨X', rfl⟩ := pinned_pre hψ hΨ hnorm hg'
    exact pinned_commutator_mem (iterHom S.D.step s) P.Z ψ z T ι hconj
      (fun Y hY => hcent Y hY) hrange hgZ hg'Z
  have hθZ : ∀ u, (θL.comp ι) u ∈ P.Z → u ∈ Subgroup.center U := fun u hu =>
    pinned_center_of_inj ι hinj (hcent (ι u) hu)
  obtain ⟨f, hf1, hfker, hf2, hfn⟩ := KSConn.rationalComponent_eq_range_of_hom_norm S hT i hs
    hmin (θL.comp ι) hθS hθfix hθY hθZ
  let θL₀ : SL(ν, L) →* P.S 0 := θL.codRestrict (P.S 0) fun X => by
    rw [hP0]
    exact hθLS X
  have hfeq : f = (P.norm.comp θL₀).comp ι :=
    MonoidHom.ext fun u => hfn u ⟨θL (ι u), by rw [hP0]; exact hθLS _⟩ rfl
  exact ⟨P.norm.comp θL₀, hfeq ▸ hf1, hfeq ▸ hfker, hfeq ▸ hf2⟩

end Pinned

end CFSG.HardMathSupport.Solomon.Coordinator.LieComp

end
