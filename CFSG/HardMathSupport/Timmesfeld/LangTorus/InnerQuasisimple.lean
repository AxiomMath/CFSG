module

public import CFSG.HardMathSupport.Timmesfeld.LangTorus.InnerQuasisimpleOrbit
public import CFSG.HardMathSupport.Timmesfeld.LangTorus.InnerQuasisimpleField

public section

namespace CFSG.HardMathSupport.Timmesfeld.LangTorus

open CFSG.Open CFSG.Blueprint.Chevalley CFSG.LieType.Chevalley CFSG.LieType.Steinberg.Adjoint
  CFSG.LocalAnalysis.ComponentInitial
  CFSG.LocalAnalysis.ComponentInitial.FourGroupChevalley CFSG.LieType.AlgebraicGroups
  CFSG.HardMathSupport.Timmesfeld.CrossChar
open scoped commutatorElement

set_option linter.unusedSectionVars false

section Reduction

variable {τ : Tag} {L : Type} [Field L] [IsAlgClosed L] {p : ℕ} (S : LangSetup τ L p)
  {a : Fin τ.rank → Lˣ}

theorem CQ_le_rootSpan (σ : L ≃+* L) (i : KernelComponent (rootCharHom a)) :
    CQ σ i ≤ rootSpan τ L (componentRoots (rootCharHom a) i) := by
  unfold CQ
  refine (Subgroup.closure_le _).2 ?_
  rintro _ ⟨γ, hγ, c, hc, rfl⟩
  rw [unionRoots_singleton] at hγ
  exact pinnedX_mem_rootSpan hγ c

theorem frobGL_eq_self_of_mem_CQ (σ : L ≃+* L) (i : KernelComponent (rootCharHom a)) {x : ModGL τ L}
    (hx : x ∈ CQ σ i) : frobGL σ x = x := by
  have : CQ σ i ≤ (frobGL σ).eqLocus (MonoidHom.id _) := by
    unfold CQ
    refine (Subgroup.closure_le _).2 ?_
    rintro _ ⟨γ, hγ, c, hc, rfl⟩
    show frobGL σ (pinnedX τ L γ c) = pinnedX τ L γ c
    rw [frobGL_pinnedX, hc]
  exact this hx

theorem commutator_le_self' {G : Type*} [Group G] (E : Subgroup G) : ⁅E, E⁆ ≤ E :=
  Subgroup.commutator_le_self E

theorem map_mem_commutator_of_perfect {C G : Type*} [Group C] [Group G] (hC : Group.IsPerfect C)
    (f : C →* G) (H : Subgroup G) (hf : ∀ c, f c ∈ H) (c : C) : f c ∈ ⁅H, H⁆ := by
  have h : commutator C ≤ (⁅H, H⁆).comap f := by
    rw [commutator_def C, Subgroup.commutator_le]
    intro a _ b _
    rw [Subgroup.mem_comap, map_commutatorElement]
    exact Subgroup.commutator_mem_commutator (hf a) (hf b)
  rw [Group.isPerfect_def.1 hC] at h
  exact h (Subgroup.mem_top c)

theorem outer_norm_mem_rationalComponent (hT : rootDiagUnit τ a ∈ S.D.torus)
    (i : KernelComponent (rootCharHom a)) {s : ℕ} [NeZero s]
    (hs : (S.ρ : (Fin τ.rank → ℤ) → _)^[s] '' componentRoots (rootCharHom a) i =
      componentRoots (rootCharHom a) i)
    (hmin : ∀ k, 0 < k → k < s →
      (S.ρ : (Fin τ.rank → ℤ) → _)^[k] '' componentRoots (rootCharHom a) i ≠
        componentRoots (rootCharHom a) i)
    {C : Type*} [Group C] (hC : Group.IsPerfect C)
    (θ₀ : C →* (outerOrbitFamily S hT i hs hmin).S 0)
    (hfix : ∀ x, iterHom S.D.step s
      ((θ₀ x : (outerOrbitFamily S hT i hs hmin).S 0) : ModGL τ L) = θ₀ x) (x : C) :
    (outerOrbitFamily S hT i hs hmin).norm (θ₀ x) ∈
      rationalComponent S.ρ S.Γ (rootCharHom a) i := by
  let f : C →* ModGL τ L := (outerOrbitFamily S hT i hs hmin).norm.comp θ₀
  have hfA : ∀ x : C, f x ∈ (outerOrbitFamily S hT i hs hmin).Afix := fun x =>
    (outerOrbitFamily S hT i hs hmin).norm_mem_Afix (hfix x)
  have hAmodel : ∀ g ∈ (outerOrbitFamily S hT i hs hmin).Afix, g ∈ S.D.model := by
    intro g hg
    refine ⟨?_, hg.2⟩
    have : (outerOrbitFamily S hT i hs hmin).A ≤ adjointGroup τ L := by
      refine iSup_le fun k => iSup₂_le fun γ _ => ?_
      rw [rootSubgroup, Subgroup.closure_le]
      rintro _ ⟨c, rfl⟩
      exact pinnedX_mem_adjointGroup _ _
    exact this hg.1
  have hM : ∀ x : C, f x ∈ S.D.model := fun x => hAmodel _ (hfA x)
  have hΓ : ∀ x : C, f x ∈ S.Γ := map_mem_commutator_of_perfect hC f _ hM
  have hRS : ∀ x : C, f x ∈ rationalSpan S.ρ S.Γ (rootCharHom a) i := by
    intro x
    refine Subgroup.mem_inf.2 ⟨?_, hΓ x⟩
    have := (hfA x).1
    rw [outerOrbitFamily_A] at this
    exact this
  unfold rationalComponent
  exact map_mem_commutator_of_perfect hC f _ hRS x

theorem _root_.CFSG.HardMathSupport.Timmesfeld.CrossChar.rationalComponent_eq_range_of_hom_T
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
    (hθZ : ∀ c, θ c ∈ (outerOrbitFamily S hT i hs hmin).Z → c ∈ Subgroup.center C) :
    ∃ f : C →* ModGL τ L, rationalComponent S.ρ S.Γ (rootCharHom a) i ≤ f.range ∧
      f.ker ≤ Subgroup.center C ∧
      (Group.IsPerfect C → f.range ≤ rationalComponent S.ρ S.Γ (rootCharHom a) i) := by
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
  have hΓM : S.Γ ≤ S.D.model := commutator_le_self' _
  have hrsA : rationalSpan S.ρ S.Γ (rootCharHom a) i ≤ P.Afix := by
    intro x hx
    obtain ⟨hx1, hx2⟩ := Subgroup.mem_inf.1 hx
    refine ⟨?_, (hΓM hx2).2⟩
    rw [hP, outerOrbitFamily_A]
    exact hx1
  refine ⟨f, ?_, ?_, ?_⟩
  · intro g hg
    have h1 := P.commutator_Afix_le (Subgroup.commutator_mono hrsA hrsA hg)
    obtain ⟨y, hyY, rfl⟩ := P.mem_normImage.1 h1
    obtain ⟨c, hc⟩ := hYW hyY
    refine ⟨c, ?_⟩
    change P.norm (θ₀ c) = P.norm y
    congr 1
    exact Subtype.ext hc
  · intro c hc
    have h1 : P.norm (θ₀ c) = 1 := hc
    exact hθZ c (P.mem_Z_of_norm_eq_one h1)
  · intro hperf
    rintro _ ⟨x, rfl⟩
    exact outer_norm_mem_rationalComponent S hT i hs hmin hperf θ₀ hfix x

theorem rationalComponent_eq_rangeT
    (hT : rootDiagUnit τ a ∈ S.D.torus) (i : KernelComponent (rootCharHom a))
    {s : ℕ} [NeZero s]
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
    (Cg : Subgroup (ModGL τ (fixSubfield σ)))
    (hCg : Cg ≤ componentRootSpan (fixSubfield σ) (rootCharHom a) i)
    (hY : ∀ g g' : ModGL τ L, g ∈ rootSpan τ L (componentRoots (rootCharHom a) i) →
      g' ∈ rootSpan τ L (componentRoots (rootCharHom a) i) →
      frobGL σ g * g⁻¹ ∈ (outerOrbitFamily S hT i hs hmin).Z →
      frobGL σ g' * g'⁻¹ ∈ (outerOrbitFamily S hT i hs hmin).Z →
      ⁅g, g'⁆ ∈ Cg.map (baseChangeGL (fixSubfield σ).subtype)) :
    ∃ f : Cg →* ModGL τ L, rationalComponent S.ρ S.Γ (rootCharHom a) i ≤ f.range ∧
      f.ker ≤ Subgroup.center Cg ∧
      (⁅Cg, Cg⁆ = Cg → f.range ≤ rationalComponent S.ρ S.Γ (rootCharHom a) i) := by
  classical
  set P := outerOrbitFamily S hT i hs hmin with hP
  set ι := baseChangeGL (τ := τ) (fixSubfield σ).subtype with hι
  set Ψ := componentRoots (rootCharHom a) i with hΨ
  have hP0 : P.S 0 = rootSpan τ L Ψ := by
    rw [hP, outerOrbitFamily_S, ZMod.val_zero]
    simp only [Function.iterate_zero, id_eq, Set.image_id']
    rfl
  have hιC : ∀ x ∈ Cg, ι x ∈ CQ σ i := by
    intro x hx
    rw [CQ_eq_map]
    exact ⟨x, hCg hx, rfl⟩
  have hιS : ∀ x ∈ Cg, ι x ∈ rootSpan τ L Ψ := fun x hx => CQ_le_rootSpan σ i (hιC x hx)
  have hιinj : Function.Injective ι := baseChangeGL_injective _
  have hzA : ∀ a ∈ P.A, z * a * z⁻¹ ∈ P.A := by
    have h : P.A ≤ P.A.comap (MulAut.conj z).toMonoidHom := by
      refine iSup_le fun k => ?_
      obtain ⟨j, hj⟩ := outer_iterate_image_component S hT i k.val
      intro g hg
      have hg' : g ∈ rootSpan τ L (componentRoots (rootCharHom a) j) := by rw [hj]; exact hg
      have h2 := (hnorm j g).1 hg'
      rw [hj] at h2
      exact P.S_le_A k h2
    exact fun a ha => h ha
  have hZconj : ∀ X : ModGL τ L, z * X * z⁻¹ ∈ P.Z → X ∈ P.Z := by
    intro X hX
    rw [CycFamily.mem_Z] at hX ⊢
    intro a ha
    have := hX _ (hzA a ha)
    have e : z * a * z⁻¹ * (z * X * z⁻¹) = z * (a * X) * z⁻¹ := by group
    have e' : z * X * z⁻¹ * (z * a * z⁻¹) = z * (X * a) * z⁻¹ := by group
    rw [e, e'] at this
    simpa using this
  have hYc : ∀ u ∈ rootSpan τ L Ψ, iterHom S.D.step s u * u⁻¹ ∈ P.Z →
      ∃ g ∈ rootSpan τ L Ψ, u = z * g * z⁻¹ ∧ frobGL σ g * g⁻¹ ∈ P.Z := by
    intro u hu0 huZ
    have e : z * (z⁻¹ * u * z) * z⁻¹ = u := by group
    have hg : z⁻¹ * u * z ∈ rootSpan τ L Ψ := (hnorm i (z⁻¹ * u * z)).2 (by rw [e]; exact hu0)
    refine ⟨z⁻¹ * u * z, hg, by group, hZconj _ ?_⟩
    have h1 := hz _ hg
    rw [e] at h1
    have e2 : z * (frobGL σ (z⁻¹ * u * z) * (z⁻¹ * u * z)⁻¹) * z⁻¹ =
        (z * frobGL σ (z⁻¹ * u * z) * z⁻¹) * u⁻¹ := by group
    rw [e2, ← h1]
    exact huZ
  let θ : Cg →* ModGL τ L := (MulAut.conj z).toMonoidHom.comp (ι.comp Cg.subtype)
  have hθ : ∀ x : Cg, θ x = z * ι x.1 * z⁻¹ := fun x => rfl
  obtain ⟨f, hf1, hf2, hf3⟩ := rationalComponent_eq_range_of_hom_T S hT i hs hmin θ
    (fun x => (hnorm i _).1 (hιS x.1 x.2))
    (fun x => by rw [hθ, hz _ (hιS x.1 x.2), frobGL_eq_self_of_mem_CQ σ i (hιC x.1 x.2)])
    (fun u u' hu hu' huZ huZ' => by
      obtain ⟨g, hg, rfl, hgZ⟩ := hYc u hu huZ
      obtain ⟨g', hg', rfl, hgZ'⟩ := hYc u' hu' huZ'
      obtain ⟨c0, hc0, hc0e⟩ := hY g g' hg hg' hgZ hgZ'
      refine ⟨⟨c0, hc0⟩, ?_⟩
      show z * ι c0 * z⁻¹ = ⁅z * g * z⁻¹, z * g' * z⁻¹⁆
      rw [show ι c0 = ⁅g, g'⁆ from hc0e]
      simp only [commutatorElement_def]
      group)
    (fun c hc => by
      rw [hθ] at hc
      have h3 := hZconj _ hc
      rw [Subgroup.mem_center_iff]
      intro c'
      have h4 := P.mem_Z.1 h3 (ι c'.1) (P.S_le_A 0 (by rw [hP0]; exact hιS c'.1 c'.2))
      exact Subtype.ext (hιinj (by simpa using h4)))
  exact ⟨f, hf1, hf2, fun hperf => hf3 (Subgroup.isPerfect_iff.2 hperf)⟩

theorem iform_rho_iterate (n : ℕ) (x y : Fin τ.rank → ℤ) :
    iform ((S.ρ : (Fin τ.rank → ℤ) → _)^[n] x) ((S.ρ : (Fin τ.rank → ℤ) → _)^[n] y) =
      iform x y := by
  induction n with
  | zero => rfl
  | succ n ih => rw [Function.iterate_succ_apply', Function.iterate_succ_apply', iform_rho, ih]

theorem iform_neg_left_aux (x y : Fin τ.rank → ℤ) : iform (-x) y = -iform x y := by
  rw [← neg_one_smul ℤ x, iform_smul_left]; ring

theorem iform_neg_right_aux (x y : Fin τ.rank → ℤ) : iform x (-y) = -iform x y := by
  rw [← neg_one_smul ℤ y, iform_smul_right]; ring

theorem twistInner_of_twistKind_eq_innerT (hW : RootAutIsWeyl)
    (hT : rootDiagUnit τ a ∈ S.D.torus) (i : KernelComponent (rootCharHom a))
    (h : twistKind S.ρ (rootCharHom a) i = .inner) :
    twistInner (componentRoots (rootCharHom a) i)
      ((S.ρ : (Fin τ.rank → ℤ) → _)^[componentOrbitLength S.ρ
        (componentRoots (rootCharHom a) i)]) := by
  classical
  by_contra hn
  have hΨ := isRootComponent_componentRoots (χ := rootCharHom a) i
  obtain ⟨hs0, hs, -⟩ := outer_componentOrbitLength_spec S hT i
  unfold twistKind at h
  rw [ite_eq_right hn] at h
  split_ifs at h with h1 h2 h3
  refine hn (hW τ _ hΨ ?_ _ ?_ (fun γ _ δ _ => iform_rho_iterate S _ γ δ) ?_)
  · rintro (h4 | h4 | h4)
    · exact h3 h4
    · exact h2 h4
    · exact h1 (Or.inl h4)
  · refine ⟨fun x hx => ?_, ?_, hs.ge⟩
    · have h5 := Set.mem_image_of_mem ((S.ρ : (Fin τ.rank → ℤ) → _)^[componentOrbitLength S.ρ
        (componentRoots (rootCharHom a) i)]) hx
      rwa [hs] at h5
    · exact (S.ρ.injective.iterate _).injOn
  · intro γ hγ
    have hγ' : -γ ∈ componentRoots (rootCharHom a) i := hΨ.neg_mem γ hγ
    set σ := (S.ρ : (Fin τ.rank → ℤ) → _)^[componentOrbitLength S.ρ
      (componentRoots (rootCharHom a) i)] with hσ
    have e0 : iform (σ (-γ) + σ γ) (σ (-γ) + σ γ) = 0 := by
      simp only [iform_add_left, iform_add_right, hσ, iform_rho_iterate S]
      simp only [iform_neg_left_aux, iform_neg_right_aux]
      ring
    have hz : σ (-γ) + σ γ = 0 := by
      by_contra hne
      have := iform_self_pos hne
      omega
    exact eq_neg_of_add_eq_zero_left hz

private theorem unionRootSpan_singleton_eq (i : KernelComponent (rootCharHom a)) :
    unionRootSpan L (rootCharHom a) ({i} : Set (KernelComponent (rootCharHom a))) =
      rootSpan τ L (componentRoots (rootCharHom a) i) := by
  unfold unionRootSpan
  rw [unionRoots_singleton]

section OrbitCommT

variable (hT : rootDiagUnit τ a ∈ S.D.torus) (i : KernelComponent (rootCharHom a)) {s : ℕ}
  [NeZero s]
  (hs : (S.ρ : (Fin τ.rank → ℤ) → _)^[s] '' componentRoots (rootCharHom a) i =
    componentRoots (rootCharHom a) i)
  (hmin : ∀ k, 0 < k → k < s →
    (S.ρ : (Fin τ.rank → ℤ) → _)^[k] '' componentRoots (rootCharHom a) i ≠
      componentRoots (rootCharHom a) i)

include hT hs hmin in
theorem orbit_centralizer_hypT :
    ∀ w ∈ (outerOrbitFamily S hT i hs hmin).Z,
      ∀ x ∈ unionRootSpan L (rootCharHom a) ({i} : Set (KernelComponent (rootCharHom a))),
        x * w = w * x := by
  have hU := unionRootSpan_singleton_eq (L := L) i
  intro w hw x hx
  rw [hU] at hx
  exact (outerOrbitFamily S hT i hs hmin).mem_Z.1 hw x
    ((outerOrbitFamily S hT i hs hmin).S_le_A 0 (by
      show x ∈ rootSpan τ L ((S.ρ : (Fin τ.rank → ℤ) → _)^[(0 : ZMod s).val] ''
        componentRoots (rootCharHom a) i)
      rw [ZMod.val_zero]
      simpa using hx))

include hT hs hmin in
theorem orbit_commutator_mem_CQT (σ : L ≃+* L) (hsL : ∃ u : Lˣ, u ^ 2 ≠ 1)
    {g g' : ModGL τ L} (hg : g ∈ rootSpan τ L (componentRoots (rootCharHom a) i))
    (hg' : g' ∈ rootSpan τ L (componentRoots (rootCharHom a) i))
    (hgZ : frobGL σ g * g⁻¹ ∈ (outerOrbitFamily S hT i hs hmin).Z)
    (hgZ' : frobGL σ g' * g'⁻¹ ∈ (outerOrbitFamily S hT i hs hmin).Z) :
    ⁅g, g'⁆ ∈ CQ σ i := by
  have hU := unionRootSpan_singleton_eq (L := L) i
  exact commutator_mem_CQ (σ := σ) (i := i) hsL (orbit_centralizer_hypT S hT i hs hmin)
    (by rw [hU]; exact hg) (by rw [hU]; exact hg') hgZ hgZ'

include hT hs hmin in
theorem orbit_commutator_mem_commutator_CQT (σ : L ≃+* L) (hsL : ∃ u : Lˣ, u ^ 2 ≠ 1)
    (hF : ∀ d : L, σ d = d → d ≠ 0 → d = 1)
    {g g' : ModGL τ L} (hg : g ∈ rootSpan τ L (componentRoots (rootCharHom a) i))
    (hg' : g' ∈ rootSpan τ L (componentRoots (rootCharHom a) i))
    (hgZ : frobGL σ g * g⁻¹ ∈ (outerOrbitFamily S hT i hs hmin).Z)
    (hgZ' : frobGL σ g' * g'⁻¹ ∈ (outerOrbitFamily S hT i hs hmin).Z) :
    ⁅g, g'⁆ ∈ ⁅CQ σ i, CQ σ i⁆ := by
  have hU := unionRootSpan_singleton_eq (L := L) i
  exact commutator_mem_commutator_CQ (σ := σ) (i := i) hsL hF
    (orbit_centralizer_hypT S hT i hs hmin) (by rw [hU]; exact hg) (by rw [hU]; exact hg') hgZ hgZ'

end OrbitCommT

theorem rationalComponent_eq_range_componentRootSpanT
    (hT : rootDiagUnit τ a ∈ S.D.torus) (i : KernelComponent (rootCharHom a))
    {s : ℕ} [NeZero s]
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
    (hsL : ∃ u : Lˣ, u ^ 2 ≠ 1) :
    ∃ f : componentRootSpan (fixSubfield σ) (rootCharHom a) i →* ModGL τ L,
      rationalComponent S.ρ S.Γ (rootCharHom a) i ≤ f.range ∧
      f.ker ≤ Subgroup.center (componentRootSpan (fixSubfield σ) (rootCharHom a) i) ∧
      (⁅componentRootSpan (fixSubfield σ) (rootCharHom a) i,
          componentRootSpan (fixSubfield σ) (rootCharHom a) i⁆ =
          componentRootSpan (fixSubfield σ) (rootCharHom a) i →
        f.range ≤ rationalComponent S.ρ S.Γ (rootCharHom a) i) :=
  rationalComponent_eq_rangeT S hT i hs hmin σ z hnorm hz _ le_rfl fun _ _ hg hg' hgZ hgZ' => by
    have := orbit_commutator_mem_CQT S hT i hs hmin σ hsL hg hg' hgZ hgZ'
    rwa [CQ_eq_map] at this

theorem rationalComponent_quasisimple_inner_of_four_leT (hW : RootAutIsWeyl)
    (hT : rootDiagUnit τ a ∈ S.D.torus) (i : KernelComponent (rootCharHom a))
    (hkind : twistKind S.ρ (rootCharHom a) i = .inner)
    (hQ : 4 ≤ S.D.q ^ componentOrbitLength S.ρ (componentRoots (rootCharHom a) i)) :
    CFSG.IsQuasisimple (rationalComponent S.ρ S.Γ (rootCharHom a) i) := by
  classical
  obtain ⟨hs0, hs, hmin⟩ := outer_componentOrbitLength_spec S hT i
  set s := componentOrbitLength S.ρ (componentRoots (rootCharHom a) i) with hsdef
  have : NeZero s := ⟨hs0.ne'⟩
  have hinner := twistInner_of_twistKind_eq_innerT S hW hT i hkind
  obtain ⟨σ, z, hσ, hnorm, hz⟩ := exists_untwistT S hT i hs0 hinner
  obtain ⟨r, e, hr, hchar, he, hq⟩ := exists_char_pow S
  have : Fact r.Prime := ⟨hr⟩
  have hσ' : ∀ c, σ c = c ^ (r ^ (e * s)) := fun c => by rw [hσ, hq, ← pow_mul]
  have hQ' : 4 ≤ r ^ (e * s) := by rw [pow_mul, ← hq]; exact hQ
  obtain ⟨t, ht⟩ := exists_unit_sq_ne_one (L := L) σ hσ' (Nat.mul_pos he hs0) hQ'
  have hsL : ∃ u : Lˣ, u ^ 2 ≠ 1 := by
    refine ⟨Units.map (fixSubfield σ).subtype.toMonoidHom t, fun h => ht ?_⟩
    apply Units.ext
    apply Subtype.ext
    simpa using congrArg (fun x : Lˣ => (x : L)) h
  have hperfC := isPerfect_componentRootSpan_of_sq_ne_one (K := fixSubfield σ)
    (χ := rootCharHom a) ht i
  have hQS := isQuasisimple_componentRootSpan_of_sq_ne_one (K := fixSubfield σ)
    (χ := rootCharHom a) ht i
  obtain ⟨f, hf1, hker, hf2⟩ :=
    rationalComponent_eq_range_componentRootSpanT S hT i hs hmin σ z hnorm hz hsL
  rw [le_antisymm hf1 (hf2 (Subgroup.isPerfect_iff.1 hperfC))]
  exact isQuasisimple_range_of_ker_le_center hQS f hker

@[expose] def SmallFieldInner : Prop :=
  ∀ (τ : Tag) (K : Type) [Field K] [Finite K] (M : Type) [CommGroup M]
    (χ : Multiplicative (Fin τ.rank → ℤ) →* M) (i : KernelComponent χ) (p : ℕ),
    p.Prime → 5 ≤ p → (∀ γ, IsRoot τ γ → χ (Multiplicative.ofAdd γ) ^ p = 1) →
    (∃ γ, IsRoot τ γ ∧ χ (Multiplicative.ofAdd γ) ≠ 1) → Nat.card K ≤ 3 →
    p ∣ Nat.card (componentRootSpan K χ i) →
    CFSG.IsQuasisimple ↥(⁅componentRootSpan K χ i, componentRootSpan K χ i⁆ :
      Subgroup (ModGL τ K)) ∧
      (Nat.card K = 2 ∨
        ⁅componentRootSpan K χ i, componentRootSpan K χ i⁆ = componentRootSpan K χ i)

theorem rootChar_pow_eq_one_of_pow (hTp : rootDiagUnit τ a ^ p = 1) {γ : Fin τ.rank → ℤ}
    (hγ : IsRoot τ γ) : rootChar a γ ^ p = 1 := by
  have hp1 : (rootDiagUnit τ a) ^ p = 1 := hTp
  have key : ∀ n : ℕ, (rootDiagUnit τ a) ^ n * pinnedX τ L γ 1 * ((rootDiagUnit τ a) ^ n)⁻¹ =
      pinnedX τ L γ (((rootChar a γ ^ n : Lˣ)) : L) := by
    intro n
    induction n with
    | zero => simp
    | succ n ih =>
      have e : (rootDiagUnit τ a) ^ (n + 1) * pinnedX τ L γ 1 * ((rootDiagUnit τ a) ^ (n + 1))⁻¹ =
          rootDiagUnit τ a * ((rootDiagUnit τ a) ^ n * pinnedX τ L γ 1 *
            ((rootDiagUnit τ a) ^ n)⁻¹) * (rootDiagUnit τ a)⁻¹ := by
        rw [pow_succ']; group
      rw [e, ih, rootDiagUnit_conj_pinnedX a hγ, pow_succ', Units.val_mul]
  have h := key p
  rw [hp1, inv_one, one_mul, mul_one] at h
  have h2 := pinnedX_injective τ L γ h
  exact Units.ext (by simpa using h2.symm)

theorem rootChar_pow_eq_one_of_mem_E (hE : rootDiagUnit τ a ∈ S.E) {γ : Fin τ.rank → ℤ}
    (hγ : IsRoot τ γ) : rootChar a γ ^ p = 1 :=
  rootChar_pow_eq_one_of_pow (S.E_exp _ hE) hγ

theorem exists_rootChar_ne_one (ha1 : rootDiagUnit τ a ≠ 1) :
    ∃ γ : Fin τ.rank → ℤ, IsRoot τ γ ∧ rootChar a γ ≠ 1 := by
  by_contra h
  push Not at h
  apply ha1
  have : a = 1 := by
    funext j
    have h1 := h (Pi.single j 1) (isRoot_single τ j)
    have e : rootChar a (Pi.single j 1) = a j := by
      unfold rootChar
      rw [Finset.prod_eq_single j (fun k _ hk => by simp [Pi.single_apply, hk])
        (fun hj => absurd (Finset.mem_univ j) hj)]
      simp
    rw [e] at h1
    exact h1
  rw [this]
  exact rootDiagUnit_one

theorem rationalComponent_quasisimple_inner_of_smallT (hW : RootAutIsWeyl)
    (hsmall : SmallFieldInner)
    (hT : rootDiagUnit τ a ∈ S.D.torus) (hTp : rootDiagUnit τ a ^ p = 1)
    (ha1 : rootDiagUnit τ a ≠ 1) (i : KernelComponent (rootCharHom a))
    (hkind : twistKind S.ρ (rootCharHom a) i = .inner) (hp5 : 5 ≤ p)
    (hQ : S.D.q ^ componentOrbitLength S.ρ (componentRoots (rootCharHom a) i) < 4)
    (hbig : ¬ Nat.Coprime p (Nat.card (rationalComponent S.ρ S.Γ (rootCharHom a) i))) :
    CFSG.IsQuasisimple (rationalComponent S.ρ S.Γ (rootCharHom a) i) := by
  classical
  obtain ⟨hs0, hs, hmin⟩ := outer_componentOrbitLength_spec S hT i
  set s := componentOrbitLength S.ρ (componentRoots (rootCharHom a) i) with hsdef
  have : NeZero s := ⟨hs0.ne'⟩
  have hinner := twistInner_of_twistKind_eq_innerT S hW hT i hkind
  obtain ⟨σ, z, hσ, hnorm, hz⟩ := exists_untwistT S hT i hs0 hinner
  obtain ⟨r, e, hr, hchar, he, hq⟩ := exists_char_pow S
  have : Fact r.Prime := ⟨hr⟩
  have hσ' : ∀ c, σ c = c ^ (r ^ (e * s)) := fun c => by rw [hσ, hq, ← pow_mul]
  have hQ' : r ^ (e * s) < 4 := by rw [pow_mul, ← hq]; exact hQ
  obtain ⟨hfinset, hcardset⟩ := ncard_pow_eq_self (L := L) r (e * s) (Nat.mul_pos he hs0)
  have hset : (fixSubfield σ : Set L) = {c : L | c ^ (r ^ (e * s)) = c} := by
    ext c
    show c ∈ fixSubfield σ ↔ _
    rw [mem_fixSubfield, hσ']
    rfl
  have hfinK : Finite (fixSubfield σ) := by
    have h1 : (fixSubfield σ : Set L).Finite := by rw [hset]; exact hfinset
    exact h1.to_subtype
  have hKcard : Nat.card (fixSubfield σ) = r ^ (e * s) := by
    have h1 : Nat.card (fixSubfield σ) = (fixSubfield σ : Set L).ncard :=
      Nat.card_coe_set_eq (fixSubfield σ : Set L)
    rw [h1, hset, hcardset]
  have hKle : Nat.card (fixSubfield σ) ≤ 3 := by rw [hKcard]; omega
  have hsL : ∃ u : Lˣ, u ^ 2 ≠ 1 := by
    obtain ⟨c, hc⟩ := Infinite.exists_notMem_finset ({0, 1, -1} : Finset L)
    have hc0 : c ≠ 0 := fun h => hc (by simp [h])
    refine ⟨Units.mk0 c hc0, fun h => hc ?_⟩
    have h2 : c ^ 2 = 1 := by simpa using congrArg (fun x : Lˣ => (x : L)) h
    have h3 : (c - 1) * (c + 1) = 0 := by linear_combination h2
    rcases mul_eq_zero.1 h3 with h | h
    · simp [sub_eq_zero.1 h]
    · simp [eq_neg_of_add_eq_zero_left h]
  set C := componentRootSpan (fixSubfield σ) (rootCharHom a) i with hCdef
  obtain ⟨f₁, hf₁1, -, -⟩ :=
    rationalComponent_eq_range_componentRootSpanT S hT i hs hmin σ z hnorm hz hsL
  have hpC : p ∣ Nat.card C := by
    have h1 : p ∣ Nat.card (rationalComponent S.ρ S.Γ (rootCharHom a) i) :=
      (Nat.Prime.dvd_iff_not_coprime S.hp).2 hbig
    exact h1.trans ((Subgroup.card_dvd_of_le hf₁1).trans (Subgroup.card_range_dvd f₁))
  obtain ⟨hDQ, hD⟩ := hsmall τ (fixSubfield σ) Lˣ (rootCharHom a) i p S.hp hp5
    (fun γ hγ => rootChar_pow_eq_one_of_pow hTp hγ)
    (by obtain ⟨γ, hγ, hne⟩ := exists_rootChar_ne_one ha1; exact ⟨γ, hγ, hne⟩) hKle hpC
  have hY : ∀ g g' : ModGL τ L, g ∈ rootSpan τ L (componentRoots (rootCharHom a) i) →
      g' ∈ rootSpan τ L (componentRoots (rootCharHom a) i) →
      frobGL σ g * g⁻¹ ∈ (outerOrbitFamily S hT i hs hmin).Z →
      frobGL σ g' * g'⁻¹ ∈ (outerOrbitFamily S hT i hs hmin).Z →
      ⁅g, g'⁆ ∈ (⁅C, C⁆).map (baseChangeGL (fixSubfield σ).subtype) := by
    intro g g' hg hg' hgZ hgZ'
    rcases hD with hD2 | hDC
    · have hF : ∀ d : L, σ d = d → d ≠ 0 → d = 1 := by
        intro d hd hd0
        let : Fintype (fixSubfield σ) := Fintype.ofFinite _
        have hcard : Fintype.card (fixSubfield σ) = 2 := by
          rw [← Nat.card_eq_fintype_card]; exact hD2
        have hdK : d ∈ fixSubfield σ := hd
        have h1 := FiniteField.pow_card_sub_one_eq_one (⟨d, hdK⟩ : fixSubfield σ)
          (fun h => hd0 (congrArg Subtype.val h))
        rw [hcard] at h1
        simpa using congrArg Subtype.val h1
      have := orbit_commutator_mem_commutator_CQT S hT i hs hmin σ hsL hF hg hg' hgZ hgZ'
      rwa [CQ_eq_map, ← Subgroup.map_commutator] at this
    · have := orbit_commutator_mem_CQT S hT i hs hmin σ hsL hg hg' hgZ hgZ'
      rwa [CQ_eq_map, ← hDC] at this
  obtain ⟨f, hf1, hker, hf2⟩ := rationalComponent_eq_rangeT S hT i hs hmin σ z hnorm hz
    ⁅C, C⁆ (Subgroup.commutator_le_self _ |>.trans le_rfl) hY
  have hperfD : ⁅⁅C, C⁆, ⁅C, C⁆⁆ = ⁅C, C⁆ := Subgroup.isPerfect_iff.1 hDQ.1
  rw [le_antisymm hf1 (hf2 hperfD)]
  exact isQuasisimple_range_of_ker_le_center hDQ f hker

theorem rationalComponent_quasisimple_innerT (hW : RootAutIsWeyl) (hsmall : SmallFieldInner)
    (hT : rootDiagUnit τ a ∈ S.D.torus) (hTp : rootDiagUnit τ a ^ p = 1)
    (ha1 : rootDiagUnit τ a ≠ 1) (i : KernelComponent (rootCharHom a))
    (hkind : twistKind S.ρ (rootCharHom a) i = .inner)
    (hbig : ¬ Nat.Coprime p (Nat.card (rationalComponent S.ρ S.Γ (rootCharHom a) i))) :
    CFSG.IsQuasisimple (rationalComponent S.ρ S.Γ (rootCharHom a) i) := by
  by_cases hQ : 4 ≤ S.D.q ^ componentOrbitLength S.ρ (componentRoots (rootCharHom a) i)
  · exact rationalComponent_quasisimple_inner_of_four_leT S hW hT i hkind hQ
  · have hp5 : 5 ≤ p := by
      rcases S.hq with h | h
      · exact h
      · exfalso
        apply hQ
        obtain ⟨hs0, -, -⟩ := outer_componentOrbitLength_spec S hT i
        exact h.trans (Nat.le_self_pow hs0.ne' _)
    exact rationalComponent_quasisimple_inner_of_smallT S hW hsmall hT hTp ha1 i hkind hp5
      (not_le.1 hQ) hbig

theorem langComponentsQuasisimple_inner_of_small (hW : RootAutIsWeyl)
    (hsmall : SmallFieldInner) :
    LangComponentsQuasisimple .inner := fun _ _ _ _ _ S _ hE ha1 i hkind hbig =>
  rationalComponent_quasisimple_innerT S hW hsmall (S.E_le hE).1 (S.E_exp _ hE) ha1 i hkind hbig

end Reduction

end CFSG.HardMathSupport.Timmesfeld.LangTorus
