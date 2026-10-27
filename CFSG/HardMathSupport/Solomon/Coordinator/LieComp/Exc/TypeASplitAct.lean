module

public import CFSG.HardMathSupport.Timmesfeld.RootAut.Main
public import CFSG.HardMathSupport.Solomon.Coordinator.LieComp.Exc.TypeASplitConj

public section

namespace CFSG.HardMathSupport.Solomon.Coordinator.LieComp

open CFSG.Open CFSG.Blueprint.Chevalley CFSG.LieType.Chevalley CFSG.LieType.Steinberg.Adjoint
  CFSG.LieType.AlgebraicGroups CFSG.HardMathSupport.Timmesfeld.LangTorus
  CFSG.HardMathSupport.Timmesfeld.CrossChar CFSG.LocalAnalysis.ComponentInitial
  CFSG.LocalAnalysis.ComponentInitial.FourGroupChevalley
  CFSG.HardMathSupport.Solomon.Coordinator.ChevQ.E6Three
open Matrix CFSG.RankThree.Classical CFSG.RankThree.Classical2 CFSG.SectionRank.OddCover
  CFSG.Assembly.LowTwoRank CFSG.LocalAnalysis.GLTheoremB
open scoped commutatorElement MatrixGroups

private theorem u3split_norm_conj {G : Type*} [Group G] {F : G →* G} {s : ℕ} [NeZero s]
    (P : CycFamily F s) (y : P.S 0) {g : G} (hg : g ∈ P.S 0) :
    (P.norm y : G) * g * (P.norm y : G)⁻¹ = (y : G) * g * (y : G)⁻¹ := by
  classical
  set u : ∀ k, P.S k := P.diag y with hu
  have hu0 : u 0 = y := by
    show P.iter 0 y = y
    ext
    rw [CycFamily.coe_iter]
    simp
  have hdecomp : u = Pi.mulSingle 0 y * Function.update u 0 1 := by
    funext j
    by_cases hj : j = 0
    · subst hj
      simp [hu0]
    · simp [Pi.mul_apply, Pi.mulSingle_eq_of_ne hj, Function.update_of_ne hj]
  set m : G := P.mu (Function.update u 0 1) with hm
  have hnorm : (P.norm y : G) = (y : G) * m := by
    rw [CycFamily.norm, MonoidHom.comp_apply, ← hu, hdecomp, map_mul, P.mu_mulSingle]
  have hm_comm : Commute (g : G) m := by
    have h1 : Commute (P.mu (Pi.mulSingle 0 ⟨g, hg⟩)) (P.mu (Function.update u 0 1)) := by
      refine P.commute_mu_of_commute _ _ ?_
      funext j
      by_cases hj : j = 0
      · subst hj
        simp
      · simp [Pi.mul_apply, Pi.mulSingle_eq_of_ne hj, Function.update_of_ne hj]
    rwa [P.mu_mulSingle] at h1
  calc (P.norm y : G) * g * (P.norm y : G)⁻¹
      = ((y : G) * m) * g * (((y : G) * m))⁻¹ := by rw [hnorm]
    _ = (y : G) * g * (y : G)⁻¹ := by
      rw [_root_.mul_inv_rev]
      calc ((y : G) * m) * g * (m⁻¹ * (y : G)⁻¹)
          = (y : G) * (m * g * m⁻¹) * (y : G)⁻¹ := by group
        _ = (y : G) * g * (y : G)⁻¹ := by
          rw [hm_comm.eq.symm]
          group

theorem cycFamily_norm_eq_self_of_eq_one {G : Type*} [Group G] {F : G →* G} {s : ℕ} [NeZero s]
    (P : CycFamily F s) (hs : s = 1) (y : P.S 0) : (P.norm y : G) = (y : G) := by
  have : Subsingleton (ZMod s) := ZMod.subsingleton_iff.2 hs
  have hdiag : P.diag y = Pi.mulSingle 0 (P.diag y 0) := by
    funext k
    rw [Subsingleton.elim k 0]
    simp
  rw [CycFamily.norm, MonoidHom.comp_apply, hdiag, P.mu_mulSingle]
  simp

theorem splitShape_of_twistKind_inner
    {τ : Tag} {L : Type} [Field L] [IsAlgClosed L] {p₀ : ℕ} (S : LangSetup τ L p₀)
    {a : Fin τ.rank → Lˣ} (hT : rootDiagUnit τ a ∈ S.D.torus)
    (i : KernelComponent (rootCharHom a)) (hkind : twistKind S.ρ (rootCharHom a) i = .inner)
    {ν : ℕ} (hν : 3 ≤ ν) {ψ : SL(ν, L) →* ModGL τ L} {σ : Fin ν → Fin ν → Fin τ.rank → ℤ}
    (hψ : IsSLFrame ψ σ) {κ : ℤ} (hκ : κ ≠ 0)
    (hnorm : ∀ x y, x ≠ y → iform (σ x y) (σ x y) = 2 * κ)
    (hΨ : componentRoots (rootCharHom a) i = frameRoots σ) :
    ∃ π : Equiv.Perm (Fin ν), ∀ x y, x ≠ y →
      (S.ρ : (Fin τ.rank → ℤ) → _)^[componentOrbitLength S.ρ
        (componentRoots (rootCharHom a) i)] (σ x y) = σ (π x) (π y) := by
  classical
  have hinner := twistInner_of_twistKind_eq_innerT S
    CFSG.HardMathSupport.Timmesfeld.RootAut.rootAutIsWeyl_holds hT i hkind
  obtain ⟨w, hw, hwσ⟩ := hinner
  have hw' : w ∈ Subgroup.closure {s : WeylGroup τ | ∃ γ ∈ frameRoots σ, s = rootReflection γ} := by
    simpa [hΨ] using hw
  have key : ∀ w ∈ Subgroup.closure {s : WeylGroup τ | ∃ γ ∈ frameRoots σ,
      s = rootReflection γ},
      ∃ π : Equiv.Perm (Fin ν), ∀ x y, x ≠ y → w • σ x y = σ (π x) (π y) := by
    intro w hw
    induction hw using Subgroup.closure_induction with
    | mem s hs =>
      obtain ⟨γ, hγ, rfl⟩ := hs
      obtain ⟨u, v, huv, rfl⟩ := hγ
      exact ⟨Equiv.swap u v, fun x y _ => hψ.rootReflection_smul hκ hnorm huv x y⟩
    | one => exact ⟨1, fun x y _ => by simp⟩
    | mul w₁ w₂ _ _ ih₁ ih₂ =>
      obtain ⟨π₁, h₁⟩ := ih₁
      obtain ⟨π₂, h₂⟩ := ih₂
      refine ⟨π₁ * π₂, fun x y hxy => ?_⟩
      rw [mul_smul, h₂ x y hxy, h₁ (π₂ x) (π₂ y) (π₂.injective.ne hxy)]
      simp [Equiv.Perm.mul_apply]
    | inv w₁ _ ih =>
      obtain ⟨π, hπ⟩ := ih
      refine ⟨π⁻¹, fun x y hxy => ?_⟩
      have h1 : w₁ • σ (π⁻¹ x) (π⁻¹ y) = σ x y := by
        rw [hπ (π⁻¹ x) (π⁻¹ y) (π.symm.injective.ne hxy)]
        simp
      calc w₁⁻¹ • σ x y = w₁⁻¹ • (w₁ • σ (π⁻¹ x) (π⁻¹ y)) := by rw [h1]
        _ = σ (π⁻¹ x) (π⁻¹ y) := inv_smul_smul w₁ _
  obtain ⟨π, hπ⟩ := key w hw'
  refine ⟨π, fun x y hxy => ?_⟩
  have hmem : σ x y ∈ componentRoots (rootCharHom a) i := by
    rw [hΨ]
    exact ⟨x, y, hxy, rfl⟩
  rw [hwσ (σ x y) hmem]
  exact hπ x y hxy

theorem split_exists_hom_untwist
    {τ : Tag} {L : Type} [Field L] [IsAlgClosed L] {p₀ : ℕ} (S : LangSetup τ L p₀)
    {ta : Fin τ.rank → Lˣ} (hT : rootDiagUnit τ ta ∈ S.D.torus)
    (i : KernelComponent (rootCharHom ta)) {ν : ℕ} (hν : 3 ≤ ν) {ψ : SL(ν, L) →* ModGL τ L}
    {σ : Fin ν → Fin ν → Fin τ.rank → ℤ} (hψ : IsSLFrame ψ σ)
    (hΨ : componentRoots (rootCharHom ta) i = frameRoots σ) (π : Equiv.Perm (Fin ν))
    (hπ : ∀ a b, a ≠ b → (S.ρ : (Fin τ.rank → ℤ) → _)^[componentOrbitLength S.ρ
      (componentRoots (rootCharHom ta) i)] (σ a b) = σ (π a) (π b))
    {r e : ℕ} (hr : r.Prime) (hchar : CharP L r) (he : 0 < e) (hq : S.D.q = r ^ e) :
    ∃ σQ : L ≃+* L,
      (∀ c, σQ c = c ^ (r ^ (e * componentOrbitLength S.ρ (componentRoots (rootCharHom ta) i)))) ∧
      ∃ z ∈ torusGroup τ L ⊔ rootSpan τ L (kernelRoots (rootCharHom ta)),
      (∀ X : SL(ν, L),
        iterHom S.D.step (componentOrbitLength S.ρ (componentRoots (rootCharHom ta) i))
            (z * ψ X * z⁻¹) =
          z * ψ (Matrix.SpecialLinearGroup.map σQ.toRingHom X) * z⁻¹) ∧
      ∃ f : SL(ν, ↥(fixSubfield σQ)) →* ModGL τ L,
        f.range = rationalComponent S.ρ S.Γ (rootCharHom ta) i ∧
        f.ker ≤ Subgroup.center SL(ν, ↥(fixSubfield σQ)) ∧
        (∀ (X : SL(ν, ↥(fixSubfield σQ))),
          ∀ g ∈ rootSpan τ L (componentRoots (rootCharHom ta) i),
            f X * g * (f X)⁻¹ =
              (z * ψ (Matrix.SpecialLinearGroup.map (fixSubfield σQ).subtype X) * z⁻¹) * g *
                (z * ψ (Matrix.SpecialLinearGroup.map (fixSubfield σQ).subtype X) * z⁻¹)⁻¹) ∧
        (componentOrbitLength S.ρ (componentRoots (rootCharHom ta) i) = 1 →
          ∀ X : SL(ν, ↥(fixSubfield σQ)),
            f X = z * ψ (Matrix.SpecialLinearGroup.map (fixSubfield σQ).subtype X) * z⁻¹) := by
  classical
  obtain ⟨hs0, hs, hmin⟩ := outer_componentOrbitLength_spec S hT i
  set s := componentOrbitLength S.ρ (componentRoots (rootCharHom ta) i) with hsdef
  have : NeZero s := ⟨hs0.ne'⟩
  have : Fact r.Prime := ⟨hr⟩
  have : CharP L r := hchar
  obtain ⟨σQ, hσQ⟩ := exists_ringEquiv_frob (L := L) r (e * s)
  have hσc : ∀ c, σQ c = c ^ (r ^ (e * s)) := fun c => by
    have h1 : σQ c = iterateFrobenius L r (e * s) c := by
      rw [← hσQ]
      rfl
    rw [h1, iterateFrobenius_def]
  obtain ⟨B, hstd⟩ := split_exists_pin S hν hψ π hπ hq hσc
  set Fs : ModGL τ L →* ModGL τ L := iterHom S.D.step s with hFs
  set P := outerOrbitFamily S hT i hs hmin with hP
  have hP0 : P.S 0 = rootSpan τ L (componentRoots (rootCharHom ta) i) := by
    rw [hP, outerOrbitFamily_S, ZMod.val_zero]
    simp only [Function.iterate_zero, id_eq, Set.image_id']
  have hψS : ∀ X, ψ X ∈ rootSpan τ L (componentRoots (rootCharHom ta) i) := fun X => by
    rw [hΨ, ← hψ.range]
    exact ⟨X, rfl⟩
  have hy₁ : ψ B ∈ rootSpan τ L (kernelRoots (rootCharHom ta)) :=
    rootSpan_mono (fun γ hγ => hγ.1) (hψS B)
  obtain ⟨z, hzZ, hz⟩ := exists_lang_torus_sup_kernelRoots S hs0
    (fun γ hγ => outer_iterate_mem_kernelRoots S hT s hγ) (Subgroup.mem_sup_right hy₁)
  have hnorm : ∀ j : KernelComponent (rootCharHom ta), ∀ g : ModGL τ L,
      g ∈ rootSpan τ L (componentRoots (rootCharHom ta) j) ↔
        z * g * z⁻¹ ∈ rootSpan τ L (componentRoots (rootCharHom ta) j) :=
    fun j g => mem_componentRootSpan_iff_conj_of_mem hzZ j g
  have hconj : ∀ X : SL(ν, L), Fs (z * ψ X * z⁻¹) =
      z * ψ (Matrix.SpecialLinearGroup.map σQ.toRingHom X) * z⁻¹ := by
    intro X
    rw [← hstd X, map_mul, map_mul, map_inv, hz]
    group
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
  have h01 : (⟨0, by omega⟩ : Fin ν) ≠ ⟨1, by omega⟩ := by simp
  obtain ⟨ε₀, hε₀⟩ := hψ.transv _ _ h01
  have hker : ψ.ker ≠ ⊤ := by
    intro h
    have h1 : Matrix.SpecialLinearGroup.transvection h01 (1 : L) ∈ ψ.ker := by
      rw [h]
      exact Subgroup.mem_top _
    rw [MonoidHom.mem_ker, hε₀, mul_one, ← pinnedX_zero τ L (σ _ _)] at h1
    exact Units.ne_zero _ (pinnedX_injective τ L _ h1)
  have hcentral : ∀ X : SL(ν, L), ψ X ∈ P.Z → X ∈ Subgroup.center SL(ν, L) := by
    intro X hX
    refine mem_center_SL_of_commute hν ψ hker fun Y => ?_
    have hYA : ψ Y ∈ P.A := P.S_le_A 0 (by rw [hP0]; exact hψS Y)
    exact ((CycFamily.mem_Z P).1 hX (ψ Y) hYA).symm
  set K : Subfield L := fixSubfield σQ with hKdef
  let ι : SL(ν, ↥K) →* SL(ν, L) := Matrix.SpecialLinearGroup.map K.subtype
  have hιinj : Function.Injective ι := specialLinearGroup_map_injective K.subtype_injective
  have hσι : ∀ c : SL(ν, ↥K), Matrix.SpecialLinearGroup.map σQ.toRingHom (ι c) = ι c := by
    intro c
    ext i j
    simp only [ι, Matrix.SpecialLinearGroup.map_apply_coe, RingHom.mapMatrix_apply,
      Matrix.map_apply, RingEquiv.toRingHom_eq_coe, RingEquiv.coe_toRingHom]
    exact (mem_fixSubfield σQ).1 (c i j).2
  have hιrange : ∀ Y : SL(ν, L), Matrix.SpecialLinearGroup.map σQ.toRingHom Y = Y →
      ∃ c : SL(ν, ↥K), ι c = Y := by
    intro Y hY
    refine exists_map_eq_of_forall_mem_range K.subtype_injective Y fun i j => ?_
    have := congrArg (fun Z : SL(ν, L) => (Z : Matrix (Fin ν) (Fin ν) L) i j) hY
    simp only [Matrix.SpecialLinearGroup.map_apply_coe, RingHom.mapMatrix_apply,
      Matrix.map_apply, RingEquiv.toRingHom_eq_coe, RingEquiv.coe_toRingHom] at this
    exact ⟨⟨_, (mem_fixSubfield σQ).2 this⟩, rfl⟩
  let θ : SL(ν, ↥K) →* ModGL τ L := (MulAut.conj z).toMonoidHom.comp (ψ.comp ι)
  have hθ : ∀ c : SL(ν, ↥K), θ c = z * ψ (ι c) * z⁻¹ := fun c => rfl
  have hθS : ∀ c : SL(ν, ↥K),
      θ c ∈ rootSpan τ L (componentRoots (rootCharHom ta) i) := fun c => by
    rw [hθ]
    exact (hnorm i _).1 (hψS _)
  have hθfix : ∀ c : SL(ν, ↥K), Fs (θ c) = θ c := fun c => by
    rw [hθ, hconj, hσι]
  have hpre : ∀ g ∈ rootSpan τ L (componentRoots (rootCharHom ta) i),
      ∃ X : SL(ν, L), g = z * ψ X * z⁻¹ := by
    intro g hg
    have h1 : z⁻¹ * g * z ∈ rootSpan τ L (componentRoots (rootCharHom ta) i) := (hnorm i _).2 (by
      have e : z * (z⁻¹ * g * z) * z⁻¹ = g := by group
      rw [e]
      exact hg)
    rw [hΨ, ← hψ.range] at h1
    obtain ⟨X, hX⟩ := h1
    exact ⟨X, by rw [hX]; group⟩
  have hfixmod : ∀ X : SL(ν, L), Fs (z * ψ X * z⁻¹) * (z * ψ X * z⁻¹)⁻¹ ∈ P.Z →
      Matrix.SpecialLinearGroup.map σQ.toRingHom X * X⁻¹ ∈ Subgroup.center SL(ν, L) := by
    intro X hX
    have e : Fs (z * ψ X * z⁻¹) * (z * ψ X * z⁻¹)⁻¹ =
        z * ψ (Matrix.SpecialLinearGroup.map σQ.toRingHom X * X⁻¹) * z⁻¹ := by
      rw [hconj, map_mul, map_inv]
      group
    rw [e] at hX
    exact hcentral _ (hZconj _ hX)
  have hθY : ∀ g g' : ModGL τ L, g ∈ rootSpan τ L (componentRoots (rootCharHom ta) i) →
      g' ∈ rootSpan τ L (componentRoots (rootCharHom ta) i) → Fs g * g⁻¹ ∈ P.Z →
        Fs g' * g'⁻¹ ∈ P.Z → ⁅g, g'⁆ ∈ θ.range := by
    intro g g' hg hg' hgZ hg'Z
    obtain ⟨X, rfl⟩ := hpre g hg
    obtain ⟨X', rfl⟩ := hpre g' hg'
    have hc := hfixmod X hgZ
    have hc' := hfixmod X' hg'Z
    set c := Matrix.SpecialLinearGroup.map σQ.toRingHom X * X⁻¹ with hcdef
    set c' := Matrix.SpecialLinearGroup.map σQ.toRingHom X' * X'⁻¹ with hc'def
    have hX : Matrix.SpecialLinearGroup.map σQ.toRingHom X = c * X := by
      rw [hcdef, inv_mul_cancel_right]
    have hX' : Matrix.SpecialLinearGroup.map σQ.toRingHom X' = c' * X' := by
      rw [hc'def, inv_mul_cancel_right]
    have hcomm : ∀ (w : SL(ν, L)) (hw : w ∈ Subgroup.center SL(ν, L)) (y : SL(ν, L)),
        Commute w y := fun w hw y => (Subgroup.mem_center_iff.1 hw y).symm
    have hfixc : Matrix.SpecialLinearGroup.map σQ.toRingHom ⁅X, X'⁆ = ⁅X, X'⁆ := by
      rw [map_commutatorElement, hX, hX']
      exact CycFamily.commutatorElement_central_mul (hcomm c hc X) (hcomm c hc X')
        (hcomm c hc c') (hcomm c' hc' X) (hcomm c' hc' X')
    obtain ⟨c₀, hc₀⟩ := hιrange _ hfixc
    refine ⟨c₀, ?_⟩
    rw [hθ, hc₀]
    simp only [commutatorElement_def, map_mul, map_inv]
    group
  have hθZ : ∀ c : SL(ν, ↥K), θ c ∈ P.Z → c ∈ Subgroup.center SL(ν, ↥K) := by
    intro c hc
    rw [hθ] at hc
    have h := hcentral _ (hZconj _ hc)
    rw [Subgroup.mem_center_iff]
    intro c2
    apply hιinj
    rw [map_mul, map_mul]
    exact Subgroup.mem_center_iff.1 h (ι c2)
  obtain ⟨f, hf1, hfker, hf2, hfn⟩ :=
    KSConn.rationalComponent_eq_range_of_hom_norm S hT i hs hmin θ hθS hθfix hθY hθZ
  let θ₀ : SL(ν, ↥K) →* P.S 0 := θ.codRestrict (P.S 0) fun c => by
    rw [hP0]
    exact hθS c
  have hfeq : f = P.norm.comp θ₀ := by
    refine MonoidHom.ext fun c => ?_
    rw [hfn c (θ₀ c) rfl]
    rfl
  have hperf : Group.IsPerfect SL(ν, ↥K) :=
    CFSG.LinearGroups.special_linear_dimension_at_least_three_perfect hν
  have hact : ∀ (X : SL(ν, ↥K)) (g : ModGL τ L),
      g ∈ rootSpan τ L (componentRoots (rootCharHom ta) i) →
      (P.norm.comp θ₀) X * g * ((P.norm.comp θ₀) X)⁻¹ =
        (z * ψ (ι X) * z⁻¹) * g * (z * ψ (ι X) * z⁻¹)⁻¹ := by
    intro X g hg
    have hgP : g ∈ P.S 0 := by rw [hP0]; exact hg
    change P.norm (θ₀ X) * g * (P.norm (θ₀ X))⁻¹ =
      (z * ψ (ι X) * z⁻¹) * g * (z * ψ (ι X) * z⁻¹)⁻¹
    rw [u3split_norm_conj P (θ₀ X) hgP]
    change θ X * g * (θ X)⁻¹ =
      (z * ψ (ι X) * z⁻¹) * g * (z * ψ (ι X) * z⁻¹)⁻¹
    rw [hθ X]
  refine ⟨σQ, hσc, z, hzZ, ?_, f, le_antisymm (hf2 hperf) hf1, hfker, ?_, ?_⟩
  · intro X
    exact hconj X
  · intro X g hg
    rw [hfeq]
    exact hact X g hg
  · intro hs1 X
    rw [hfeq]
    change (P.norm (θ₀ X) : ModGL τ L) = z * ψ (ι X) * z⁻¹
    rw [cycFamily_norm_eq_self_of_eq_one P (hsdef.trans hs1) (θ₀ X)]
    exact hθ X

theorem split_exists_hom_act
    {τ : Tag} {L : Type} [Field L] [IsAlgClosed L] {p₀ : ℕ} (S : LangSetup τ L p₀)
    {ta : Fin τ.rank → Lˣ} (hT : rootDiagUnit τ ta ∈ S.D.torus)
    (i : KernelComponent (rootCharHom ta)) {ν : ℕ} (hν : 3 ≤ ν) {ψ : SL(ν, L) →* ModGL τ L}
    {σ : Fin ν → Fin ν → Fin τ.rank → ℤ} (hψ : IsSLFrame ψ σ)
    (hΨ : componentRoots (rootCharHom ta) i = frameRoots σ) (π : Equiv.Perm (Fin ν))
    (hπ : ∀ a b, a ≠ b → (S.ρ : (Fin τ.rank → ℤ) → _)^[componentOrbitLength S.ρ
      (componentRoots (rootCharHom ta) i)] (σ a b) = σ (π a) (π b))
    {r e : ℕ} (hr : r.Prime) (hchar : CharP L r) (he : 0 < e) (hq : S.D.q = r ^ e) :
    ∃ σQ : L ≃+* L,
      (∀ c, σQ c = c ^ (r ^ (e * componentOrbitLength S.ρ (componentRoots (rootCharHom ta) i)))) ∧
      ∃ z ∈ torusGroup τ L ⊔ rootSpan τ L (kernelRoots (rootCharHom ta)),
      ∃ f : SL(ν, ↥(fixSubfield σQ)) →* ModGL τ L,
        f.range = rationalComponent S.ρ S.Γ (rootCharHom ta) i ∧
        f.ker ≤ Subgroup.center SL(ν, ↥(fixSubfield σQ)) ∧
        ∀ (X : SL(ν, ↥(fixSubfield σQ))),
          ∀ g ∈ rootSpan τ L (componentRoots (rootCharHom ta) i),
            f X * g * (f X)⁻¹ =
              (z * ψ (Matrix.SpecialLinearGroup.map (fixSubfield σQ).subtype X) * z⁻¹) * g *
                (z * ψ (Matrix.SpecialLinearGroup.map (fixSubfield σQ).subtype X) * z⁻¹)⁻¹ := by
  obtain ⟨σQ, hσQ, z, hz, _, f, hfrange, hfker, hfact, _⟩ :=
    split_exists_hom_untwist S hT i hν hψ hΨ π hπ hr hchar he hq
  exact ⟨σQ, hσQ, z, hz, f, hfrange, hfker, hfact⟩

end CFSG.HardMathSupport.Solomon.Coordinator.LieComp

end
