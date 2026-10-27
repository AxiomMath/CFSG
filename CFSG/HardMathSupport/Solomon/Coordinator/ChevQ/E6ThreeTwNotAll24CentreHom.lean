module

public import CFSG.HardMathSupport.Timmesfeld.CrossChar.TwCompSU

public section

namespace CFSG.HardMathSupport.Solomon.Coordinator.ChevQ.E6Three

namespace KSConn

open CFSG.Open CFSG.Blueprint.Chevalley CFSG.LieType.Chevalley CFSG.LieType.Steinberg.Adjoint
  CFSG.LocalAnalysis.ComponentInitial CFSG.LocalAnalysis.ComponentInitial.FourGroupChevalley
  CFSG.LieType.AlgebraicGroups CFSG.HardMathSupport.Timmesfeld.LangTorus
  CFSG.HardMathSupport.Timmesfeld.CrossChar
open Matrix CFSG.RankThree.Classical CFSG.RankThree.Classical2 CFSG.SectionRank.OddCover
  CFSG.Assembly.LowTwoRank CFSG.LocalAnalysis.GLTheoremB
open scoped commutatorElement MatrixGroups

set_option linter.unusedSectionVars false

theorem cycFamily_norm_apply_of_eq_one
    {G : Type*} [Group G] {F : G →* G} {s : ℕ} [NeZero s] (P : CycFamily F s) (hs : s = 1)
    (y : P.S 0) : P.norm y = (y : G) := by
  subst hs
  have h : P.diag y = Pi.mulSingle 0 (P.iter 0 y) := by
    funext k
    have hk : k = 0 := Subsingleton.elim _ _
    subst hk
    rfl
  rw [CycFamily.norm, MonoidHom.comp_apply, h, CycFamily.mu_mulSingle, CycFamily.coe_iter]
  simp


variable {τ : Tag} {L : Type} [Field L] [IsAlgClosed L] {p : ℕ} (S : LangSetup τ L p)
  {a ta : Fin τ.rank → Lˣ}

theorem rationalComponent_eq_range_of_hom_norm
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
      (Group.IsPerfect C → f.range ≤ rationalComponent S.ρ S.Γ (rootCharHom a) i) ∧
      ∀ (c : C) (y : (outerOrbitFamily S hT i hs hmin).S 0), (y : ModGL τ L) = θ c →
        f c = (outerOrbitFamily S hT i hs hmin).norm y := by
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
  refine ⟨f, ?_, ?_, ?_, ?_⟩
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
  · intro c y hy
    have : y = θ₀ c := Subtype.ext (by rw [hy]; rfl)
    rw [this]
    rfl

theorem two_suN_exists_hom_conj (hT : rootDiagUnit τ ta ∈ S.D.torus)
    (i : KernelComponent (rootCharHom ta)) {ν : ℕ} (hν : 3 ≤ ν)
    {ψ : SL(ν, L) →* ModGL τ L} {σ : Fin ν → Fin ν → Fin τ.rank → ℤ} (hψ : IsSLFrame ψ σ)
    (hΨ : componentRoots (rootCharHom ta) i = frameRoots σ) (π : Equiv.Perm (Fin ν))
    (hπ : ∀ a b, a ≠ b → (S.ρ : (Fin τ.rank → ℤ) → _)^[componentOrbitLength S.ρ
      (componentRoots (rootCharHom ta) i)] (σ a b) = σ (π b) (π a))
    {r e : ℕ} (hr : r.Prime) (hchar : CharP L r) (he : 0 < e) (hq : S.D.q = r ^ e)
    (hs1 : componentOrbitLength S.ρ (componentRoots (rootCharHom ta) i) = 1) :
    ∃ σQ : L ≃+* L,
      (∀ c, σQ c = c ^ (r ^ (e * componentOrbitLength S.ρ (componentRoots (rootCharHom ta) i)))) ∧
      ∃ f : ↥(fixSubgroup (stdUnitaryEquiv (ν := ν) σQ)) →* ModGL τ L,
        rationalComponent S.ρ S.Γ (rootCharHom ta) i ≤ f.range ∧
        f.ker ≤ Subgroup.center ↥(fixSubgroup (stdUnitaryEquiv (ν := ν) σQ)) ∧
        (Group.IsPerfect ↥(fixSubgroup (stdUnitaryEquiv (ν := ν) σQ)) →
          f.range ≤ rationalComponent S.ρ S.Γ (rootCharHom ta) i) ∧
        ∃ z : ModGL τ L, ∀ c : ↥(fixSubgroup (stdUnitaryEquiv (ν := ν) σQ)),
          f c = z * ψ (c : SL(ν, L)) * z⁻¹ := by
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
  have hQ : S.D.q ^ s = r ^ (e * s) := by rw [hq, ← pow_mul]
  set Fs : ModGL τ L →* ModGL τ L := iterHom S.D.step s with hFs
  set P := outerOrbitFamily S hT i hs hmin with hP
  have hP0 : P.S 0 = rootSpan τ L (componentRoots (rootCharHom ta) i) := by
    rw [hP, outerOrbitFamily_S, ZMod.val_zero]
    simp only [Function.iterate_zero, id_eq, Set.image_id']
  choose! ε hε using fun (a b : Fin ν) (hab : a ≠ b) => hψ.transv a b hab
  have hπne : ∀ a b : Fin ν, a ≠ b → π b ≠ π a := fun a b hab => (π.injective.ne hab).symm
  have hstepU : ∀ a b : Fin ν, a ≠ b → ∃ μ : Lˣ, ∀ c : L,
      Fs (pinnedX τ L (σ a b) c) = pinnedX τ L (σ (π b) (π a)) ((μ : L) * σQ c) := by
    intro a b hab
    obtain ⟨μ, hμ0, hμ⟩ := iter_step_pinnedX S s (hψ.isRoot a b hab)
    refine ⟨Units.mk0 μ hμ0, fun c => ?_⟩
    rw [hFs, iterHom_eq_iterate, hμ, hπ a b hab, hσc, ← hQ]
    rfl
  choose! μ hμ using hstepU
  set β : Fin ν → Fin ν → Lˣ := fun a b =>
    μ a b * ε a b ^ (r ^ (e * s)) * (ε (π b) (π a))⁻¹ with hβ
  have hkey : ∀ (a b : Fin ν) (hab : a ≠ b) (t : L),
      Fs (ψ (Matrix.SpecialLinearGroup.transvection hab t)) =
        ψ (Matrix.SpecialLinearGroup.transvection (hπne a b hab) ((β a b : L) * σQ t)) := by
    intro a b hab t
    rw [hε a b hab t, hμ a b hab, hε (π b) (π a) (hπne a b hab)]
    congr 1
    rw [map_mul, hσc (ε a b : L), hβ]
    simp only [Units.val_mul, Units.val_pow_eq_pow_val, Units.val_inv_eq_inv_val]
    have h0 : (ε (π b) (π a) : L) ≠ 0 := Units.ne_zero _
    field_simp
  have hcoc : ∀ a b c : Fin ν, a ≠ b → b ≠ c → a ≠ c → β a c = -(β a b * β b c) := by
    intro a b c hab hbc hac
    have hcomm := Matrix.SpecialLinearGroup.commutatorElement_transvection hab hbc hac (1 : L) 1
    rw [mul_one] at hcomm
    have h1 := congrArg (fun X => Fs (ψ X)) hcomm
    simp only [map_commutatorElement] at h1
    rw [hkey a b hab, hkey b c hbc, hkey a c hac, map_one, mul_one, mul_one, mul_one,
      ← map_commutatorElement ψ,
      commutator_transvection_rev (hπne a b hab) (hπne b c hbc) (hπne a c hac),
      hε _ _ (hπne a c hac), hε _ _ (hπne a c hac)] at h1
    have h2 := pinnedX_injective τ L _ h1
    have h0 : (ε (π c) (π a) : L) ≠ 0 := Units.ne_zero _
    apply Units.ext
    have h3 := mul_left_cancel₀ h0 h2
    rw [Units.val_neg, Units.val_mul]
    exact h3.symm
  obtain ⟨d, hd⟩ := exists_units_of_cocycle hν β hcoc
  set M : GL (Fin ν) L := diagHom ν d * (permGL π : GL (Fin ν) L)⁻¹ with hMdef
  obtain ⟨B, hB⟩ := exists_specialLinear_conj_eq (n := ν) (by omega) M
  have hBconj : ∀ (a b : Fin ν) (hab : a ≠ b) (u : L),
      B * Matrix.SpecialLinearGroup.transvection (hπne a b hab) u * B⁻¹ =
        Matrix.SpecialLinearGroup.transvection (Ne.symm hab) ((d b : L) * u * ((d a)⁻¹ : Lˣ)) := by
    intro a b hab u
    apply Subtype.ext
    rw [Matrix.SpecialLinearGroup.coe_mul, Matrix.SpecialLinearGroup.coe_mul,
      Matrix.SpecialLinearGroup.transvection_coe, Matrix.SpecialLinearGroup.transvection_coe, hB]
    have hM : ∀ Y : Matrix (Fin ν) (Fin ν) L, (M : Matrix (Fin ν) (Fin ν) L) * Y *
        (↑M⁻¹ : Matrix (Fin ν) (Fin ν) L) = (diagHom ν d : Matrix (Fin ν) (Fin ν) L) *
          ((↑(permGL π : GL (Fin ν) L)⁻¹ : Matrix (Fin ν) (Fin ν) L) * Y *
            ((permGL π : GL (Fin ν) L) : Matrix (Fin ν) (Fin ν) L)) *
              (↑(diagHom ν d)⁻¹ : Matrix (Fin ν) (Fin ν) L) := by
      intro Y
      simp only [hMdef, _root_.mul_inv_rev, inv_inv, Units.val_mul, Matrix.mul_assoc]
    rw [hM, Matrix.mul_add, Matrix.add_mul, Matrix.mul_one, Units.inv_mul,
      permGL_inv_mul_single_mul, diagHom_mul_one_add_single_mul d (Ne.symm hab) u]
  have hstd : ∀ X : SL(ν, L), ψ B * Fs (ψ X) * (ψ B)⁻¹ = ψ (stdUnitary σQ.toRingHom X) := by
    have h : (MulAut.conj (ψ B)).toMonoidHom.comp (Fs.comp ψ) =
        ψ.comp (stdUnitary σQ.toRingHom) := by
      refine MonoidHom.eq_of_eqOn_dense
        (CFSG.LinearGroups.special_linear_elementary_generation (n := ν) (K := L)) ?_
      rintro _ ⟨a, b, hab, t, rfl⟩
      simp only [MonoidHom.comp_apply, MulEquiv.coe_toMonoidHom, MulAut.conj_apply]
      rw [hkey a b hab t, ← map_mul, ← map_inv, ← map_mul, hBconj a b hab,
        stdUnitary_transvection]
      congr 2
      rw [hd a b hab]
      simp only [Units.val_neg, Units.val_mul, Units.val_inv_eq_inv_val,
        RingEquiv.toRingHom_eq_coe, RingEquiv.coe_toRingHom]
      have h0 : (d a : L) ≠ 0 := Units.ne_zero _
      have h0' : (d b : L) ≠ 0 := Units.ne_zero _
      field_simp
    intro X
    have := DFunLike.congr_fun h X
    simpa [MulAut.conj_apply] using this
  have hψS : ∀ X, ψ X ∈ rootSpan τ L (componentRoots (rootCharHom ta) i) := fun X => by
    rw [hΨ, ← hψ.range]
    exact ⟨X, rfl⟩
  have hy₁ : ψ B ∈ rootSpan τ L (kernelRoots (rootCharHom ta)) :=
    rootSpan_mono (fun γ hγ => hγ.1) (hψS B)
  obtain ⟨z, hz, hnorm⟩ := exists_lang_mul_T S hT hs0 hy₁
  have hconj : ∀ X : SL(ν, L), Fs (z * ψ X * z⁻¹) = z * ψ (stdUnitary σQ.toRingHom X) * z⁻¹ := by
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
  have hker : ψ.ker ≠ ⊤ := by
    intro h
    have h01 : (⟨0, by omega⟩ : Fin ν) ≠ ⟨1, by omega⟩ := by simp
    have h1 : Matrix.SpecialLinearGroup.transvection h01 (1 : L) ∈ ψ.ker := by
      rw [h]
      exact Subgroup.mem_top _
    rw [MonoidHom.mem_ker, hε _ _ h01, mul_one, ← pinnedX_zero τ L (σ _ _)] at h1
    exact Units.ne_zero _ (pinnedX_injective τ L _ h1)
  have hcentral : ∀ X : SL(ν, L), ψ X ∈ P.Z → X ∈ Subgroup.center SL(ν, L) := by
    intro X hX
    refine mem_center_SL_of_commute hν ψ hker fun Y => ?_
    have hYA : ψ Y ∈ P.A := P.S_le_A 0 (by rw [hP0]; exact hψS Y)
    exact ((CycFamily.mem_Z P).1 hX (ψ Y) hYA).symm
  set C := fixSubgroup (stdUnitaryEquiv (ν := ν) σQ) with hCdef
  have hCmem : ∀ X : SL(ν, L), X ∈ C ↔ stdUnitary σQ.toRingHom X = X := fun X => by
    rw [hCdef, mem_fixSubgroup, stdUnitaryEquiv_apply]
  let θ : C →* ModGL τ L := (MulAut.conj z).toMonoidHom.comp (ψ.comp C.subtype)
  have hθ : ∀ c : C, θ c = z * ψ c * z⁻¹ := fun c => rfl
  have hθS : ∀ c : C, θ c ∈ rootSpan τ L (componentRoots (rootCharHom ta) i) := fun c => by
    rw [hθ]
    exact (hnorm i _).1 (hψS c)
  have hθfix : ∀ c : C, Fs (θ c) = θ c := fun c => by
    rw [hθ, hconj, (hCmem c).1 c.2]
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
      stdUnitary σQ.toRingHom X * X⁻¹ ∈ Subgroup.center SL(ν, L) := by
    intro X hX
    have e : Fs (z * ψ X * z⁻¹) * (z * ψ X * z⁻¹)⁻¹ =
        z * ψ (stdUnitary σQ.toRingHom X * X⁻¹) * z⁻¹ := by
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
    set c := stdUnitary σQ.toRingHom X * X⁻¹ with hcdef
    set c' := stdUnitary σQ.toRingHom X' * X'⁻¹ with hc'def
    have hX : stdUnitary σQ.toRingHom X = c * X := by rw [hcdef, inv_mul_cancel_right]
    have hX' : stdUnitary σQ.toRingHom X' = c' * X' := by rw [hc'def, inv_mul_cancel_right]
    have hcomm : ∀ (w : SL(ν, L)) (hw : w ∈ Subgroup.center SL(ν, L)) (y : SL(ν, L)),
        Commute w y := fun w hw y => (Subgroup.mem_center_iff.1 hw y).symm
    have hfixc : stdUnitary σQ.toRingHom ⁅X, X'⁆ = ⁅X, X'⁆ := by
      rw [map_commutatorElement, hX, hX']
      exact CycFamily.commutatorElement_central_mul (hcomm c hc X) (hcomm c hc X')
        (hcomm c hc c') (hcomm c' hc' X) (hcomm c' hc' X')
    refine ⟨⟨⁅X, X'⁆, (hCmem _).2 hfixc⟩, ?_⟩
    rw [hθ]
    simp only [commutatorElement_def, map_mul, map_inv]
    group
  have hθZ : ∀ c : C, θ c ∈ P.Z → c ∈ Subgroup.center C := by
    intro c hc
    rw [hθ] at hc
    have h := hcentral _ (hZconj _ hc)
    rw [Subgroup.mem_center_iff]
    intro d'
    exact Subtype.ext (Subgroup.mem_center_iff.1 h d')
  obtain ⟨f, hf1, hfker, hf2, hfn⟩ := rationalComponent_eq_range_of_hom_norm S hT i hs hmin θ hθS
    hθfix hθY hθZ
  refine ⟨σQ, hσc, f, hf1, hfker, hf2, z, fun c => ?_⟩
  have hnorm := hfn c ⟨θ c, by rw [hP0]; exact hθS c⟩ rfl
  rw [hnorm, cycFamily_norm_apply_of_eq_one P hs1]
  rfl

end KSConn

end CFSG.HardMathSupport.Solomon.Coordinator.ChevQ.E6Three
