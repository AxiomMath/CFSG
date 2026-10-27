module

public import CFSG.LocalAnalysis.GLTheoremA.CatA.T171ShapeExcActNorm
public import CFSG.LocalAnalysis.GLTheoremA.CatC.KD264LieCompAlgExcCore
import CFSG.RankThree.Classical2.SLnConjLemmas

public section

namespace CFSG.LocalAnalysis.GLTheoremA.T171Sh

open CFSG.Blueprint.Chevalley CFSG.LieType.Chevalley CFSG.LieType.Steinberg.Adjoint
  CFSG.LocalAnalysis.ComponentInitial CFSG.LocalAnalysis.ComponentInitial.FourGroupChevalley
  CFSG.LocalAnalysis.GLTheoremA.KD264Lie CFSG.HardMathSupport.Timmesfeld.CrossChar
  CFSG.HardMathSupport.Timmesfeld.LangTorus CFSG.LieType.AlgebraicGroups
  CFSG.ComponentClassification.OuterAutomorphisms
  CFSG.ComponentClassification.PerfectAutomorphisms CFSG.GroupActions
  CFSG.ComponentClassification.PerfectCentralQuotient CFSG.RankThree.Classical2
  Matrix
open scoped Pointwise commutatorElement MatrixGroups

section Aux

variable {L : Type} [Field L] {ν : ℕ}

private noncomputable def invTransposeGL : GL (Fin ν) L →* GL (Fin ν) L where
  toFun N := ⟨((N⁻¹ : GL (Fin ν) L) : Matrix (Fin ν) (Fin ν) L)ᵀ,
    ((N : GL (Fin ν) L) : Matrix (Fin ν) (Fin ν) L)ᵀ,
    by rw [← Matrix.transpose_mul, ← Units.val_mul, mul_inv_cancel, Units.val_one,
      Matrix.transpose_one],
    by rw [← Matrix.transpose_mul, ← Units.val_mul, inv_mul_cancel, Units.val_one,
      Matrix.transpose_one]⟩
  map_one' := by
    apply Units.ext
    simp
  map_mul' N N' := by
    apply Units.ext
    change (((N * N')⁻¹ : GL (Fin ν) L) : Matrix (Fin ν) (Fin ν) L)ᵀ =
      ((N⁻¹ : GL (Fin ν) L) : Matrix (Fin ν) (Fin ν) L)ᵀ *
        ((N'⁻¹ : GL (Fin ν) L) : Matrix (Fin ν) (Fin ν) L)ᵀ
    rw [_root_.mul_inv_rev, Units.val_mul, Matrix.transpose_mul]

private noncomputable def stdGL (σ : L ≃+* L) : GL (Fin ν) L →* GL (Fin ν) L :=
  invTransposeGL.comp (Matrix.GeneralLinearGroup.map σ.toRingHom)

private theorem coe_stdGL (σ : L ≃+* L) (N : GL (Fin ν) L) :
    ((stdGL σ N : GL (Fin ν) L) : Matrix (Fin ν) (Fin ν) L) =
      (((N : Matrix (Fin ν) (Fin ν) L).map σ)⁻¹)ᵀ := by
  change ((((Matrix.GeneralLinearGroup.map σ.toRingHom N)⁻¹ : GL (Fin ν) L) :
    Matrix (Fin ν) (Fin ν) L))ᵀ = _
  rw [Matrix.coe_units_inv]
  rfl

private theorem toGL_stdUnitary (σ : L ≃+* L) (A : SL(ν, L)) :
    Matrix.SpecialLinearGroup.toGL (stdUnitary σ.toRingHom A) =
      stdGL σ (Matrix.SpecialLinearGroup.toGL A) := by
  apply Units.ext
  rw [coe_stdGL]
  change ((stdUnitary σ.toRingHom A : SL(ν, L)) : Matrix (Fin ν) (Fin ν) L) = _
  rw [coe_stdUnitary]
  rfl

private theorem toGL_conjSLn (M : GL (Fin ν) L) (A : SL(ν, L)) :
    Matrix.SpecialLinearGroup.toGL (conjSLn M A) =
      M * Matrix.SpecialLinearGroup.toGL A * M⁻¹ := by
  apply Units.ext
  change ((conjSLn M A : SL(ν, L)) : Matrix (Fin ν) (Fin ν) L) = _
  rw [coe_conjSLn, Units.val_mul, Units.val_mul]
  rfl

private theorem stdUnitary_conjSLn (σ : L ≃+* L) (M : GL (Fin ν) L) (A : SL(ν, L)) :
    stdUnitary σ.toRingHom (conjSLn M A) =
      conjSLn (stdGL σ M) (stdUnitary σ.toRingHom A) := by
  apply Matrix.SpecialLinearGroup.toGL_injective
  rw [toGL_stdUnitary, toGL_conjSLn, toGL_conjSLn, map_mul, map_mul, map_inv,
    toGL_stdUnitary]

private theorem stdGL_scalar (σ : L ≃+* L) (μ : Lˣ) :
    stdGL σ (Matrix.GeneralLinearGroup.scalar (Fin ν) μ) =
      Matrix.GeneralLinearGroup.scalar (Fin ν) (Units.map (σ.toRingHom : L →* L) μ)⁻¹ := by
  rw [stdGL, MonoidHom.comp_apply, Matrix.GeneralLinearGroup.map_scalar]
  apply Units.ext
  change (((Matrix.GeneralLinearGroup.scalar (Fin ν) (Units.map (σ.toRingHom : L →* L) μ))⁻¹ :
    GL (Fin ν) L) : Matrix (Fin ν) (Fin ν) L)ᵀ = _
  rw [← map_inv, Matrix.GeneralLinearGroup.coe_scalar]
  simp only [Matrix.scalar_apply, Matrix.diagonal_transpose]

private theorem conjSLn_mem_fix_stdUnitary {σ : L ≃+* L} {G : GL (Fin ν) L}
    (hG : stdGL σ G = G) {X : SL(ν, L)} (hX : stdUnitary σ.toRingHom X = X) :
    stdUnitary σ.toRingHom (conjSLn G X) = conjSLn G X := by
  rw [stdUnitary_conjSLn, hG, hX]

end Aux

section UnitaryFrame

variable {τ : Tag} {L : Type} [Field L] [IsAlgClosed L] {p₀ : ℕ} (S : LangSetup τ L p₀)
  {a : Fin τ.rank → Lˣ}

theorem centerQuotientHom_mem_innAutDerived_unitaryFrame [CharP L 2]
    (hT : rootDiagUnit τ a ∈ S.D.torus) (i : KernelComponent (rootCharHom a)) {ν : ℕ}
    (hν : 3 ≤ ν) {ψ : SL(ν, L) →* ModGL τ L} {σf : Fin ν → Fin ν → Fin τ.rank → ℤ}
    (hψ : IsSLFrame ψ σf) (hΨ : componentRoots (rootCharHom a) i = frameRoots σf)
    (π : Equiv.Perm (Fin ν))
    (hπ : ∀ a' b, a' ≠ b → (S.ρ : (Fin τ.rank → ℤ) → _)^[componentOrbitLength S.ρ
      (componentRoots (rootCharHom a) i)] (σf a' b) = σf (π b) (π a'))
    (h32 : (ν, S.D.q ^ componentOrbitLength S.ρ (componentRoots (rootCharHom a) i)) ≠ (3, 2))
    {y : ModGL τ L}
    (hyZ : y ∈ torusGroup τ L ⊔ rootSpan τ L (kernelRoots (rootCharHom a)))
    (hyF : S.D.step y = y)
    (hy : MulAut.conj y ∈
      CFSG.GroupActions.subgroupStabAut (rationalComponent S.ρ S.Γ (rootCharHom a) i)) :
    centerQuotientHom _ (CFSG.GroupActions.subgroupStabRestrict _ ⟨MulAut.conj y, hy⟩) ∈
      innAutDerived (↥(rationalComponent S.ρ S.Γ (rootCharHom a) i) ⧸
        Subgroup.center ↥(rationalComponent S.ρ S.Γ (rootCharHom a) i)) := by
  classical
  haveI : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hc2 : CharP L 2 := inferInstance
  obtain ⟨σ₂, hσ₂⟩ := exists_ringEquiv_frob (L := L) 2 1
  have hσ₂c : ∀ c, σ₂ c = c ^ 2 := by
    intro c
    have h1 : σ₂ c = iterateFrobenius L 2 1 c := by rw [← hσ₂]; rfl
    rw [h1, iterateFrobenius_def, pow_one]
  obtain ⟨hs0, hs, hmin⟩ := outer_componentOrbitLength_spec S hT i
  haveI : NeZero (componentOrbitLength S.ρ (componentRoots (rootCharHom a) i)) := ⟨hs0.ne'⟩
  set s := componentOrbitLength S.ρ (componentRoots (rootCharHom a) i) with hsdef
  set R := rationalComponent S.ρ S.Γ (rootCharHom a) i with hR
  obtain ⟨r, e, hr, hchar, he, hq⟩ := S.exists_char_pow
  haveI : Fact r.Prime := ⟨hr⟩
  haveI : CharP L r := hchar
  obtain ⟨σQ, z, hσQ, hzZ, hnorm, hconj⟩ :=
    exists_unitary_untwist_kd264alg S hT i hν hψ hΨ π hπ hr hchar he hq
  have hσQc : ∀ c, σQ c = c ^ (r ^ (e * s)) := hσQ
  have hqpow : S.D.q ^ s = r ^ (e * s) := by rw [hq, ← pow_mul]
  have hne : (ν, r ^ (e * s)) ≠ (3, 2) := by
    intro h
    exact h32 (by rw [hqpow]; exact h)
  have hes : 1 ≤ e * s := Nat.succ_le_of_lt (Nat.mul_pos (by omega) hs0)
  obtain ⟨-, hCqs, -⟩ :=
    stdUnitary_fixSubgroup (ν := ν) hr (f := e * s) hes σQ hσQc hν
  set C := fixSubgroup (stdUnitaryEquiv (ν := ν) σQ) with hCdef
  have hCq : CFSG.IsQuasisimple C := hCqs hne
  have hCperf : Group.IsPerfect C := hCq.1
  have hCmem : ∀ X : SL(ν, L), X ∈ C ↔ stdUnitary σQ.toRingHom X = X := fun X => by
    rw [hCdef, mem_fixSubgroup, stdUnitaryEquiv_apply]
  have hψS : ∀ X, ψ X ∈ rootSpan τ L (componentRoots (rootCharHom a) i) := fun X => by
    rw [hΨ, ← hψ.range]
    exact ⟨X, rfl⟩
  have hkerne : ψ.ker ≠ ⊤ := by
    intro h
    have h01 : (⟨0, by omega⟩ : Fin ν) ≠ ⟨1, by omega⟩ := by simp
    obtain ⟨ε, hε⟩ := hψ.transv _ _ h01
    have h1 : Matrix.SpecialLinearGroup.transvection h01 (1 : L) ∈ ψ.ker := by
      rw [h]
      exact Subgroup.mem_top _
    rw [MonoidHom.mem_ker, hε, mul_one, ← pinnedX_zero τ L (σf _ _)] at h1
    exact Units.ne_zero _ (pinnedX_injective τ L _ h1)
  have hSLq : CFSG.IsQuasisimple SL(ν, L) := isQuasisimple_specialLinearGroup hν
  have hker : ψ.ker ≤ Subgroup.center SL(ν, L) := by
    rcases CFSG.LieType.CurtisTits.le_center_or_eq_top_of_isQuasisimple hSLq ψ.ker with h | h
    · exact h
    · exact absurd h hkerne
  set P := outerOrbitFamily S hT i hs hmin with hP
  have hP0 : P.S 0 = rootSpan τ L (componentRoots (rootCharHom a) i) := by
    rw [hP, outerOrbitFamily_S, ZMod.val_zero]
    simp only [Function.iterate_zero, id_eq, Set.image_id']
  have hzA : ∀ u ∈ P.A, z * u * z⁻¹ ∈ P.A := by
    have h : P.A ≤ P.A.comap (MulAut.conj z).toMonoidHom := by
      refine iSup_le fun k => ?_
      obtain ⟨j, hj⟩ := outer_iterate_image_component S hT i k.val
      intro g hg
      have hg' : g ∈ rootSpan τ L (componentRoots (rootCharHom a) j) := by rw [hj]; exact hg
      have h2 := (hnorm j g).1 hg'
      rw [hj] at h2
      exact P.S_le_A k h2
    exact fun u hu => h hu
  have hZconj : ∀ x : ModGL τ L, z * x * z⁻¹ ∈ P.Z → x ∈ P.Z := by
    intro x hx
    rw [CycFamily.mem_Z] at hx ⊢
    intro u hu
    have := hx _ (hzA u hu)
    have e1 : z * u * z⁻¹ * (z * x * z⁻¹) = z * (u * x) * z⁻¹ := by group
    have e2 : z * x * z⁻¹ * (z * u * z⁻¹) = z * (x * u) * z⁻¹ := by group
    rw [e1, e2] at this
    simpa using this
  have hcentral : ∀ X : SL(ν, L), ψ X ∈ P.Z → X ∈ Subgroup.center SL(ν, L) := by
    intro X hX
    refine mem_center_SL_of_commute hν ψ hkerne fun Y => ?_
    have hYA : ψ Y ∈ P.A := P.S_le_A 0 (by rw [hP0]; exact hψS Y)
    exact ((CycFamily.mem_Z P).1 hX (ψ Y) hYA).symm
  let θ : C →* ModGL τ L := (MulAut.conj z).toMonoidHom.comp (ψ.comp C.subtype)
  have hθ : ∀ c : C, θ c = z * ψ ((c : C) : SL(ν, L)) * z⁻¹ := fun c => rfl
  have hθS : ∀ c : C, θ c ∈ rootSpan τ L (componentRoots (rootCharHom a) i) := fun c => by
    rw [hθ]
    exact (hnorm i _).1 (hψS _)
  have hθfix : ∀ c : C, iterHom S.D.step s (θ c) = θ c := fun c => by
    rw [hθ, hconj, (hCmem c).1 c.2]
  have hpre : ∀ g ∈ rootSpan τ L (componentRoots (rootCharHom a) i),
      ∃ X : SL(ν, L), g = z * ψ X * z⁻¹ := by
    intro g hg
    have h1 : z⁻¹ * g * z ∈ rootSpan τ L (componentRoots (rootCharHom a) i) := (hnorm i _).2 (by
      have e : z * (z⁻¹ * g * z) * z⁻¹ = g := by group
      rw [e]
      exact hg)
    rw [hΨ, ← hψ.range] at h1
    obtain ⟨X, hX⟩ := h1
    exact ⟨X, by rw [hX]; group⟩
  have hfixmod : ∀ X : SL(ν, L),
      iterHom S.D.step s (z * ψ X * z⁻¹) * (z * ψ X * z⁻¹)⁻¹ ∈ P.Z →
      stdUnitary σQ.toRingHom X * X⁻¹ ∈ Subgroup.center SL(ν, L) := by
    intro X hX
    have e : iterHom S.D.step s (z * ψ X * z⁻¹) * (z * ψ X * z⁻¹)⁻¹ =
        z * ψ (stdUnitary σQ.toRingHom X * X⁻¹) * z⁻¹ := by
      rw [hconj, map_mul, map_inv]
      group
    rw [e] at hX
    exact hcentral _ (hZconj _ hX)
  have hθY : ∀ g g' : ModGL τ L, g ∈ rootSpan τ L (componentRoots (rootCharHom a) i) →
      g' ∈ rootSpan τ L (componentRoots (rootCharHom a) i) → iterHom S.D.step s g * g⁻¹ ∈ P.Z →
      iterHom S.D.step s g' * g'⁻¹ ∈ P.Z → ⁅g, g'⁆ ∈ θ.range := by
    intro g g' hg hg' hgZ hg'Z
    obtain ⟨X, rfl⟩ := hpre g hg
    obtain ⟨X', rfl⟩ := hpre g' hg'
    have hc := hfixmod X hgZ
    have hc' := hfixmod X' hg'Z
    set c := stdUnitary σQ.toRingHom X * X⁻¹ with hcdef
    set c' := stdUnitary σQ.toRingHom X' * X'⁻¹ with hc'def
    have hX : stdUnitary σQ.toRingHom X = c * X := by rw [hcdef, inv_mul_cancel_right]
    have hX' : stdUnitary σQ.toRingHom X' = c' * X' := by rw [hc'def, inv_mul_cancel_right]
    have hcomm : ∀ (w : SL(ν, L)) (hw : w ∈ Subgroup.center SL(ν, L)) (q : SL(ν, L)),
        Commute w q := fun w hw q => (Subgroup.mem_center_iff.1 hw q).symm
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
    intro d
    exact Subtype.ext (Subgroup.mem_center_iff.1 h (d : SL(ν, L)))
  have huZ : z⁻¹ * y * z ∈ torusGroup τ L ⊔ rootSpan τ L (kernelRoots (rootCharHom a)) :=
    mul_mem (mul_mem (inv_mem hzZ) hyZ) hzZ
  obtain ⟨M, hM⟩ := exists_conj_frame_of_mem_kd264alg i (by omega) hψ hΨ huZ
  have hyA : ∀ A : SL(ν, L), y * (z * ψ A * z⁻¹) * y⁻¹ =
      z * ψ (conjSLn M A) * z⁻¹ := by
    intro A
    rw [← hM A]
    group
  have hMinv : ∀ A : SL(ν, L), ψ (conjSLn M⁻¹ A) =
      (z⁻¹ * y * z)⁻¹ * ψ A * (z⁻¹ * y * z) := by
    intro A
    have h1 := hM (conjSLn M⁻¹ A)
    rw [← conjSLn_mul, mul_inv_cancel, conjSLn_one] at h1
    rw [← h1]
    group
  have hFs : iterHom S.D.step s y = y := iterHom_eq_self_of_fixed hyF s
  have hcomm : ∀ A : SL(ν, L),
      ψ (conjSLn (stdGL σQ M) (stdUnitary σQ.toRingHom A)) =
        ψ (conjSLn M (stdUnitary σQ.toRingHom A)) := by
    intro A
    have e2 : iterHom S.D.step s (y * (z * ψ A * z⁻¹) * y⁻¹) =
        y * iterHom S.D.step s (z * ψ A * z⁻¹) * y⁻¹ := by
      rw [map_mul, map_mul, map_inv, hFs]
    rw [hyA, hconj, hconj, hyA, stdUnitary_conjSLn] at e2
    exact mul_right_cancel (mul_left_cancel e2)
  have hstdsurj : Function.Surjective (stdUnitary (ν := ν) σQ.toRingHom) := fun X =>
    ⟨(stdUnitaryEquiv (ν := ν) σQ).symm X, (stdUnitaryEquiv (ν := ν) σQ).apply_symm_apply X⟩
  set Dm : GL (Fin ν) L := M⁻¹ * stdGL σQ M with hDm
  have hDψ : ∀ B : SL(ν, L), ψ (conjSLn Dm B) = ψ B := by
    intro B
    obtain ⟨A, rfl⟩ := hstdsurj B
    rw [hDm, conjSLn_mul, hMinv, hcomm, ← hM]
    group
  have hperfSL : Group.IsPerfect SL(ν, L) :=
    CFSG.LinearGroups.special_linear_dimension_at_least_three_perfect hν
  haveI := hperfSL
  have hDtriv : ∀ B : SL(ν, L), conjSLn Dm B = B := by
    have hcentralD : ∀ B : SL(ν, L), B⁻¹ * conjSLn Dm B ∈ Subgroup.center SL(ν, L) := by
      intro B
      apply hker
      rw [MonoidHom.mem_ker, map_mul, map_inv, hDψ B, inv_mul_cancel]
    have hid := hom_eq_id_of_central_displacement (conjSLn Dm) hcentralD
    intro B
    have := congrArg (fun f : SL(ν, L) →* SL(ν, L) => f B) hid
    simpa using this
  obtain ⟨c, hc⟩ := exists_scalar_of_commute_conjSLn_kd264alg Dm hDtriv
  have hc0 : c ≠ 0 := by
    rintro rfl
    have h1 := congrArg Matrix.det hc
    haveI : Nonempty (Fin ν) := ⟨⟨0, by omega⟩⟩
    rw [Matrix.scalar_apply, Matrix.diagonal_zero, Matrix.det_zero] at h1
    exact (Matrix.isUnits_det_units _).ne_zero h1
  set u : Lˣ := Units.mk0 c hc0 with hu
  have hMu : stdGL σQ M = M * Matrix.GeneralLinearGroup.scalar (Fin ν) u := by
    have h1 : Dm = Matrix.GeneralLinearGroup.scalar (Fin ν) u := by
      apply Units.ext
      rw [hc, Matrix.GeneralLinearGroup.coe_scalar, hu, Units.val_mk0]
    rw [← h1, hDm, mul_inv_cancel_left]
  have hσqs : ∀ c : L, σQ c = c ^ (S.D.q ^ s) := fun c => by
    rw [hσQc c, hq, ← pow_mul]
  obtain ⟨μ₀, hμ₀⟩ :=
    IsAlgClosed.exists_pow_nat_eq (u : L) (n := S.D.q ^ s + 1) (by omega)
  have hμ0 : μ₀ ≠ 0 := by
    rintro rfl
    rw [zero_pow (by omega)] at hμ₀
    exact u.ne_zero hμ₀.symm
  set μ : Lˣ := Units.mk0 μ₀ hμ0 with hμ
  set G : GL (Fin ν) L := M * Matrix.GeneralLinearGroup.scalar (Fin ν) μ with hG
  have hσμ : Units.map (σQ.toRingHom : L →* L) μ = u * μ⁻¹ := by
    apply Units.ext
    show σQ μ₀ = (u : L) * μ₀⁻¹
    rw [hσqs, ← hμ₀, pow_succ]
    field_simp
  have hGM : ∀ A : SL(ν, L), conjSLn G A = conjSLn M A := fun A => by
    rw [hG, conjSLn_mul_scalar]
  have hGstd : stdGL σQ G = G := by
    rw [hG, map_mul, hMu, stdGL_scalar, hσμ, mul_assoc, ← map_mul, _root_.mul_inv_rev,
      inv_inv, mul_comm μ u⁻¹, ← mul_assoc, mul_inv_cancel, one_mul]
  have hGu : ((G : Matrix (Fin ν) (Fin ν) L).map σQ)ᵀ * G = 1 := by
    have h1 := congrArg (fun g : GL (Fin ν) L => (g : Matrix (Fin ν) (Fin ν) L)) hGstd
    simp only [coe_stdGL] at h1
    have hdet : IsUnit ((G : Matrix (Fin ν) (Fin ν) L).map σQ).det := by
      have h0 : ((G : Matrix (Fin ν) (Fin ν) L).map σQ).det =
          σQ (G : Matrix (Fin ν) (Fin ν) L).det := (RingHom.map_det σQ.toRingHom _).symm
      rw [h0]
      exact (Matrix.isUnits_det_units G).map σQ
    calc ((G : Matrix (Fin ν) (Fin ν) L).map σQ)ᵀ * (G : Matrix (Fin ν) (Fin ν) L) =
        ((G : Matrix (Fin ν) (Fin ν) L).map σQ)ᵀ *
          (((G : Matrix (Fin ν) (Fin ν) L).map σQ)⁻¹)ᵀ := by rw [h1]
      _ = 1 := by
        rw [← Matrix.transpose_mul, Matrix.nonsing_inv_mul _ hdet, Matrix.transpose_one]
  have hGstd_inv : stdGL σQ (G⁻¹) = G⁻¹ := by
    rw [map_inv, hGstd]
  have hGinv : (((G⁻¹ : GL (Fin ν) L) : Matrix (Fin ν) (Fin ν) L).map σQ)ᵀ *
      ((G⁻¹ : GL (Fin ν) L) : Matrix (Fin ν) (Fin ν) L) = 1 := by
    have h1 := congrArg (fun g : GL (Fin ν) L => (g : Matrix (Fin ν) (Fin ν) L)) hGstd_inv
    simp only [coe_stdGL] at h1
    have hdet : IsUnit ((((G⁻¹ : GL (Fin ν) L) : Matrix (Fin ν) (Fin ν) L).map σQ).det) := by
      have h0 : (((G⁻¹ : GL (Fin ν) L) : Matrix (Fin ν) (Fin ν) L).map σQ).det =
          σQ (((G⁻¹ : GL (Fin ν) L) : Matrix (Fin ν) (Fin ν) L).det) :=
        (RingHom.map_det σQ.toRingHom _).symm
      rw [h0]
      exact (Matrix.isUnits_det_units (G⁻¹)).map σQ
    calc (((G⁻¹ : GL (Fin ν) L) : Matrix (Fin ν) (Fin ν) L).map σQ)ᵀ *
          ((G⁻¹ : GL (Fin ν) L) : Matrix (Fin ν) (Fin ν) L) =
        (((G⁻¹ : GL (Fin ν) L) : Matrix (Fin ν) (Fin ν) L).map σQ)ᵀ *
          (((((G⁻¹ : GL (Fin ν) L) : Matrix (Fin ν) (Fin ν) L).map σQ)⁻¹))ᵀ := by rw [h1]
      _ = 1 := by
        rw [← Matrix.transpose_mul, Matrix.nonsing_inv_mul _ hdet, Matrix.transpose_one]
  have hconj_mem : ∀ X : SL(ν, L), X ∈ C → conjSLn G X ∈ C := by
    intro X hX
    rw [hCmem] at hX ⊢
    exact conjSLn_mem_fix_stdUnitary hGstd hX
  have hconj_mem_inv : ∀ X : SL(ν, L), X ∈ C → conjSLn G⁻¹ X ∈ C := by
    intro X hX
    rw [hCmem] at hX ⊢
    exact conjSLn_mem_fix_stdUnitary hGstd_inv hX
  let φ : MulAut C :=
    { toFun := fun X => ⟨conjSLn G (X : SL(ν, L)), hconj_mem (X : SL(ν, L)) X.2⟩
      invFun := fun X => ⟨conjSLn G⁻¹ (X : SL(ν, L)), hconj_mem_inv (X : SL(ν, L)) X.2⟩
      left_inv := fun X => by
        apply Subtype.ext
        change conjSLn G⁻¹ (conjSLn G (X : SL(ν, L))) = (X : SL(ν, L))
        rw [← conjSLn_mul, inv_mul_cancel, conjSLn_one]
      right_inv := fun X => by
        apply Subtype.ext
        change conjSLn G (conjSLn G⁻¹ (X : SL(ν, L))) = (X : SL(ν, L))
        rw [← conjSLn_mul, mul_inv_cancel, conjSLn_one]
      map_mul' := fun X Y =>
        Subtype.ext (map_mul (conjSLn G) (X : SL(ν, L)) (Y : SL(ν, L))) }
  have hφ : ∀ X : C, ((φ X : C) : SL(ν, L)) = conjSLn G (X : SL(ν, L)) := fun X => rfl
  have hσσ₂ : ∀ c, σQ (σ₂ c) = σ₂ (σQ c) := by
    intro c
    rw [hσqs, hσ₂c, hσqs, hσ₂c, ← pow_mul, ← pow_mul, mul_comm]
  have hφinn : φ ∈ innAutDerived C := by
    haveI := hc2
    exact mem_innAutDerived_of_unitary_conj_kd264alg (ν := ν) (by omega) σQ σ₂ hσ₂c hσσ₂
      G hGu φ hφ
  have hθφ : ∀ c : C, θ (φ c) = y * θ c * y⁻¹ := by
    intro c
    change z * ψ ((φ c : C) : SL(ν, L)) * z⁻¹ =
      y * (z * ψ ((c : C) : SL(ν, L)) * z⁻¹) * y⁻¹
    rw [hφ, hGM]
    exact (hyA ((c : C) : SL(ν, L))).symm
  exact centerQuotientHom_subgroupStabRestrict_mem_innAutDerived_of_norm S hT i hs hmin θ
    hθS hθfix hθY hθZ hCperf hyZ hyF hy φ hφinn hθφ

end UnitaryFrame

end CFSG.LocalAnalysis.GLTheoremA.T171Sh

end
