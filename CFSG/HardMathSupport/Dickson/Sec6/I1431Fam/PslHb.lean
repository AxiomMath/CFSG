module

public import CFSG.RankThree.SteinbergR3ECALinearPrimaryBlocks

public section

namespace CFSG.HardMathSupport.Dickson.Sec6.I1431

open Polynomial Module CFSG.RankThree.PartOne.KCPrimary CFSG.RankThree.PartOne.KCUnitary
  CFSG.RankThree.CALinearPrimary

section Scalar

variable {E V : Type*} [Field E] [AddCommGroup V] [Module E V]

theorem det_smulOfUnit [Module.Free E V] (d : Eˣ) :
    LinearEquiv.det (LinearEquiv.smulOfUnit d : V ≃ₗ[E] V) = d ^ Module.finrank E V := by
  apply Units.ext
  rw [LinearEquiv.coe_det, Units.val_pow_eq_pow_val]
  have : ((LinearEquiv.smulOfUnit d : V ≃ₗ[E] V) : V →ₗ[E] V) = (d : E) • LinearMap.id :=
    LinearMap.ext fun v => rfl
  rw [this, LinearMap.det_smul, LinearMap.det_id, mul_one]

theorem smulOfUnit_comm (d : Eˣ) (f : V ≃ₗ[E] V) :
    (LinearEquiv.smulOfUnit d : V ≃ₗ[E] V) * f = f * (LinearEquiv.smulOfUnit d : V ≃ₗ[E] V) := by
  ext v
  show (d : E) • f v = f ((d : E) • v)
  rw [map_smul]

theorem det_smul_mul_of_cube [Module.Free E V] (hfin : Module.finrank E V = 2) (γ : V ≃ₗ[E] V)
    (h3 : LinearEquiv.det γ ^ 3 = 1) :
    LinearEquiv.det ((LinearEquiv.smulOfUnit (LinearEquiv.det γ) : V ≃ₗ[E] V) * γ) = 1 := by
  rw [map_mul, det_smulOfUnit, hfin, ← pow_succ, h3]

end Scalar

section Split

variable {K : Type*} [Field K] {V : Type*} [AddCommGroup V] [Module K V] [FiniteDimensional K V]
  {x : LinearMap.GeneralLinearGroup K V}

theorem blockGL_ext {X : Module.End K V} {b : K[X]} {γ₁ γ₂ : blockGL X b}
    (h : ∀ v (hv : v ∈ primaryComponent X b), blockApply γ₁ v hv = blockApply γ₂ v hv) :
    γ₁ = γ₂ := by
  apply Units.ext
  apply LinearMap.ext
  intro v
  apply Subtype.ext
  exact h v v.2

theorem exists_block_split (hsq : Squarefree (minpoly K (x : Module.End K V))) {h : K[X]}
    (hh : h ∈ primaryFactors (x : Module.End K V))
    (hm2 : primaryMultiplicity (x : Module.End K V) h = 2)
    {g : LinearMap.GeneralLinearGroup K V} (hg : g ∈ gl_centralizer x) (hg3 : g ^ 3 = 1) :
    ∃ s ∈ linearSpecialBlock x h, ∃ c ∈ gl_centralizer x,
      (∀ m ∈ linearSpecialBlock x h, c * m = m * c) ∧ g = s * c := by
  classical
  haveI : Fact (Irreducible h) := ⟨irreducible_of_mem_primaryFactors hh⟩
  let Γ := glCentralizerEquivPi hsq
  let hb : primaryFactors (x : Module.End K V) := ⟨h, hh⟩
  let g0 : gl_centralizer x := ⟨g, hg⟩
  let eq := LinearMap.GeneralLinearGroup.generalLinearEquiv (AdjoinRoot h)
    (primaryComponent (x : Module.End K V) h)
  let γ : blockGL (x : Module.End K V) h := Γ g0 hb
  let ge : primaryComponent (x : Module.End K V) h ≃ₗ[AdjoinRoot h]
      primaryComponent (x : Module.End K V) h := eq γ
  have hγ3 : ge ^ 3 = 1 := by
    have h0 : g0 ^ 3 = 1 := Subtype.ext hg3
    have h1 : (Γ g0) ^ 3 = 1 := by rw [← map_pow, h0, map_one]
    have h2 : γ ^ 3 = 1 := congrFun h1 hb
    rw [← map_pow, h2, map_one]
  have hd3 : LinearEquiv.det ge ^ 3 = 1 := by rw [← map_pow, hγ3, map_one]
  let u0 := (LinearEquiv.smulOfUnit (LinearEquiv.det ge) :
    primaryComponent (x : Module.End K V) h ≃ₗ[AdjoinRoot h]
      primaryComponent (x : Module.End K V) h) * ge
  have hdet : LinearEquiv.det u0 = 1 := det_smul_mul_of_cube hm2 ge hd3
  let u : _root_.SpecialLinearGroup (AdjoinRoot h) (primaryComponent (x : Module.End K V) h) :=
    ⟨u0, hdet⟩
  obtain ⟨s, hs⟩ := linearSpecialBlockRestrict_surjective hsq hh u
  have hsv : ∀ v (hv : v ∈ primaryComponent (x : Module.End K V) h),
      ((s.1 : LinearMap.GeneralLinearGroup K V) : Module.End K V) v =
        ((u0 ⟨v, hv⟩ : primaryComponent (x : Module.End K V) h) : V) := by
    intro v hv
    rw [← coe_linearSpecialBlockRestrict s ⟨v, hv⟩, hs]
  let s0 : gl_centralizer x := ⟨s.1, s.2.1⟩
  have hΓs : Γ s0 hb = eq.symm u0 := by
    apply blockGL_ext
    intro v hv
    rw [blockApply_glCentralizerEquivPi hsq s0 hb v hv]
    exact hsv v hv
  have hoff : ∀ (m : LinearMap.GeneralLinearGroup K V) (hm : m ∈ linearSpecialBlock x h)
      (b : primaryFactors (x : Module.End K V)), (b : K[X]) ≠ h → Γ ⟨m, hm.1⟩ b = 1 := by
    intro m hm b hbh
    apply blockGL_ext
    intro v hv
    rw [blockApply_glCentralizerEquivPi hsq ⟨m, hm.1⟩ b v hv, blockApply_one]
    exact hm.2.1 b b.2 hbh v hv
  have hu : u0⁻¹ * ge = (LinearEquiv.smulOfUnit (LinearEquiv.det ge) :
      primaryComponent (x : Module.End K V) h ≃ₗ[AdjoinRoot h]
        primaryComponent (x : Module.End K V) h)⁻¹ := by
    have hc : Commute (LinearEquiv.smulOfUnit (LinearEquiv.det ge) :
        primaryComponent (x : Module.End K V) h ≃ₗ[AdjoinRoot h]
          primaryComponent (x : Module.End K V) h) ge := smulOfUnit_comm _ _
    simp only [u0, mul_inv_rev]
    rw [mul_assoc, (hc.inv_left).eq, inv_mul_cancel_left]
  refine ⟨s.1, s.2, (s0⁻¹ * g0).1, (s0⁻¹ * g0).2, ?_, (mul_inv_cancel_left s.1 g).symm⟩
  intro m hm
  have hm0 : m ∈ gl_centralizer x := hm.1
  have key : (s0⁻¹ * g0) * (⟨m, hm0⟩ : gl_centralizer x) =
      (⟨m, hm0⟩ : gl_centralizer x) * (s0⁻¹ * g0) := by
    apply Γ.injective
    funext b
    simp only [map_mul, map_inv, Pi.mul_apply, Pi.inv_apply]
    by_cases hbh : (b : K[X]) = h
    · have hbb : b = hb := Subtype.ext hbh
      subst hbb
      apply eq.injective
      simp only [map_mul, map_inv]
      rw [hΓs, MulEquiv.apply_symm_apply]
      show u0⁻¹ * ge * eq (Γ ⟨m, hm0⟩ hb) = eq (Γ ⟨m, hm0⟩ hb) * (u0⁻¹ * ge)
      rw [hu]
      exact (Commute.inv_left (smulOfUnit_comm (LinearEquiv.det ge) (eq (Γ ⟨m, hm0⟩ hb)))).eq
    · rw [hoff m hm b hbh, mul_one, one_mul]
  exact congrArg Subtype.val key

end Split

end CFSG.HardMathSupport.Dickson.Sec6.I1431
