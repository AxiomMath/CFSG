module

public import CFSG.HardMathSupport.Dickson.Sec6.I1431Fam.PslHb
public import CFSG.Assembly.ComponentTypeDefs
public import CFSG.LocalAnalysis.AGLEmbeddingD2.Ambient

public section

namespace CFSG.HardMathSupport.Dickson.Sec6.I1431

open Polynomial Module CFSG.RankThree.PartOne.KCPrimary CFSG.RankThree.PartOne.KCUnitary
  CFSG.RankThree.CALinearPrimary

section Split

variable {K : Type*} [Field K] {V : Type*} [AddCommGroup V] [Module K V] [FiniteDimensional K V]
  {x : LinearMap.GeneralLinearGroup K V}

theorem exists_block_split_scalar (hsq : Squarefree (minpoly K (x : Module.End K V))) {h : K[X]}
    (hh : h ∈ primaryFactors (x : Module.End K V))
    (hm2 : primaryMultiplicity (x : Module.End K V) h = 2)
    {g : LinearMap.GeneralLinearGroup K V} (hg : g ∈ gl_centralizer x) {ν : Kˣ}
    (hg3 : ∀ v, ((g ^ 3 : LinearMap.GeneralLinearGroup K V) : Module.End K V) v = (ν : K) • v) :
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
  let ν' : (AdjoinRoot h)ˣ := Units.map (algebraMap K (AdjoinRoot h)).toMonoidHom ν
  have hγ3 : γ ^ 3 = Γ (g0 ^ 3) hb := by
    have : (Γ g0) ^ 3 = Γ (g0 ^ 3) := (map_pow Γ g0 3).symm
    exact congrFun this hb
  have hge3 : ge ^ 3 = LinearEquiv.smulOfUnit ν' := by
    have h1 : ge ^ 3 = eq (γ ^ 3) := (map_pow eq γ 3).symm
    rw [h1]
    ext w
    have h2 : (((eq (γ ^ 3)) w : primaryComponent (x : Module.End K V) h) : V) =
        blockApply (Γ (g0 ^ 3) hb) (w : V) w.2 := by rw [hγ3]; rfl
    rw [h2]
    have h3 : blockApply (Γ (g0 ^ 3) hb) (w : V) w.2 =
        (((g0 ^ 3 : gl_centralizer x) : LinearMap.GeneralLinearGroup K V) :
          Module.End K V) (w : V) :=
      blockApply_glCentralizerEquivPi hsq (g0 ^ 3) hb (w : V) w.2
    rw [h3]
    have h4 : ((g0 ^ 3 : gl_centralizer x) : LinearMap.GeneralLinearGroup K V) = g ^ 3 := rfl
    rw [h4, hg3 (w : V)]
    show (ν : K) • (w : V) = (((ν' : AdjoinRoot h) • w : primaryComponent (x : Module.End K V) h) : V)
    exact (coe_algebraMap_smul_primaryComponent (x : Module.End K V) h (ν : K) w).symm
  have hm2' : Module.finrank (AdjoinRoot h) (primaryComponent (x : Module.End K V) h) = 2 := hm2
  have hdet3 : LinearEquiv.det ge ^ 3 = ν' ^ 2 := by
    rw [← map_pow, hge3, det_smulOfUnit, hm2']
  let D : (AdjoinRoot h)ˣ := LinearEquiv.det ge
  let d : (AdjoinRoot h)ˣ := ν' * D⁻¹
  have hd2 : d ^ 2 = D := by
    have h1 : D ^ 3 = ν' ^ 2 := hdet3
    calc d ^ 2 = ν' ^ 2 * (D⁻¹) ^ 2 := by simp only [d, mul_pow]
      _ = D ^ 3 * (D⁻¹) ^ 2 := by rw [h1]
      _ = D := by group
  let S : primaryComponent (x : Module.End K V) h ≃ₗ[AdjoinRoot h]
      primaryComponent (x : Module.End K V) h := LinearEquiv.smulOfUnit d⁻¹
  let u0 := S * ge
  have hdet : LinearEquiv.det u0 = 1 := by
    show LinearEquiv.det (S * ge) = 1
    rw [map_mul, det_smulOfUnit, hm2']
    change (d⁻¹) ^ 2 * D = 1
    rw [inv_pow, hd2, inv_mul_cancel]
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
  have hu : u0⁻¹ * ge = S⁻¹ := by
    have hc : Commute S ge := smulOfUnit_comm _ _
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
      exact (Commute.inv_left (smulOfUnit_comm d⁻¹ (eq (Γ ⟨m, hm0⟩ hb)))).eq
    · rw [hoff m hm b hbh, mul_one, one_mul]
  exact congrArg Subtype.val key

end Split

end CFSG.HardMathSupport.Dickson.Sec6.I1431
