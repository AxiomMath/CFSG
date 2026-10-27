module

public import CFSG.HardMathSupport.Solomon.Coordinator.LieSemisimple.LinearBlocks
public import CFSG.HardMathSupport.Timmesfeld.CrossChar.NonsplitGen
public import CFSG.RankThree.PartOne.KC.UnitaryRigidityScalar

public section

namespace CFSG.HardMathSupport.Solomon.Coordinator.LieSemisimple

open Polynomial CFSG.RankThree.PartOne.KCPrimary CFSG.RankThree.PartOne.KCUnitary
  CFSG.RankThree.PartOne.KCUnitaryScalar CFSG.RankThree.CALinearPrimary
open scoped Matrix

theorem eq_X_sub_C_of_mem_primaryFactors_of_pow_eq_one
    {n : ℕ} {K : Type} [Field K] {p : ℕ} (hp0 : p ≠ 0) {ω : K}
    (hω : IsPrimitiveRoot ω p) {D : GL (Fin n) K} (hD : D ^ p = 1) {f : K[X]}
    (hf : f ∈ primaryFactors (glA D : Module.End K (Fin n → K))) :
    ∃ ε : K, f = X - C ε ∧ ε ^ p = 1 ∧ ε ≠ 0 := by
  have hglA : ((glA D : LinearMap.GeneralLinearGroup K (Fin n → K)) :
      Module.End K (Fin n → K)) = Matrix.toLin' (D : Matrix (Fin n) (Fin n) K) := rfl
  obtain ⟨ε, hε⟩ :=
    CFSG.HardMathSupport.Timmesfeld.CrossChar.exists_eq_X_sub_C_of_mem_primaryFactors
      (F := K) (n := n) hp0 hω hD (hglA ▸ hf)
  have hann : aeval (glA D : Module.End K (Fin n → K)) ((X : K[X]) ^ p - 1) = 0 := by
    have hp : (glA D : LinearMap.GeneralLinearGroup K (Fin n → K)) ^ p = 1 := by
      rw [← map_pow, hD, map_one]
    have hp' : ((glA D : LinearMap.GeneralLinearGroup K (Fin n → K)) :
        Module.End K (Fin n → K)) ^ p = 1 := by
      rw [← Units.val_pow_eq_pow_val, hp]
      rfl
    rw [map_sub, map_pow, aeval_X, map_one]
    exact sub_eq_zero.mpr hp'
  have hdvd : f ∣ (X : K[X]) ^ p - 1 :=
    (mem_primaryFactors.mp hf).2.2.trans (minpoly.dvd K _ hann)
  rw [hε] at hdvd
  have hroot : ((X : K[X]) ^ p - 1).IsRoot ε := dvd_iff_isRoot.mp hdvd
  have hεp : ε ^ p = 1 := by
    simpa [Polynomial.IsRoot, sub_eq_zero] using hroot
  have hε0 : ε ≠ 0 := by
    intro h0
    rw [h0, zero_pow hp0] at hεp
    exact zero_ne_one hεp
  exact ⟨ε, hε, hεp, hε0⟩

theorem glA_apply_eq_smul_of_conj_eq_scalar_mul
    {n : ℕ} {K : Type} [Field K] {D Mb : GL (Fin n) K} {ζ : Kˣ}
    (hconj : Mb * D * Mb⁻¹ = Matrix.GeneralLinearGroup.scalar (Fin n) ζ * D) :
    ∀ w : Fin n → K,
      (glA Mb : Module.End K (Fin n → K)) ((glA D : Module.End K (Fin n → K)) w) =
        (ζ : K) • (glA D : Module.End K (Fin n → K))
          ((glA Mb : Module.End K (Fin n → K)) w) := by
  have hglA_scalar : (glA (Matrix.GeneralLinearGroup.scalar (Fin n) ζ) :
      Module.End K (Fin n → K)) = (ζ : K) • 1 := by
    ext v i
    simp [glA, Matrix.GeneralLinearGroup.toLin, Matrix.toLin'_apply,
      Matrix.GeneralLinearGroup.coe_scalar, Matrix.scalar_apply, Matrix.mulVec_diagonal]
  let DlinG : LinearMap.GeneralLinearGroup K (Fin n → K) := glA D
  let MblinG : LinearMap.GeneralLinearGroup K (Fin n → K) := glA Mb
  let MbinvG : LinearMap.GeneralLinearGroup K (Fin n → K) := MblinG⁻¹
  let Dlin : Module.End K (Fin n → K) := (DlinG : Module.End K (Fin n → K))
  let Mblin : Module.End K (Fin n → K) := (MblinG : Module.End K (Fin n → K))
  let Mbinv : Module.End K (Fin n → K) := (MbinvG : Module.End K (Fin n → K))
  have hg : (Matrix.GeneralLinearGroup.toLin (Mb * D * Mb⁻¹) :
        LinearMap.GeneralLinearGroup K (Fin n → K)) =
      Matrix.GeneralLinearGroup.toLin
        (Matrix.GeneralLinearGroup.scalar (Fin n) ζ * D) := by
    rw [hconj]
  have hg' : MblinG * DlinG * MbinvG =
      (glA (Matrix.GeneralLinearGroup.scalar (Fin n) ζ) :
        LinearMap.GeneralLinearGroup K (Fin n → K)) * DlinG := by
    simpa [MblinG, DlinG, MbinvG, glA, map_mul] using hg
  have hlinconj : Mblin * Dlin * Mbinv = (ζ : K) • Dlin := by
    have h := congrArg (fun g : LinearMap.GeneralLinearGroup K (Fin n → K) =>
      (g : Module.End K (Fin n → K))) hg'
    simp only [Units.val_mul] at h
    rw [hglA_scalar] at h
    simpa [Mblin, Dlin, Mbinv, MblinG, DlinG, MbinvG, mul_smul] using h
  intro w
  have hbinv : Mbinv (Mblin w) = w := by
    show ((MbinvG : Module.End K (Fin n → K))) ((MblinG : Module.End K (Fin n → K)) w) = w
    rw [← Module.End.mul_apply, ← Units.val_mul, inv_mul_cancel, Units.val_one,
      Module.End.one_apply]
  have h := congrArg (fun T : Module.End K (Fin n → K) => T (Mblin w)) hlinconj
  have h' : Mblin (Dlin w) = (ζ : K) • Dlin (Mblin w) := by
    simpa [Module.End.mul_apply, Mbinv, MbinvG, hbinv] using h
  simpa only [Mblin, Dlin, MblinG, DlinG] using h'

theorem map_primaryComponent_X_sub_C_of_conj_eq_scalar_mul
    {n : ℕ} {K : Type} [Field K] {D Mb : GL (Fin n) K} {ζ : Kˣ} {f : K[X]} {ε : K}
    (hconj : Mb * D * Mb⁻¹ = Matrix.GeneralLinearGroup.scalar (Fin n) ζ * D)
    (hform : f = X - C ε) :
    (primaryComponent (glA D : Module.End K (Fin n → K)) f).map
        (glA Mb : Module.End K (Fin n → K)) =
      primaryComponent (glA D : Module.End K (Fin n → K)) (X - C (ε / ζ)) := by
  let MblinG : LinearMap.GeneralLinearGroup K (Fin n → K) := glA Mb
  let MbinvG : LinearMap.GeneralLinearGroup K (Fin n → K) := MblinG⁻¹
  let Dlin : Module.End K (Fin n → K) := (glA D : Module.End K (Fin n → K))
  let Mblin : Module.End K (Fin n → K) := (MblinG : Module.End K (Fin n → K))
  let Mbinv : Module.End K (Fin n → K) := (MbinvG : Module.End K (Fin n → K))
  have hMinj : Function.Injective (glA Mb : Module.End K (Fin n → K)) := by
    simpa using (LinearMap.GeneralLinearGroup.toLinearEquiv (glA Mb)).injective
  have hMDv : ∀ w : Fin n → K, Mblin (Dlin w) = (ζ : K) • Dlin (Mblin w) := by
    intro w
    simpa only [Mblin, Dlin, MblinG] using
      glA_apply_eq_smul_of_conj_eq_scalar_mul (D := D) (Mb := Mb) (ζ := ζ) hconj w
  have hbinvR : ∀ w : Fin n → K, Mblin (Mbinv w) = w := by
    intro w
    show ((MblinG : Module.End K (Fin n → K))) ((MbinvG : Module.End K (Fin n → K)) w) = w
    rw [← Module.End.mul_apply, ← Units.val_mul, mul_inv_cancel, Units.val_one,
      Module.End.one_apply]
  let g : K[X] := X - C (ε / ζ)
  have hMV : (primaryComponent (glA D : Module.End K (Fin n → K)) f).map Mblin =
      primaryComponent (glA D : Module.End K (Fin n → K)) g := by
    ext w
    constructor
    · rintro ⟨v, hv, rfl⟩
      have hv' : Dlin v = ε • v := by
        rw [hform] at hv
        exact (CFSG.RankThree.PartOne.KCUnitaryScalar.mem_primaryComponent_X_sub_C).mp hv
      have h := hMDv v
      rw [hv', map_smul] at h
      have hζ0 : (ζ : K) ≠ 0 := ζ.ne_zero
      have h2 := congrArg (fun x : Fin n → K => (ζ : K)⁻¹ • x) h
      simp only [smul_smul, inv_mul_cancel₀ hζ0, one_smul] at h2
      dsimp only [g]
      refine (CFSG.RankThree.PartOne.KCUnitaryScalar.mem_primaryComponent_X_sub_C).mpr ?_
      rw [div_eq_mul_inv, mul_comm]
      exact h2.symm
    · intro hw
      have hw' : Dlin w = (ε / ζ) • w := by
        dsimp only [g] at hw
        exact (CFSG.RankThree.PartOne.KCUnitaryScalar.mem_primaryComponent_X_sub_C).mp hw
      refine ⟨Mbinv w, ?_, hbinvR w⟩
      rw [hform]
      refine (CFSG.RankThree.PartOne.KCUnitaryScalar.mem_primaryComponent_X_sub_C).mpr ?_
      apply hMinj
      rw [hMDv (Mbinv w), hbinvR, hw', map_smul, hbinvR]
      rw [smul_smul]
      have hζdiv : (ζ : K) * (ε / ζ) = ε := by field_simp
      rw [hζdiv]
  simpa only [Mblin, MblinG] using hMV

theorem mem_primaryFactors_X_sub_C_div_and_ne_of_map_primaryComponent
    {n : ℕ} {K : Type} [Field K] {D Mb : GL (Fin n) K} {ζ : Kˣ} {f : K[X]} {ε : K}
    (hform : f = X - C ε) (hζ1 : ζ ≠ 1) (hε0 : ε ≠ 0)
    (hVne : primaryComponent (glA D : Module.End K (Fin n → K)) f ≠ ⊥)
    (hMV : (primaryComponent (glA D : Module.End K (Fin n → K)) f).map
        (glA Mb : Module.End K (Fin n → K)) =
      primaryComponent (glA D : Module.End K (Fin n → K)) (X - C (ε / ζ))) :
    (X - C (ε / ζ)) ∈ primaryFactors (glA D : Module.End K (Fin n → K)) ∧
      X - C (ε / ζ) ≠ f := by
  have hMinj : Function.Injective (glA Mb : Module.End K (Fin n → K)) := by
    simpa using (LinearMap.GeneralLinearGroup.toLinearEquiv (glA Mb)).injective
  have hgne : Module.End.eigenspace (glA D : Module.End K (Fin n → K)) (ε / ζ) ≠ ⊥ := by
    obtain ⟨v, hv, hvne⟩ := Submodule.exists_mem_ne_zero_of_ne_bot hVne
    refine Submodule.ne_bot_iff _ |>.mpr ⟨(glA Mb : Module.End K (Fin n → K)) v, ?_, ?_⟩
    · have hmem : (glA Mb : Module.End K (Fin n → K)) v ∈
          (primaryComponent (glA D : Module.End K (Fin n → K)) f).map
            (glA Mb : Module.End K (Fin n → K)) :=
        Submodule.mem_map.mpr ⟨v, hv, rfl⟩
      rw [hMV] at hmem
      have heig : primaryComponent (glA D : Module.End K (Fin n → K)) (X - C (ε / ζ)) =
          Module.End.eigenspace (glA D : Module.End K (Fin n → K)) (ε / ζ) := by
        ext v
        rw [CFSG.RankThree.PartOne.KCUnitaryScalar.mem_primaryComponent_X_sub_C,
          Module.End.mem_eigenspace_iff]
      rwa [heig] at hmem
    · intro h0
      exact hvne (hMinj (by simpa using h0))
  refine ⟨CFSG.RankThree.PartOne.KCUnitaryScalar.X_sub_C_mem_primaryFactors
    (Module.End.hasEigenvalue_iff.mpr hgne), ?_⟩
  intro h
  rw [hform] at h
  have h1 : ε / ζ = ε := by
    have h := congrArg (fun p : K[X] => p.coeff 0) h
    simpa using h
  have h2 : ε = ε * (ζ : K) := (div_eq_iff ζ.ne_zero).mp h1
  have h3 : (ζ : K) = 1 := by
    exact (mul_left_cancel₀ hε0 (by rw [mul_one]; exact h2)).symm
  exact hζ1 (Units.ext h3)

theorem mem_center_specialFactor_of_isScalar_on_primaryComponent
    {n : ℕ} {K : Type} [Field K] {D : GL (Fin n) K}
    (hsq : Squarefree (minpoly K (glA D : Module.End K (Fin n → K)))) {f : K[X]}
    (x : ↥(specialFactor D f))
    (hx : ∃ μ : K, ∀ v ∈ primaryComponent (glA D : Module.End K (Fin n → K)) f,
      (slGL n K (x : Matrix.SpecialLinearGroup (Fin n) K) : Module.End K (Fin n → K)) v =
        μ • v) :
    x ∈ Subgroup.center ↥(specialFactor D f) := by
  obtain ⟨μ, hμ⟩ := hx
  have hfix : ∀ a ∈ specialFactor D f, ∀ {j : K[X]},
      j ∈ primaryFactors (glA D : Module.End K (Fin n → K)) → j ≠ f →
      ∀ v ∈ primaryComponent (glA D : Module.End K (Fin n → K)) j,
        (slGL n K a : Module.End K (Fin n → K)) v = v := by
    intro a ha j hj hjf v hv
    exact (mem_linearSpecialBlock.mp (ha : slGL n K a ∈ linearSpecialBlock (glA D) f)).2.1
      j hj hjf v hv
  rw [Subgroup.mem_center_iff]
  intro y
  apply Subtype.ext
  apply slGL_injective
  rw [Subgroup.coe_mul, Subgroup.coe_mul, map_mul, map_mul]
  apply Units.ext
  rw [Units.val_mul, Units.val_mul]
  apply ext_primaryComponent hsq
  intro j hj v hv
  by_cases hje : j = f
  · rw [hje] at hv
    have hyL : slGL n K (y : Matrix.SpecialLinearGroup (Fin n) K) ∈
        linearSpecialBlock (glA D) f := y.2
    have hyc : Commute ((slGL n K (y : Matrix.SpecialLinearGroup (Fin n) K) :
        Module.End K (Fin n → K))) (glA D : Module.End K (Fin n → K)) :=
      (mem_gl_centralizer (x := (glA D))).mp (mem_linearSpecialBlock.mp hyL).1
    have hyv : (slGL n K (y : Matrix.SpecialLinearGroup (Fin n) K) :
        Module.End K (Fin n → K)) v ∈ primaryComponent (glA D : Module.End K (Fin n → K)) f :=
      apply_mem_primaryComponent hyc hv
    simp only [Module.End.mul_apply]
    rw [hμ _ hyv, hμ _ hv, map_smul]
  · have hxf := hfix (x : Matrix.SpecialLinearGroup (Fin n) K) x.2 hj hje v hv
    have hyf := hfix (y : Matrix.SpecialLinearGroup (Fin n) K) y.2 hj hje v hv
    simp only [Module.End.mul_apply]
    rw [hyf, hxf]
    exact hyf

theorem exists_not_mem_center_specialFactor
    {n : ℕ} {K : Type} [Field K] [Finite K] {D : GL (Fin n) K}
    (hsq : Squarefree (minpoly K (glA D : Module.End K (Fin n → K)))) {f : K[X]}
    (hf : f ∈ primaryFactors (glA D : Module.End K (Fin n → K)))
    (hgood : IsGoodFactor D f) :
    ∃ x : ↥(specialFactor D f), x ∉ Subgroup.center ↥(specialFactor D f) := by
  have hq := isQuasisimple_specialFactor (A := D) hsq hf hgood
  obtain ⟨a, b, hab⟩ := hq.2.2
  obtain ⟨x, rfl⟩ := QuotientGroup.mk'_surjective (Subgroup.center ↥(specialFactor D f)) a
  obtain ⟨y, rfl⟩ := QuotientGroup.mk'_surjective (Subgroup.center ↥(specialFactor D f)) b
  refine ⟨x, fun hx => hab ?_⟩
  have hxy : x * y = y * x := (Subgroup.mem_center_iff.mp hx y).symm
  rw [← map_mul, ← map_mul, hxy]

end CFSG.HardMathSupport.Solomon.Coordinator.LieSemisimple

end
