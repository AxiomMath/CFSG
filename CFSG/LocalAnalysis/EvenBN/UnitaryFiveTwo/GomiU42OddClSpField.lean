module

public import CFSG.Assembly.RankThreeEvenDefs
public import CFSG.LocalAnalysis.ComponentClassification.CatalogueBSymplecticBDescentForm
public import CFSG.LocalAnalysis.EvenSporadicStandard.Induction.Fi.Prelim

public section

namespace CFSG.LocalAnalysis.EvenBN.UnitaryFiveTwo

open Subgroup CFSG CFSG.Assembly.LowTwoRank
open CFSG.ComponentClassification
open CFSG.ComponentClassification.CatalogueBSymplecticB CFSG.ComponentClassification.CatalogueBAlternatingIsometry
open CFSG.ComponentClassification.CatalogueBLinearTwoDescent
open CFSG.ComponentClassification.CatalogueBOrthogonalDescent
open LinearMap (BilinForm)

section NegIsometry

variable {K : Type} [Field K] [Finite K] {V : Type} [AddCommGroup V] [Module K V]
  [Module.Finite K V]

theorem exists_isometry_conj_eq_neg (B : BilinForm K V) (hB : B.IsAlt) (hBnd : B.Nondegenerate)
    (sigma : K ≃+* K) (hsigma : sigma ^ 2 = 1) (hne : sigma ≠ 1) (h2 : (2 : K) ≠ 0)
    (tau0 : V ≃+ V) (mu lambda b c : Kˣ) (hsemi : ∀ a x, tau0 (a • x) = sigma a • tau0 x)
    (hform : ∀ x y, B (tau0 x) (tau0 y) = (mu : K) * sigma (B x y))
    (hsquare : ∀ x, tau0 (tau0 x) = (lambda : K) • x)
    (hb : (b : K) * sigma (b : K) = (lambda : K)⁻¹)
    (hc : sigma (c : K) / (c : K) = (b : K) ^ 2 * (mu : K)) :
    ∃ g : isometryGroup B,
      semilinearConjugation B sigma tau0 mu hsemi hform g = g * negIsometry B := by
  classical
  set T := normalizedOperator tau0 b with hTdef
  have hs := normalizedOperator_semilinear sigma tau0 b hsemi
  have hf := normalized_form_identity sigma B tau0 mu b c hform hc
  have hT := normalizedOperator_involutive sigma tau0 lambda b hsemi hsquare hb
  haveI hWfin : Module.Finite (fixedSubfield K sigma) (fixedSubspace sigma T hs) := by
    obtain ⟨e, d', hd'⟩ := exists_fixedSpace_basis sigma hsigma hne h2 T hT hs
    exact Module.Finite.of_basis d'
  set B0 := descendedBilinear sigma T hs B c hf with hB0def
  have hB0 : B0.IsAlt := descendedBilinear_isAlt sigma T hs B c hf hB
  have hnd0 : B0.Nondegenerate :=
    descendedBilinear_nondegenerate_of_isAlt sigma T hs B c hf hsigma hne h2 hT hB hBnd
  obtain ⟨m, bs, -, hll, hrr, -⟩ := exists_blueprint_symplectic_basis B0 hB0 hnd0
  obtain ⟨x0, hx0⟩ : ∃ x0, sigma x0 ≠ x0 := by
    by_contra hcon
    push Not at hcon
    exact hne (RingEquiv.ext hcon)
  have hσσ : ∀ x, sigma (sigma x) = x := fun x => by
    have := congrArg (fun s : K ≃+* K => s x) hsigma
    simpa [pow_two] using this
  set ι : K := x0 - sigma x0 with hι
  have hσι : sigma ι = -ι := by
    rw [hι, map_sub, hσσ]; ring
  have hι0 : ι ≠ 0 := by
    intro h0
    exact hx0 (sub_eq_zero.mp h0).symm
  have hι2 : sigma ((ι ^ 2)⁻¹) = (ι ^ 2)⁻¹ := by
    rw [map_inv₀, map_pow, hσι]; ring
  let ν : fixedSubfield K sigma := ⟨(ι ^ 2)⁻¹, (mem_fixedSubfield K sigma _).mpr hι2⟩
  have hν0 : ν ≠ 0 := by
    intro h0
    have := congrArg (fun a : fixedSubfield K sigma => (a : K)) h0
    exact inv_ne_zero (pow_ne_zero 2 hι0) this
  let νu : (fixedSubfield K sigma)ˣ := Units.mk0 ν hν0
  let w : Fin m ⊕ Fin m → (fixedSubfield K sigma)ˣ := Sum.elim (fun _ => 1) (fun _ => νu)
  let bs' := bs.unitsSMul w
  let h : fixedSubspace sigma T hs ≃ₗ[fixedSubfield K sigma] fixedSubspace sigma T hs :=
    bs.equiv bs' (Equiv.refl _)
  have hbi : ∀ i, h (bs i) = w i • bs i := fun i => by
    simp [h, bs', Module.Basis.equiv_apply, Module.Basis.unitsSMul_apply]
  have hh : B0.comp h.toLinearMap h.toLinearMap = ν • B0 := by
    apply LinearMap.BilinForm.ext_basis bs
    intro i j
    show B0 (h (bs i)) (h (bs j)) = ν • B0 (bs i) (bs j)
    rw [hbi i, hbi j]
    rcases i with i | i <;> rcases j with j | j
    · simp [w, hll, Units.smul_def]
    · simp [w, νu, Units.smul_def, mul_comm]
    · simp [w, νu, Units.smul_def]
    · simp [w, νu, Units.smul_def, hrr]
  set ĥ := extendFixedEquiv sigma hsigma hne h2 T hT hs h with hĥdef
  obtain ⟨e, he⟩ :=
    CatalogueBLinearDescent.exists_fixed_finrank_basis sigma hsigma hne h2 T hT hs
  have hBh : B.comp ĥ.toLinearMap ĥ.toLinearMap = (ι ^ 2)⁻¹ • B := by
    apply LinearMap.BilinForm.ext_basis e
    intro i j
    have hi : ĥ (e i) = (h ⟨e i, he i⟩ : V) :=
      extendFixedEquiv_fixed sigma hsigma hne h2 T hT hs h ⟨e i, he i⟩
    have hj : ĥ (e j) = (h ⟨e j, he j⟩ : V) :=
      extendFixedEquiv_fixed sigma hsigma hne h2 T hT hs h ⟨e j, he j⟩
    have key := congrArg (fun a : fixedSubfield K sigma => (a : K))
      (LinearMap.congr_fun₂ hh ⟨e i, he i⟩ ⟨e j, he j⟩)
    simp only [LinearMap.BilinForm.comp_apply, LinearMap.coe_coe, LinearMap.smul_apply,
      smul_eq_mul, hB0def] at key
    push_cast at key
    simp only [descendedBilinear_apply] at key
    show B (ĥ (e i)) (ĥ (e j)) = (ι ^ 2)⁻¹ * B (e i) (e j)
    rw [hi, hj]
    have hν : ((ν : fixedSubfield K sigma) : K) = (ι ^ 2)⁻¹ := rfl
    rw [hν] at key
    apply mul_left_cancel₀ c.ne_zero
    rw [key]
    ring
  let ιu : Kˣ := Units.mk0 ι hι0
  let g : V ≃ₗ[K] V := ĥ.trans (LinearEquiv.smulOfUnit ιu)
  have hg_apply : ∀ x, g x = ι • ĥ x := fun x => rfl
  have hgiso : g ∈ isometryGroup B := by
    rw [mem_isometryGroup_iff]
    intro x y
    have h1 := LinearMap.congr_fun₂ hBh x y
    simp only [LinearMap.BilinForm.comp_apply, LinearMap.coe_coe, LinearMap.smul_apply,
      smul_eq_mul] at h1
    have h1' : B (ĥ x) (ĥ y) = (ι ^ 2)⁻¹ * B x y := h1
    simp only [hg_apply, map_smul, LinearMap.smul_apply, smul_eq_mul]
    rw [h1']
    field_simp
  have hcomm : ∀ x, ĥ (tau0 x) = tau0 (ĥ x) :=
    (commutes_normalized_iff tau0 b ĥ.toLinearMap).mp fun x =>
      extendFixedEquiv_commutes sigma hsigma hne h2 T hT hs h x
  refine ⟨⟨g, hgiso⟩, ?_⟩
  apply Subtype.ext
  apply LinearEquiv.ext
  intro x
  rw [semilinearConjugation_apply]
  change tau0 (g (tau0.symm x)) = g (-x)
  rw [hg_apply, hg_apply, hsemi, hσι, ← hcomm, tau0.apply_symm_apply]
  simp [neg_smul, smul_neg]

end NegIsometry

end CFSG.LocalAnalysis.EvenBN.UnitaryFiveTwo
