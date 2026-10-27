module

public import CFSG.GH74.Uniqueness.Bender.O3
public import CFSG.GH74.Uniqueness.Bender.AutFixed
public import CFSG.GH74.Uniqueness.Bender.Models
public import CFSG.LocalAnalysis.ComponentInitial.UnitaryHigherEvenAllInvolutionFourGroup
public import CFSG.LocalAnalysis.ShultStronglyClosedTI.RankOneModelTransport
public import CFSG.LocalAnalysis.ShultStronglyClosedTI.OddPrimeInvertersLinear
import CFSG.Models.BenderSuzuki
public import CFSG.CharacterTheory.Semidihedral.OddFieldLift
public import CFSG.LieType.BorelTits.CompleteFlag
public import CFSG.LocalAnalysis.ComponentClassification.CatalogueBDerivedNormalSectionBound
public import CFSG.LocalAnalysis.ComponentClassification.CatalogueBHeldSmallCorePrimeCore
public import CFSG.LocalAnalysis.ComponentClassification.CatalogueBOrthogonalDescentEndpoint
public import CFSG.LocalAnalysis.ComponentClassification.CatalogueBOrthogonalFiveStructure
public import CFSG.LocalAnalysis.ComponentClassification.CatalogueBOrthogonalFixedTransfer
public import CFSG.LocalAnalysis.ComponentClassification.CatalogueBOrthogonalPointActionModels
public import CFSG.LocalAnalysis.ComponentClassification.CatalogueBOrthogonalPointPlusBorelModel
public import CFSG.LocalAnalysis.ComponentClassification.CatalogueBOrthogonalScalarSquareField
public import CFSG.LocalAnalysis.ComponentClassification.CatalogueBOrthogonalScalarSquareStructure
public import CFSG.LocalAnalysis.ComponentClassification.CatalogueBOrthogonalSixComponentsCover
public import CFSG.LocalAnalysis.ComponentClassification.CatalogueBOrthogonalSixModelGeometry
public import CFSG.LocalAnalysis.ComponentClassification.CatalogueBOrthogonalTraceZeroCoordinates
public import CFSG.LocalAnalysis.ComponentClassification.CatalogueBProjectiveInvolutionStructure
public import CFSG.LocalAnalysis.ComponentClassification.CatalogueBSymplecticBField
public import CFSG.LocalAnalysis.ComponentClassification.CatalogueBSymplecticBLinear
public import CFSG.LocalAnalysis.ComponentClassification.CatalogueBSymplecticRepresentationOdd
public import CFSG.LocalAnalysis.ComponentClassification.CatalogueKProper
public import CFSG.LocalAnalysis.ComponentClassification.CatalogueKProperGroups
public import CFSG.LocalAnalysis.ComponentInitial.LinearInvolutionFixedField
public import CFSG.LocalAnalysis.ComponentInitial.OrthogonalFamilyLemmasFive
public import CFSG.LocalAnalysis.ComponentInitial.OrthogonalFamilyLemmasSix
public import CFSG.LocalAnalysis.ComponentInitial.OrthogonalReflectionSplitting
public import CFSG.LocalAnalysis.ComponentInitial.OrthogonalStandardFormsRegular
public import CFSG.LocalAnalysis.ProperTwoGeneratedCore.LocalCriterionDenominatorCyclic
public import CFSG.LocalAnalysis.ShultStronglyClosedTI.SuzukiModelPointStructure
public import CFSG.ThirdParty.QiuzhenCFSG.BenderSuzuki.External.Huppert.IV.theorem_5_4
public import CFSG.ThirdParty.QiuzhenCFSG.GorensteinWalter.Defs
public import CFSG.ThirdParty.QiuzhenCFSG.GorensteinWalter.FiniteFieldFixedSubfieldCard
public import TauCeti.LinearAlgebra.Dimension.IsQuadraticExtension
public import TauCeti.LinearAlgebra.QuadraticForm.OrthogonalBasis
public import TauCeti.LinearAlgebra.QuadraticForm.OrthogonalGroup.LowRank

public section

namespace CFSG.GH74.Uniqueness.Bender

open Matrix CFSG.LocalAnalysis.ComponentInitial CFSG.LocalAnalysis.ComponentInitial.UnitaryHigher
open CFSG.LocalAnalysis.ComponentInitial.FourGroupEvenCanonical
open CFSG.ClassicalGroups.UnitaryFlag
open CFSG.ComponentClassification.UnbalancedCatalog.UnitaryFieldTransfer
open CFSG.ComponentClassification.UnbalancedCatalog (IsCanonicalGram isCanonicalGram_one
  even_unitary_canonical_field_centralizer_transfer)

section Fixed

variable {f : ℕ} {E : Type} [Field E] (h : UnitaryFieldData 2 f E) {C : GL (Fin 3) E}
  (hC : IsPrimeFormGram C) {Cl : GL (Fin 3) h.fixedField}
  (hCl : (Cl : Matrix (Fin 3) (Fin 3) h.fixedField).map h.fixedField.subtype = C)

include hCl in
theorem exists_isometry_of_fixed {φ : E ≃+* E} (hφ : ∀ x, φ x = h.bar x)
    (x : primeFormP h (C : Matrix (Fin 3) (Fin 3) E))
    (hx : primeFormFieldAut h hC φ x = x) :
    ∃ g : matrixIsometryGroup (Cl : Matrix (Fin 3) (Fin 3) h.fixedField),
      fixedIsometryProj h hCl g = x := by
  obtain ⟨s, rfl⟩ := QuotientGroup.mk_surjective x
  rw [primeFormFieldAut_mk] at hx
  have hz : (primeFormFieldSU h hC φ s)⁻¹ * s ∈
      normOneScalars h (gramSU h (C : Matrix (Fin 3) (Fin 3) E)) 3 := QuotientGroup.eq.mp hx
  set z := (primeFormFieldSU h hC φ s)⁻¹ * s with hzdef
  obtain ⟨c, hcN, hc3, hcz⟩ := hz
  have hbc : φ (c : E) = ((c⁻¹ : Eˣ) : E) := by
    rw [hφ, Units.val_inv_eq_inv_val]
    exact eq_inv_of_mul_eq_one_right hcN
  have hfz : primeFormFieldSU h hC φ z = z⁻¹ := by
    apply Subtype.ext
    change glAut φ (z : GL (Fin 3) E) = ((z⁻¹ : gramSU h (C : Matrix (Fin 3) (Fin 3) E)) :
      GL (Fin 3) E)
    rw [Subgroup.coe_inv, hcz, ← map_inv (GeneralLinearGroup.scalar (Fin 3) (R := E))]
    apply Units.ext
    rw [coe_glAut, GeneralLinearGroup.coe_scalar, GeneralLinearGroup.coe_scalar, scalar_apply,
      scalar_apply, diagonal_map (map_zero φ), hbc]
  have hz3 : z * z * z = 1 := by
    apply Subtype.ext
    change (z : GL (Fin 3) E) * z * z = 1
    have hc3' : c * c * c = 1 := by rw [← pow_three']; exact hc3
    rw [hcz, ← map_mul, ← map_mul, hc3', map_one]
  have hfs : primeFormFieldSU h hC φ s = s * z⁻¹ := by
    rw [hzdef]
    group
  have hzinv : z⁻¹ = z * z := inv_eq_of_mul_eq_one_right (by rw [← mul_assoc]; exact hz3)
  have hzz : z⁻¹ * z⁻¹ = z := by
    rw [hzinv, show z * z * (z * z) = (z * z * z) * z by group, hz3, one_mul]
  have hfs' : primeFormFieldSU h hC φ (s * z) = s * z := by
    rw [map_mul, hfs, hfz, mul_assoc, hzz]
  have hbar' : (((s * z : gramSU h (C : Matrix (Fin 3) (Fin 3) E)) : GL (Fin 3) E) :
      Matrix (Fin 3) (Fin 3) E).map h.bar =
      (((s * z : gramSU h (C : Matrix (Fin 3) (Fin 3) E)) : GL (Fin 3) E) :
        Matrix (Fin 3) (Fin 3) E) := by
    have h1 := congrArg (fun y : gramSU h (C : Matrix (Fin 3) (Fin 3) E) =>
      ((y : GL (Fin 3) E) : Matrix (Fin 3) (Fin 3) E)) hfs'
    change (((glAut φ ((s * z : gramSU h (C : Matrix (Fin 3) (Fin 3) E)) : GL (Fin 3) E) :
      GL (Fin 3) E)) : Matrix (Fin 3) (Fin 3) E) = _ at h1
    rw [coe_glAut] at h1
    refine Eq.trans ?_ h1
    ext i j
    simp [Matrix.map_apply, hφ]
  set g₀ := descendGL h ((s * z : gramSU h (C : Matrix (Fin 3) (Fin 3) E)) : GL (Fin 3) E) hbar'
    with hg₀def
  have hdesc : ((g₀ : GL (Fin 3) h.fixedField) : Matrix (Fin 3) (Fin 3) h.fixedField).map
      h.fixedField.subtype =
      (((s * z : gramSU h (C : Matrix (Fin 3) (Fin 3) E)) : GL (Fin 3) E) :
        Matrix (Fin 3) (Fin 3) E) := descendMatrix_map h _ hbar'
  have hg₀ : g₀ ∈ matrixIsometryGroup (Cl : Matrix (Fin 3) (Fin 3) h.fixedField) := by
    rw [mem_matrixIsometryGroup]
    apply map_subtype_injective h
    dsimp only
    rw [Matrix.map_mul, Matrix.map_mul, Matrix.transpose_map, hdesc, hCl]
    have h1 := (s * z : gramSU h (C : Matrix (Fin 3) (Fin 3) E)).2.1
    rw [hbar'] at h1
    exact h1
  refine ⟨⟨g₀, hg₀⟩, ?_⟩
  change ((fixedIsometrySU h hCl ⟨g₀, hg₀⟩ : gramSU h (C : Matrix (Fin 3) (Fin 3) E)) :
    primeFormP h (C : Matrix (Fin 3) (Fin 3) E)) = (s : primeFormP h (C : Matrix (Fin 3) (Fin 3) E))
  rw [show fixedIsometrySU h hCl ⟨g₀, hg₀⟩ = s * z from Subtype.ext (map_descendGL h _ hbar'),
    QuotientGroup.mk_mul, (QuotientGroup.eq_one_iff z).mpr (mem_normOneScalars.mpr ⟨c, hcN, hc3, hcz⟩), mul_one]

include hCl in
theorem nonempty_autFixed_mulEquiv_isometry {φ : E ≃+* E} (hφ : ∀ x, φ x = h.bar x) :
    Nonempty (autFixed (primeFormFieldAut h hC φ) ≃*
      matrixIsometryGroup (Cl : Matrix (Fin 3) (Fin 3) h.fixedField)) := by
  have hfix : ∀ g, fixedIsometryProj h hCl g ∈ autFixed (primeFormFieldAut h hC φ) :=
    fun g => primeFormFieldAut_fixedIsometryProj h hCl hC hφ g
  let ι' : matrixIsometryGroup (Cl : Matrix (Fin 3) (Fin 3) h.fixedField) →*
      autFixed (primeFormFieldAut h hC φ) := (fixedIsometryProj h hCl).codRestrict _ hfix
  have hbij : Function.Bijective ι' :=
    ⟨fun a b hab => fixedIsometryProj_injective h hCl le_rfl (congrArg Subtype.val hab),
      fun y => by
        obtain ⟨g, hg⟩ := exists_isometry_of_fixed h hC hCl hφ y.1 y.2
        exact ⟨g, Subtype.ext hg⟩⟩
  exact ⟨(MulEquiv.ofBijective ι' hbij).symm⟩

theorem glAut_map_subtype_general (φ : E ≃+* E) (g : GL (Fin 3) h.fixedField) :
    glAut φ (GeneralLinearGroup.map h.fixedField.subtype g) =
      GeneralLinearGroup.map h.fixedField.subtype (glAut (fixedRestrict h φ) g) := by
  apply Units.ext
  rw [coe_glAut]
  ext i j
  rfl

include hCl in
theorem psi_apply_fixedIsometryProj
    (hcan : IsCanonicalGram (Cl : Matrix (Fin 3) (Fin 3) h.fixedField))
    (g g₁ : matrixIsometryGroup (Cl : Matrix (Fin 3) (Fin 3) h.fixedField)) (φ' : E ≃+* E) :
    primeFormPsi h hC ⟨fixedIsometryHom h hCl g, φ'⟩ (fixedIsometryProj h hCl g₁) =
      fixedIsometryProj h hCl (g * fixedAct h hcan φ' g₁ * g⁻¹) := by
  rw [primeFormPsi_apply, MulAut.mul_apply]
  change primeFormConjHom h _ (fixedIsometryHom h hCl g)
    (primeFormFieldAut h hC φ' ((fixedIsometrySU h hCl g₁ : gramSU h (C : Matrix (Fin 3) (Fin 3) E)) :
      primeFormP h (C : Matrix (Fin 3) (Fin 3) E))) = _
  rw [primeFormFieldAut_mk, primeFormConjHom_mk]
  change _ = ((fixedIsometrySU h hCl (g * fixedAct h hcan φ' g₁ * g⁻¹) :
    gramSU h (C : Matrix (Fin 3) (Fin 3) E)) : primeFormP h (C : Matrix (Fin 3) (Fin 3) E))
  congr 1

end Fixed

section D1

variable {f : ℕ} {E : Type} [Field E] (h : UnitaryFieldData 2 f E)

theorem map_one_subtype :
    (((1 : GL (Fin 3) h.fixedField) : Matrix (Fin 3) (Fin 3) h.fixedField)).map
      h.fixedField.subtype = (((1 : GL (Fin 3) E) : Matrix (Fin 3) (Fin 3) E)) := by
  rw [Units.val_one, Matrix.map_one _ (map_zero _) (map_one _), Units.val_one]

theorem eq_one_or_eq_of_centralizes (hq : ¬(3 = 3 ∧ 2 ^ f = 2)) {φ : E ≃+* E}
    (hφ : ∀ x, φ x = h.bar x)
    (β : MulAut (primeFormP h ((1 : GL (Fin 3) E) : Matrix (Fin 3) (Fin 3) E)))
    (hβγ : β * primeFormFieldAut h isPrimeFormGram_one φ =
      primeFormFieldAut h isPrimeFormGram_one φ * β)
    (hβfix : ∀ g : matrixIsometryGroup (1 : Matrix (Fin 3) (Fin 3) h.fixedField),
      β (fixedIsometryProj h (map_one_subtype h) g) = fixedIsometryProj h (map_one_subtype h) g) :
    β = 1 ∨ β = primeFormFieldAut h isPrimeFormGram_one φ := by
  have hcharF : CharP h.fixedField 2 := fixedField_charP h
  have hfinF : Finite h.fixedField := fixedField_finite h
  have hcan : IsCanonicalGram (((1 : GL (Fin 3) h.fixedField) : Matrix (Fin 3) (Fin 3)
      h.fixedField)) := by
    rw [Units.val_one]
    exact isCanonicalGram_one
  have hcen := (even_unitary_canonical_field_centralizer_transfer h (le_refl 3) hq
    isPrimeFormGram_one (Or.inl (by rw [Units.val_one])) 1 (map_one_subtype h) φ hφ).1 β
  obtain ⟨g, φ', hβ⟩ := hcen.mp (Subgroup.mem_centralizer_singleton_iff.mpr hβγ)
  have hfix' : ∀ g₁ : matrixIsometryGroup (1 : Matrix (Fin 3) (Fin 3) h.fixedField),
      g * fixedAct h hcan φ' g₁ * g⁻¹ = g₁ := by
    intro g₁
    have h1 := hβfix g₁
    rw [hβ, psi_apply_fixedIsometryProj h isPrimeFormGram_one (map_one_subtype h) hcan g g₁ φ']
      at h1
    exact fixedIsometryProj_injective h (map_one_subtype h) le_rfl h1
  have h2 : (2 : h.fixedField) = 0 := CharTwo.two_eq_zero
  have hconjtr : ∀ (G : GL (Fin 3) h.fixedField) (N : Matrix (Fin 3) (Fin 3) h.fixedField),
      Matrix.trace ((G : Matrix (Fin 3) (Fin 3) h.fixedField) * N *
        ((G⁻¹ : GL (Fin 3) h.fixedField) : Matrix (Fin 3) (Fin 3) h.fixedField)) =
        Matrix.trace N := by
    intro G N
    rw [Matrix.trace_mul_comm, ← Matrix.mul_assoc, Units.inv_mul, Matrix.one_mul]
  have hfr : fixedRestrict h φ' = 1 := by
    refine RingEquiv.ext fun t => ?_
    have hdet : (!![0, 1; 1, (t : h.fixedField)] : Matrix (Fin 2) (Fin 2) h.fixedField).det =
        1 := by
      rw [Matrix.det_fin_two]
      simp
      linear_combination (-1 : h.fixedField) * h2
    set A : Matrix.SpecialLinearGroup (Fin 2) h.fixedField := ⟨!![0, 1; 1, t], hdet⟩ with hA
    have h1 := hfix' (sl2ToIsometry A)
    have h3 := congrArg (fun x : matrixIsometryGroup (1 : Matrix (Fin 3) (Fin 3) h.fixedField) =>
      Matrix.trace (((x : GL (Fin 3) h.fixedField)) : Matrix (Fin 3) (Fin 3) h.fixedField)) h1
    simp only [Subgroup.coe_mul, Units.val_mul, Subgroup.coe_inv] at h3
    rw [hconjtr] at h3
    have h5 : (fixedRestrict h φ') (Matrix.trace ((sl2ToGL A : GL (Fin 3) h.fixedField) :
        Matrix (Fin 3) (Fin 3) h.fixedField)) =
        Matrix.trace ((sl2ToGL A : GL (Fin 3) h.fixedField) :
          Matrix (Fin 3) (Fin 3) h.fixedField) := by
      have h6 := h3
      change Matrix.trace (((glAut (fixedRestrict h φ') (sl2ToGL A) : GL (Fin 3) h.fixedField)) :
        Matrix (Fin 3) (Fin 3) h.fixedField) = Matrix.trace ((sl2ToGL A : GL (Fin 3)
          h.fixedField) : Matrix (Fin 3) (Fin 3) h.fixedField) at h6
      rw [coe_glAut] at h6
      refine Eq.trans ?_ h6
      simp [Matrix.trace, map_sum]
    rw [trace_sl2ToGL] at h5
    have h7 : (fixedRestrict h φ') (1 + 0 + t) = 1 + 0 + t := by
      simpa [hA] using h5
    simpa using h7
  have hfa : ∀ g₁ : matrixIsometryGroup (1 : Matrix (Fin 3) (Fin 3) h.fixedField),
      fixedAct h hcan φ' g₁ = g₁ := by
    intro g₁
    have h1 : fixedAct h hcan φ' = 1 := by
      unfold fixedAct
      rw [MonoidHom.comp_apply, hfr, map_one]
    rw [h1]
    rfl
  have hg1 : g = 1 := by
    let e := isometryThreeEquivSL2 (k := h.fixedField)
    have hz : e g ∈ Subgroup.center (Matrix.SpecialLinearGroup (Fin 2) h.fixedField) := by
      rw [Subgroup.mem_center_iff]
      intro x
      have h1 := hfix' (e.symm x)
      rw [hfa] at h1
      have h2' : g * e.symm x = e.symm x * g := by
        calc g * e.symm x = g * e.symm x * g⁻¹ * g := by group
          _ = e.symm x * g := by rw [h1]
      have h3 := congrArg e h2'
      rw [map_mul, map_mul, MulEquiv.apply_symm_apply] at h3
      exact h3.symm
    rw [sl2_center_eq_bot', Subgroup.mem_bot] at hz
    exact e.injective (hz.trans (map_one e).symm)
  have hφ'mem : φ' ∈ Subgroup.zpowers φ := mem_zpowers_of_fixedRestrict_eq_one h hφ hfr
  have hφφ : φ * φ = 1 := RingEquiv.ext fun x => by
    change φ (φ x) = x
    rw [hφ, hφ, h.bar_bar]
  obtain ⟨j, hj⟩ := Subgroup.mem_zpowers_iff.mp hφ'mem
  have hj2 : φ ^ j = 1 ∨ φ ^ j = φ := by
    obtain ⟨r, hr | hr⟩ := Int.even_or_odd' j
    · left
      rw [hr, _root_.zpow_mul, zpow_two, hφφ, _root_.one_zpow]
    · right
      rw [hr, _root_.zpow_add_one, _root_.zpow_mul, zpow_two, hφφ, _root_.one_zpow, one_mul]
  have hβΨ : ∀ φ'' : E ≃+* E, primeFormPsi h isPrimeFormGram_one
      ⟨fixedIsometryHom h (map_one_subtype h) 1, φ''⟩ =
      primeFormFieldAut h isPrimeFormGram_one φ'' := by
    intro φ''
    rw [primeFormPsi_apply, map_one, map_one, one_mul]
    rfl
  subst hg1
  rw [hβ, hβΨ, ← hj]
  rcases hj2 with h1 | h1
  · left
    rw [h1]
    exact (primeFormFieldHom h isPrimeFormGram_one).map_one
  · right
    rw [h1]

end D1

section Main

open CFSG.BenderSuzuki CFSG.ShultStronglyClosedTI CFSG.Assembly.LowTwoRank

abbrev UnitaryModelP (n : ℕ) (hU : UnitaryFieldData 2 n (GaloisField 2 (2 * n))) : Type :=
  primeFormP hU ((1 : GL (Fin 3) (GaloisField 2 (2 * n))) :
    Matrix (Fin 3) (Fin 3) (GaloisField 2 (2 * n)))

theorem unitaryFieldData_gf {n : ℕ} (hn : 1 ≤ n) : UnitaryFieldData 2 n (GaloisField 2 (2 * n)) :=
  ⟨Nat.prime_two, hn, GaloisField.card 2 (2 * n) (by omega)⟩

theorem BenderType.exists_outer_model_unitary {K : Type*} [Group K] {n e : ℕ}
    (h : BenderType K n 3 e) (α : MulAut K) (hα : α * α = 1)
    (hout : ¬ ∃ g : K, ∀ x : K, α x = g * x * g⁻¹) :
    ∃ (hU : UnitaryFieldData 2 n (GaloisField 2 (2 * n)))
      (ψ : K ≃* UnitaryModelP n hU) (θ : MulAut (UnitaryModelP n hU))
      (φ : GaloisField 2 (2 * n) ≃+* GaloisField 2 (2 * n)),
      (∀ x, φ x = hU.bar x) ∧
        MulAut.congr ψ α = MulAut.congr θ (primeFormFieldAut hU isPrimeFormGram_one φ) := by
  obtain ⟨hn, ⟨e₁⟩⟩ : 2 ≤ n ∧ Nonempty (K ≃* PSU3Model n) := by
    cases h with
    | unitary n hn e => exact ⟨hn, ⟨e⟩⟩
  have hmodel : PSU3Model n = CFSG.Open.PSU3 2 n := CFSG.Models.benderPSU3Model_eq_psu3 n
  let E := GaloisField 2 (2 * n)
  have hU : UnitaryFieldData 2 n E := unitaryFieldData_gf (by omega)
  have e₀ : K ≃* StatedProj (StatedSU 3 (2 ^ n) E) :=
    (e₁.trans (MulEquiv.subgroupCongr hmodel)).trans (glaSUCanonicalEquivNative n).symm
  have hC : IsPrimeFormGram (1 : GL (Fin 3) E) := isPrimeFormGram_one
  have hn3 : 3 ≤ 3 := le_rfl
  have hq : ¬(3 = 3 ∧ 2 ^ n = 2) := by
    rintro ⟨-, h2⟩
    have : 2 ^ 2 ≤ 2 ^ n := Nat.pow_le_pow_right (by norm_num) hn
    omega
  obtain ⟨χ⟩ := nonempty_primeFormP_mulEquiv hU hC
  let ψ : K ≃* UnitaryModelP n hU :=
    e₀.trans ((unitaryPSUEquiv hU (by omega)).symm.trans χ.symm)
  set β := MulAut.congr ψ α with hβdef
  have hβ2 : β * β = 1 := mulAut_congr_sq_eq_one ψ hα
  have hβout : ¬ ∃ g, ∀ x, β x = g * x * g⁻¹ := not_inner_congr ψ hout
  have hβ1 : β ≠ 1 := by
    intro h1
    apply hβout
    refine ⟨1, fun x => ?_⟩
    rw [h1]
    simp
  have hord : orderOf β = 2 := by
    have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
    refine orderOf_eq_prime ?_ hβ1
    rw [sq]
    exact hβ2
  obtain ⟨hcases, -, -, hDinner⟩ := even_unitary_involution_matrix_lifts hU hC hn3 hq β hord
  rcases hcases with hid | hbar
  · exfalso
    apply hβout
    have hin := hDinner β (by
      rw [← ker_primeFormFieldFactor hU hC hn3 hq, MonoidHom.mem_ker]
      exact hid) hord
    obtain ⟨y, hy⟩ := hin
    exact ⟨y, fun x => by rw [← hy]; rfl⟩
  obtain ⟨-, -, C₀, hC₀, hcase₀, -, -, -, -, ⟨θ, -, hθβ⟩, -⟩ :=
    even_unitary_antiunitary_involution_descent hU hC hn3 hq β hord hbar
  have hC₀1 : (C₀ : Matrix (Fin 3) (Fin 3) E) = 1 := by
    rcases hcase₀ with h1 | ⟨r, hr, -⟩
    · exact h1
    · omega
  have hC₀eq : C₀ = 1 := Units.ext hC₀1
  subst hC₀eq
  exact ⟨hU, ψ, θ, primeFormFieldFactor hU hC hn3 hq β, hbar, MulEquiv.ext hθβ⟩

theorem BenderType.fixed_unitary {K : Type*} [Group K] {n e : ℕ} (h : BenderType K n 3 e)
    (α : MulAut K) (hα : α * α = 1) (hout : ¬ ∃ g : K, ∀ x : K, α x = g * x * g⁻¹) :
    Nonempty (autFixed α ≃* PSL2Model n) := by
  obtain ⟨hU, ψ, θ, φ, hφ, hαθ⟩ := h.exists_outer_model_unitary α hα hout
  obtain ⟨hn, -⟩ : 2 ≤ n ∧ Nonempty (K ≃* PSU3Model n) := by
    cases h with
    | unitary n hn e => exact ⟨hn, ⟨e⟩⟩
  have hfk : Finite hU.fixedField := fixedField_finite hU
  have hchar : CharP hU.fixedField 2 := fixedField_charP hU
  have hC : IsPrimeFormGram (1 : GL (Fin 3) (GaloisField 2 (2 * n))) := isPrimeFormGram_one
  have hCl : (((1 : GL (Fin 3) hU.fixedField) : Matrix (Fin 3) (Fin 3) hU.fixedField)).map
      hU.fixedField.subtype = (((1 : GL (Fin 3) (GaloisField 2 (2 * n))) :
        Matrix (Fin 3) (Fin 3) (GaloisField 2 (2 * n)))) := by
    rw [Units.val_one, Matrix.map_one _ (map_zero _) (map_one _), Units.val_one]
  obtain ⟨e₃⟩ := nonempty_autFixed_mulEquiv_isometry hU hC hCl hφ
  have e₄ : autFixed α ≃* autFixed (primeFormFieldAut hU hC φ) :=
    ((autFixedEquiv ψ α).trans (MulEquiv.subgroupCongr (by rw [hαθ]))).trans
      (autFixedEquiv θ (primeFormFieldAut hU hC φ)).symm
  have hcardk : Nat.card hU.fixedField = 2 ^ n := by
    have := UnitaryFieldData.card_fixedField hU
    simpa using this
  have e₅ := isometryThreeEquivSL2 (k := hU.fixedField)
  exact ⟨(e₄.trans e₃).trans (e₅.trans (OddPrimeInverters.sl2EquivPSL2Binary (by omega) hcardk))⟩

theorem BenderType.centralizer_unitary {K : Type*} [Group K] {n e : ℕ} (h : BenderType K n 3 e)
    (α : MulAut K) (hα : α * α = 1) (hout : ¬ ∃ g : K, ∀ x : K, α x = g * x * g⁻¹)
    (β : MulAut K) (hβα : β * α = α * β) (hβ : ∀ x ∈ autFixed α, β x = x) :
    β = 1 ∨ β = α := by
  obtain ⟨hU, ψ, θ, φ, hφ, hαθ⟩ := h.exists_outer_model_unitary α hα hout
  obtain ⟨hn, -⟩ : 2 ≤ n ∧ Nonempty (K ≃* PSU3Model n) := by
    cases h with
    | unitary n hn e => exact ⟨hn, ⟨e⟩⟩
  have hq : ¬(3 = 3 ∧ 2 ^ n = 2) := by
    rintro ⟨-, h2⟩
    have : 2 ^ 2 ≤ 2 ^ n := Nat.pow_le_pow_right (by norm_num) hn
    omega
  set γ := primeFormFieldAut hU isPrimeFormGram_one φ with hγ
  set β'' := (MulAut.congr θ).symm (MulAut.congr ψ β) with hβ''
  have hβ''c : MulAut.congr θ β'' = MulAut.congr ψ β := MulEquiv.apply_symm_apply _ _
  have hcomm : β'' * γ = γ * β'' := by
    apply (MulAut.congr θ).injective
    rw [map_mul, map_mul, hβ''c, ← hαθ, ← map_mul, ← map_mul, hβα]
  have hfix : ∀ g : matrixIsometryGroup (1 : Matrix (Fin 3) (Fin 3) hU.fixedField),
      β'' (fixedIsometryProj hU (map_one_subtype hU) g) =
        fixedIsometryProj hU (map_one_subtype hU) g := by
    intro g
    set x := fixedIsometryProj hU (map_one_subtype hU) g with hx
    have hγx : γ x = x := primeFormFieldAut_fixedIsometryProj hU (map_one_subtype hU) isPrimeFormGram_one hφ g
    have hθx : θ x ∈ autFixed (MulAut.congr ψ α) := by
      rw [hαθ, mem_autFixed_iff]
      change θ (γ (θ.symm (θ x))) = θ x
      rw [MulEquiv.symm_apply_apply, hγx]
    have hψx := hβ _ ((mem_autFixed_congr_iff ψ α _).mp hθx)
    have h1 : MulAut.congr ψ β (θ x) = θ x := by
      change ψ (β (ψ.symm (θ x))) = θ x
      rw [hψx, MulEquiv.apply_symm_apply]
    change θ.symm ((MulAut.congr ψ β) (θ x)) = x
    rw [h1, MulEquiv.symm_apply_apply]
  rcases eq_one_or_eq_of_centralizes hU hq hφ β'' hcomm hfix with h1 | h1
  · left
    apply (MulAut.congr ψ).injective
    rw [← hβ''c, h1, map_one, map_one]
  · right
    apply (MulAut.congr ψ).injective
    rw [← hβ''c, h1, hαθ]

end Main

end CFSG.GH74.Uniqueness.Bender
