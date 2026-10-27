module

public import CFSG.LocalAnalysis.ComponentClassification.UnbalancedCatalogRigidityOrthCentralizer
public import CFSG.LocalAnalysis.ComponentClassification.CatalogueBAlternatingIsometryBasis
public import CFSG.ClassicalGroups.Symplectic.Model
public import CFSG.Open.StatedDefs
public import CFSG.LieType.BorelTits.CompleteFlag
public import CFSG.LocalAnalysis.ComponentClassification.CatalogueBDerivedNormalSectionBound
public import CFSG.LocalAnalysis.ComponentClassification.CatalogueBHeldSmallCorePrimeCore
public import CFSG.LocalAnalysis.ComponentClassification.CatalogueBOrthogonalDescentEndpoint
public import CFSG.LocalAnalysis.ComponentClassification.CatalogueBOrthogonalFiveStructure
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
public import CFSG.LocalAnalysis.ComponentClassification.DisjointSolvableKernels
public import CFSG.LocalAnalysis.ComponentClassification.LayerMultiplication
public import CFSG.LocalAnalysis.ComponentClassification.MinimalBCenter
public import CFSG.LocalAnalysis.ComponentClassification.OrdinaryComponentJoins
public import CFSG.LocalAnalysis.ComponentClassification.TwoLayer
public import CFSG.LocalAnalysis.ComponentClassification.UnbalancedCatalogRigidityAlternating
public import CFSG.LocalAnalysis.ComponentClassification.UnbalancedCatalogRigidityOrthRestrict
public import CFSG.LocalAnalysis.ComponentClassification.UniversalOrbitBlock
public import CFSG.LocalAnalysis.ComponentInitial.OrthogonalFamilyLemmasFive
public import CFSG.LocalAnalysis.ComponentInitial.OrthogonalFamilyLemmasSix
public import CFSG.LocalAnalysis.ComponentInitial.OrthogonalReflectionSplitting
public import CFSG.LocalAnalysis.ComponentInitial.OrthogonalStandardFormsRegular
public import CFSG.LocalAnalysis.ComponentInitial.UnitaryHigherEvenOrthogonalModel
public import CFSG.LocalAnalysis.SectionRank.PRank
public import CFSG.LocalAnalysis.SectionRank.SQT
public import CFSG.ThirdParty.QiuzhenCFSG.GorensteinWalter.Defs
public import CFSG.ThirdParty.QiuzhenCFSG.GorensteinWalter.FiniteFieldFixedSubfieldCard
public import TauCeti.LinearAlgebra.Dimension.IsQuadraticExtension
public import TauCeti.LinearAlgebra.QuadraticForm.OrthogonalBasis
public import TauCeti.LinearAlgebra.QuadraticForm.OrthogonalGroup.LowRank

public section

attribute [-instance] instCommGroupOfIsSimpleGroupOfIsNilpotent
  instAddCommGroupOfIsSimpleAddGroupOfIsNilpotent

namespace CFSG.HardMathSupport.Curtis.Coordinator.PLType.OrthCoord

open Matrix QuadraticMap CFSG.ClassicalGroups.Orthogonal CFSG.LocalAnalysis.ComponentInitial
open CFSG.ComponentClassification.CatalogueBOrthogonalSemilinear
open CFSG.ComponentClassification.UnbalancedCatalog
open CFSG.ClassicalGroups.Alternating (symplecticTransvection symplecticTransvection_apply
  symplecticTransvection_zero alternating_transvection_generation)

theorem bijective_restrict_of_index_two {G P : Type*} [Group G] [Group P]
    (O Ω S : Subgroup G) (hSO : S ≤ O)
    (hidx : ∀ x y, x ∈ O → y ∈ O → x ∉ Ω → y ∉ Ω → x * y ∈ Ω)
    (z : G) (hz : z ∈ S) (hzΩ : z ∉ Ω)
    (ρ : S →* P) (hsurj : Function.Surjective ρ)
    (hker : ∀ s : S, ρ s = 1 → s = 1 ∨ (s : G) = z)
    (hz1 : ρ ⟨z, hz⟩ = 1) :
    Function.Bijective (ρ.comp (Subgroup.inclusion (inf_le_right : Ω ⊓ S ≤ S))) := by
  constructor
  · rw [← MonoidHom.ker_eq_bot_iff, eq_bot_iff]
    intro a ha
    rw [MonoidHom.mem_ker, MonoidHom.comp_apply] at ha
    rw [Subgroup.mem_bot]
    rcases hker _ ha with h | h
    · apply Subtype.ext
      have := congrArg (fun s : S => (s : G)) h
      simpa using this
    · exact absurd (h ▸ (a.2.1 : (a : G) ∈ Ω)) hzΩ
  · intro p
    obtain ⟨s, rfl⟩ := hsurj p
    by_cases hs : (s : G) ∈ Ω
    · exact ⟨⟨s, hs, s.2⟩, rfl⟩
    · have hsz : (s : G) * z ∈ Ω := hidx _ _ (hSO s.2) (hSO hz) hs hzΩ
      refine ⟨⟨(s : G) * z, hsz, S.mul_mem s.2 hz⟩, ?_⟩
      change ρ (s * ⟨z, hz⟩) = ρ s
      rw [map_mul, hz1, mul_one]

section Lift

variable {K : Type} [Field K] {d : ℕ} {Q : QuadraticForm K (Fin d → K)} {v : Fin d → K}
variable [CharP K 2] [Finite K] (hQ : Q.polarBilin.Nondegenerate) (hv : Q v = 1)
include hQ hv

theorem exists_lift_transvection' (u : vPerp Q v) (c : K) :
    ∃ g : symmetryCentralizer Q v,
      symmetryRestrict hQ hv g = symplecticTransvection (vQuotForm Q v) (vQuotForm_isAlt Q v)
        (Submodule.Quotient.mk u) c := by
  by_cases hc : c = 0
  · refine ⟨1, ?_⟩
    rw [map_one, hc, symplecticTransvection_zero]
  have h22 : (2 : K) = 0 := CharTwo.two_eq_zero
  obtain ⟨b, hb⟩ := FiniteField.isSquare_of_char_two (ringChar.eq K 2) (c⁻¹ + Q u)
  obtain ⟨l, hl⟩ := FiniteField.isSquare_of_char_two (ringChar.eq K 2) c
  have huv : polar Q (u : Fin d → K) v = 0 := by
    rw [polar_comm]
    exact u.2
  have hvv : polar Q v v = 0 := by rw [polar_self, hv, two_nsmul, CharTwo.add_self_eq_zero]
  set z₀ : Fin d → K := (u : Fin d → K) + b • v with hz₀def
  set z : Fin d → K := l • z₀ with hzdef
  have hz₀ : Q z₀ = c⁻¹ := by
    rw [hz₀def, QuadraticMap.map_add Q, QuadraticMap.map_smul, hv, polar_smul_right, huv,
      smul_eq_mul, smul_eq_mul, mul_zero, add_zero, mul_one]
    linear_combination hb.symm + Q u * h22
  have hz : Q z = 1 := by
    rw [hzdef, QuadraticMap.map_smul, hz₀, smul_eq_mul, ← hl, mul_inv_cancel₀ hc]
  have hzv : polar Q z v = 0 := by
    rw [hzdef, hz₀def, polar_smul_left, polar_add_left, polar_smul_left, huv, hvv, smul_zero,
      add_zero, smul_zero]
  have hsz : symmetryGL Q z ∈ symmetryCentralizer Q v := by
    refine ⟨symmetryGL_mem Q z, (mem_centralizer_symmetryGL_iff hQ hv (symmetryGL_mem Q z)).mpr ?_⟩
    rw [symmetryGL_mulVec_of_charTwo hz, hzv, zero_smul, add_zero]
  refine ⟨⟨symmetryGL Q z, hsz⟩ * ⟨symmetryGL Q v, symmetryGL_mem_symmetryCentralizer⟩, ?_⟩
  apply Units.ext
  apply LinearMap.ext
  intro x
  induction x using Submodule.Quotient.induction_on with
  | H x =>
    rw [symmetryRestrict_mk, symplecticTransvection_apply, vQuotForm_mk,
      ← Submodule.Quotient.mk_smul, ← Submodule.Quotient.mk_add, Submodule.Quotient.eq,
      Submodule.mem_comap]
    have hx : polar Q v (x : Fin d → K) = 0 := x.2
    have hxz₀ : polar Q z₀ (x : Fin d → K) = polar Q (x : Fin d → K) u := by
      rw [hz₀def, polar_add_left, polar_smul_left, hx, smul_zero, add_zero, polar_comm]
    have hact : ((((⟨symmetryGL Q z, hsz⟩ * ⟨symmetryGL Q v,
        symmetryGL_mem_symmetryCentralizer⟩ : symmetryCentralizer Q v) : GL (Fin d) K) :
          Matrix (Fin d) (Fin d) K) *ᵥ (x : Fin d → K)) =
        (x : Fin d → K) + (c * polar Q (x : Fin d → K) u) • (u : Fin d → K) +
          (c * polar Q (x : Fin d → K) u * b) • v := by
      rw [Subgroup.coe_mul, Units.val_mul, ← mulVec_mulVec, symmetryGL_mulVec_of_charTwo hv,
        hx, zero_smul, add_zero, symmetryGL_mulVec_of_charTwo hz, hzdef, polar_smul_left,
        hxz₀, hl, hz₀def]
      module
    refine Submodule.mem_span_singleton.mpr ⟨c * polar Q (x : Fin d → K) u * b, ?_⟩
    simp only [Submodule.subtype_apply, Submodule.coe_sub, Submodule.coe_add,
      Submodule.coe_smul]
    change _ = ((((⟨symmetryGL Q z, hsz⟩ * ⟨symmetryGL Q v,
        symmetryGL_mem_symmetryCentralizer⟩ : symmetryCentralizer Q v) : GL (Fin d) K) :
          Matrix (Fin d) (Fin d) K) *ᵥ (x : Fin d → K)) - _
    rw [hact]
    abel

theorem range_symmetryRestrict' :
    (symmetryRestrict hQ hv).range = bilinIsometryGroup (vQuotForm Q v) := by
  have hv0 : v ≠ 0 := by
    rintro rfl
    rw [QuadraticMap.map_zero] at hv
    exact zero_ne_one hv
  apply le_antisymm
  · rintro _ ⟨g, rfl⟩
    exact symmetryRestrict_mem hQ hv g
  · rw [alternating_transvection_generation (vQuotForm_isAlt Q v)
      (vQuotForm_nondegenerate hQ hv0), Subgroup.closure_le]
    rintro _ ⟨a, c, rfl⟩
    obtain ⟨u, rfl⟩ := Submodule.Quotient.mk_surjective _ a
    obtain ⟨g, hg⟩ := exists_lift_transvection' hQ hv u c
    exact ⟨g, hg⟩

end Lift

section Sp

variable {K : Type} [Field K] {d : ℕ} {Q : QuadraticForm K (Fin d → K)} {v : Fin d → K}

noncomputable def statedSpEquiv (n : ℕ) :
    ↥(CFSG.Open.StatedSp n K) ≃* ↥(TauCeti.GLSymplectic (Fin n) K) :=
  MulEquiv.subgroupCongr (CFSG.ClassicalGroups.Symplectic.statedSp_eq_GLSymplectic (n := n)
    (K := K))

theorem nonempty_bilinIsometryGroup_vQuotForm_equiv [CharP K 2]
    (hQ : Q.polarBilin.Nondegenerate) (hv : Q v = 1) {k : ℕ} (hd : d = 2 * k) :
    Nonempty (↥(bilinIsometryGroup (vQuotForm Q v)) ≃* ↥(CFSG.Open.StatedSp (k - 1) K)) := by
  have hv0 : v ≠ 0 := by
    rintro rfl
    rw [QuadraticMap.map_zero] at hv
    exact zero_ne_one hv
  obtain ⟨m, hm, ⟨e⟩⟩ :=
    CFSG.ComponentClassification.CatalogueBAlternatingIsometry.exists_isometryEquiv_symplectic
      (vQuotForm Q v) (vQuotForm_isAlt Q v) (vQuotForm_nondegenerate hQ hv0)
  have hfr := finrank_vQuot hQ hv
  obtain rfl : m = k - 1 := by omega
  exact ⟨((bilinIsometryGroupEquiv (vQuotForm Q v)).trans e).trans (statedSpEquiv _).symm⟩

end Sp

section Main

theorem coord_centralizer_equiv {K : Type} [Field K] [Finite K] [CharP K 2] {k : ℕ}
    (Q : QuadraticForm K (Fin (2 * k) → K)) (hQ : Q.polarBilin.Nondegenerate)
    (v : Fin (2 * k) → K) (hv : Q v = 1)
    (hidx : ∀ x y, x ∈ matrixIsometries Q → y ∈ matrixIsometries Q →
      x ∉ matrixDerived Q → y ∉ matrixDerived Q → x * y ∈ matrixDerived Q)
    (hz : symmetryGL Q v ∉ matrixDerived Q) :
    Nonempty (↥(matrixDerived Q ⊓ symmetryCentralizer Q v) ≃* CFSG.Open.StatedSp (k - 1) K) := by
  obtain ⟨e⟩ := nonempty_bilinIsometryGroup_vQuotForm_equiv hQ hv (rfl : 2 * k = 2 * k)
  let ρ : symmetryCentralizer Q v →* ↥(bilinIsometryGroup (vQuotForm Q v)) :=
    (symmetryRestrict hQ hv).codRestrict _ (symmetryRestrict_mem hQ hv)
  have hsurj : Function.Surjective ρ := by
    intro y
    have hy : (y : LinearMap.GeneralLinearGroup K (vQuot Q v)) ∈
        (symmetryRestrict hQ hv).range := by
      rw [range_symmetryRestrict' hQ hv]
      exact y.2
    obtain ⟨g, hg⟩ := hy
    exact ⟨g, Subtype.ext hg⟩
  have hρ : ∀ s, ρ s = 1 ↔ symmetryRestrict hQ hv s = 1 := fun s =>
    ⟨fun h => congrArg Subtype.val h, fun h => Subtype.ext h⟩
  have hker : ∀ s : symmetryCentralizer Q v, ρ s = 1 → s = 1 ∨ (s : GL (Fin (2 * k)) K) =
      symmetryGL Q v := by
    intro s hs
    rcases eq_one_or_eq_symmetryGL_of_restrict_eq_one hQ hv ((hρ s).mp hs) with h | h
    · exact Or.inl (Subtype.ext h)
    · exact Or.inr h
  have hz1 : ρ ⟨symmetryGL Q v, symmetryGL_mem_symmetryCentralizer⟩ = 1 := by
    rw [hρ, ← MonoidHom.mem_ker, ker_symmetryRestrict hQ hv]
    exact Subgroup.mem_zpowers _
  have hbij := bijective_restrict_of_index_two (matrixIsometries Q) (matrixDerived Q)
    (symmetryCentralizer Q v) inf_le_left hidx (symmetryGL Q v) symmetryGL_mem_symmetryCentralizer
    hz ρ hsurj hker hz1
  exact ⟨(MulEquiv.ofBijective _ hbij).trans e⟩

end Main

end CFSG.HardMathSupport.Curtis.Coordinator.PLType.OrthCoord
