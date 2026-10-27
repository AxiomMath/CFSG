module

public import CFSG.LocalAnalysis.ComponentClassification.CatalogueBAlternatingIsometryBasis
public import CFSG.LocalAnalysis.ComponentClassification.UnbalancedCatalogEvenCore
public import CFSG.LocalAnalysis.ComponentInitial.LinearIsometry
public import CFSG.LocalAnalysis.ComponentInitial.UnitaryHigherEvenOrthogonalRealization

public noncomputable section

namespace CFSG.ComponentClassification.UnbalancedCatalog

open Matrix QuadraticMap CFSG.ClassicalGroups.Orthogonal CFSG.LocalAnalysis.ComponentInitial
open CFSG.ComponentClassification.CatalogueBOrthogonalSemilinear
open CFSG.ComponentClassification.CatalogueBAlternatingIsometry (isometryGroup
  mem_isometryGroup_iff)
open CFSG.LocalAnalysis.ComponentInitial.UnitaryHigher (unitMultiplierPairs
  mem_unitMultiplierPairs_iff eq_one_of_kappa_eq_one exists_scalarPair_mul_mem kappa_scalarPair
  scalarPair_mem)

theorem oddCore_eq_bot_of_surjective {G H : Type*} [Group G] [Group H] [Finite G]
    (φ : G →* H) (hφ : Function.Surjective φ) (hH : CFSG.oddCore H = ⊥)
    (hker : ∀ x ∈ φ.ker, x ^ 2 = 1) : CFSG.oddCore G = ⊥ := by
  have : Finite H := Finite.of_surjective φ hφ
  have hle : (CFSG.oddCore G).map φ ≤ CFSG.oddCore H := by
    apply EvenCatalog.le_oddCore_of_normal ((CFSG.oddCore_normal G).map φ hφ)
    exact Odd.of_dvd_nat EvenCatalog.odd_card_oddCore (Subgroup.card_map_dvd _ φ)
  rw [hH, le_bot_iff] at hle
  rw [eq_bot_iff]
  intro q hq
  have hq1 : φ q = 1 := by
    have : φ q ∈ (CFSG.oddCore G).map φ := Subgroup.mem_map_of_mem φ hq
    rwa [hle, Subgroup.mem_bot] at this
  rw [Subgroup.mem_bot]
  by_contra hne
  exact EvenCatalog.not_mem_oddCore_of_sq_eq_one hne (hker q hq1) hq

@[expose] def bilinIsometryGroupEquiv {K V : Type*} [Field K] [AddCommGroup V] [Module K V]
    (B : LinearMap.BilinForm K V) : bilinIsometryGroup B ≃* isometryGroup B :=
  ((LinearMap.GeneralLinearGroup.generalLinearEquiv K V).subgroupMap (bilinIsometryGroup B)).trans
    (MulEquiv.subgroupCongr (by
      ext g
      constructor
      · rintro ⟨h, hh, rfl⟩
        exact (mem_isometryGroup_iff B _).mpr hh
      · intro hg
        refine ⟨(LinearMap.GeneralLinearGroup.generalLinearEquiv K V).symm g, ?_,
          (LinearMap.GeneralLinearGroup.generalLinearEquiv K V).apply_symm_apply g⟩
        exact (mem_isometryGroup_iff B g).mp hg))

variable {K : Type} [Field K] {d : ℕ} {Q : QuadraticForm K (Fin d → K)}

theorem inclusion_mem_unitMultiplierPairs (g : matrixIsometries Q) :
    matrixIsometryInclusion Q g ∈ unitMultiplierPairs Q := fun v => by
  rw [matrixIsometryInclusion_val, coordinateSemilinearMap_inl]
  exact (mem_matrixIsometries_iff Q g.val).mp g.2 v

section Regular

variable [CharP K 2] (hQ : Q.polarBilin.Nondegenerate)
  (hT : ∃ T : Submodule K (Fin d → K), Module.finrank K T = 3 ∧ ∀ x ∈ T, Q x = 0)
  (hE : ⁅TauCeti.QuadraticMap.orthogonalGroup Q, TauCeti.QuadraticMap.orthogonalGroup Q⁆ =
    elementaryGroup Q) (hd : 1 ≤ d)
include hQ hT hE hd

theorem kappa_eq_of_unit {g h : similarityPairs Q} (hg : g ∈ unitMultiplierPairs Q)
    (hh : h ∈ unitMultiplierPairs Q)
    (heq : matrixProjectiveConjugationHom Q g = matrixProjectiveConjugationHom Q h) : g = h := by
  have := eq_one_of_kappa_eq_one Q hQ hT hE hd (mul_mem hg (inv_mem hh))
    (by rw [map_mul, map_inv, heq, mul_inv_cancel])
  exact mul_inv_eq_one.mp this

theorem kappa_inclusion_injective :
    Function.Injective ((matrixProjectiveConjugationHom Q).comp (matrixIsometryInclusion Q)) :=
  fun g h heq => matrixIsometryInclusion_injective Q (kappa_eq_of_unit hQ hT hE hd
    (inclusion_mem_unitMultiplierPairs g) (inclusion_mem_unitMultiplierPairs h) heq)

omit hQ hT hE hd in
theorem exists_unit_rep [Finite K] {x : MulAut (matrixProjectiveDerived Q)}
    (hx : x ∈ matrixProjectiveImage Q) :
    ∃ g ∈ unitMultiplierPairs Q, matrixProjectiveConjugationHom Q g = x := by
  obtain ⟨g, rfl⟩ := hx
  obtain ⟨b, hb⟩ := exists_scalarPair_mul_mem Q g
  exact ⟨_, hb, by rw [map_mul, kappa_scalarPair, one_mul]⟩

end Regular

theorem kappa_derived_eq_conj (g : matrixDerived Q) :
    matrixProjectiveConjugationHom Q (matrixDerivedInclusion Q g) =
      MulAut.conj (matrixProjectiveProjection Q g) := by
  apply MulEquiv.ext
  intro x
  obtain ⟨A, rfl⟩ := matrixProjectiveProjection_surjective Q x
  rw [MulAut.conj_apply]
  change matrixProjectiveConjugation Q _ (matrixProjectiveProjection Q A) = _
  rw [matrixProjectiveConjugation_mk, ← map_mul, ← map_inv, ← map_mul]
  congr 1

end CFSG.ComponentClassification.UnbalancedCatalog
