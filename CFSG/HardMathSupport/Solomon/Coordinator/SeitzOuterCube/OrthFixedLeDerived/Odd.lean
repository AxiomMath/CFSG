module

public import CFSG.RankThree.PartOne.KC.OrthogonalSubfieldBY
public import CFSG.HardMathSupport.Solomon.Coordinator.SeitzOuterCube.OrthFixedLeDerived.BaseChange

public section

open scoped commutatorElement

namespace CFSG.HardMathSupport.Solomon.Coordinator.SeitzOuterCube

open CFSG.RankThree.PartOne.KCOrthogonalSubfield
  CFSG.ComponentClassification.CatalogueBOrthogonalSemilinear
  CFSG.ClassicalGroups.Orthogonal CFSG.ClassicalInvolution CFSG.RankThree.Classical2 TauCeti

section Derived

variable {K V : Type*} [Field K] [AddCommGroup V] [Module K V] [FiniteDimensional K V]
  [Finite K] [Invertible (2 : K)] {Q : QuadraticForm K V}

theorem detSpinorNorm_eq_one_of_mem_orthDerived (hQ : Q.Nondegenerate) {g : V ≃ₗ[K] V}
    (hg : g ∈ orthDerived Q) (hgO : g ∈ TauCeti.QuadraticMap.orthogonalGroup Q) :
    detSpinorNorm hQ ⟨g, hgO⟩ = 1 := by
  have hle : orthDerived Q ≤ (detSpinorNorm hQ).ker.map
      (TauCeti.QuadraticMap.orthogonalGroup Q).subtype := by
    rw [orthDerived, Subgroup.commutator_le]
    intro a ha b hb
    refine ⟨⁅(⟨a, ha⟩ : TauCeti.QuadraticMap.orthogonalGroup Q), ⟨b, hb⟩⁆, ?_, rfl⟩
    rw [SetLike.mem_coe, MonoidHom.mem_ker, map_commutatorElement,
      commutatorElement_eq_one_iff_mul_comm]
    exact mul_comm (detSpinorNorm hQ ⟨a, ha⟩) (detSpinorNorm hQ ⟨b, hb⟩)
  obtain ⟨g', hg', hg'g⟩ := hle hg
  have : g' = ⟨g, hgO⟩ := Subtype.ext hg'g
  rw [← this]
  exact hg'

end Derived

section Main

variable {K : Type} [Field K] [Finite K] (k : Subfield K) {d : ℕ}
  {Q₀ : QuadraticForm k (Fin d → k)} {Q : QuadraticForm K (Fin d → K)}

theorem subfieldFixedGroup_le_derivedImage_of_odd (h2 : (2 : K) ≠ 0)
    (hext : IsExtension k Q₀ Q) (hnd₀ : (QuadraticMap.polarBilin Q₀).Nondegenerate)
    (hT₀ : ∃ U : Submodule k (Fin d → k), Module.finrank k U = 3 ∧ ∀ u ∈ U, Q₀ u = 0)
    (hnd : (QuadraticMap.polarBilin Q).Nondegenerate) (hodd : Odd (Module.finrank k K)) :
    subfieldFixedGroup k Q₀ Q ≤ subfieldDerivedImage k hext := by
  classical
  have : Finite k := Finite.of_injective (algebraMap k K) (algebraMap k K).injective
  letI : Invertible (2 : K) := invertibleOfNonzero h2
  letI : Invertible (2 : k) := invertibleOfNonzero (two_ne_zero_of_subfield k h2)
  have hnd₀' : Q₀.Nondegenerate := QuadraticMap.nondegenerate_polar_iff.mp hnd₀
  have hnd' : Q.Nondegenerate := QuadraticMap.nondegenerate_polar_iff.mp hnd
  rintro _ ⟨y, hy, rfl⟩
  obtain ⟨x, hx, hxy⟩ : ∃ x ∈ matrixIsometries Q₀, glIncl k x = y.val := hy
  have hyD : matrixLinearIso y.val ∈ orthDerived Q := by
    rw [← CFSG.RankThree.PartOne.KCOrthogonalAut.map_matrixDerived Q]
    exact ⟨y.val, y.2, rfl⟩
  have hyO : matrixLinearIso y.val ∈ TauCeti.QuadraticMap.orthogonalGroup Q :=
    matrixDerived_le_isometries Q y.2
  have hK : detSpinorNorm hnd' (orthIncl k hext ⟨matrixLinearIso x, hx⟩) = 1 := by
    have : orthIncl k hext ⟨matrixLinearIso x, hx⟩ = ⟨matrixLinearIso y.val, hyO⟩ := by
      apply Subtype.ext
      show linIncl k (matrixLinearIso x) = matrixLinearIso y.val
      rw [linIncl_matrixLinearIso, hxy]
    rw [this]
    exact detSpinorNorm_eq_one_of_mem_orthDerived hnd' hyD hyO
  rw [detSpinorNorm_orthIncl k hext hnd₀' hnd'] at hK
  have hk : detSpinorNorm hnd₀' ⟨matrixLinearIso x, hx⟩ = 1 :=
    detSquareClassMap_injective k hodd (hK.trans (map_one (detSquareClassMap k)).symm)
  obtain ⟨P, hP⟩ := exists_hyp_triple hnd₀ hT₀
  have hE := (orthogonalGroup_index_four hnd₀ (hP 0 1 (by decide)) (hP 0 2 (by decide))
    (hP 1 2 (by decide))).2 ⟨matrixLinearIso x, hx⟩
  have hxE : matrixLinearIso x ∈ elementaryGroup Q₀ := hE.mpr hk
  have hxD : x ∈ matrixDerived Q₀ := by
    have h := hxE
    rw [← (CFSG.RankThree.Classical.orthDerived_eq_and_le_closure hnd₀ hT₀).1,
      ← CFSG.RankThree.PartOne.KCOrthogonalAut.map_matrixDerived Q₀] at h
    obtain ⟨x', hx', hx'x⟩ := h
    have : x' = x := matrixLinearIso.injective hx'x
    exact this ▸ hx'
  refine ⟨matrixProjectiveProjection Q₀ ⟨x, hxD⟩, ?_⟩
  rw [incl_mk]
  congr 1
  exact Subtype.ext hxy

end Main

end CFSG.HardMathSupport.Solomon.Coordinator.SeitzOuterCube
