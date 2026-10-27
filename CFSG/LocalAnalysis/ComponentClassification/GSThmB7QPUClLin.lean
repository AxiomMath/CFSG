module

public import CFSG.LocalAnalysis.ComponentClassification.GSThmB7QPUClLinCore
public import CFSG.LocalAnalysis.ComponentClassification.CatLeafProofX10LinRow
public import CFSG.LocalAnalysis.ComponentClassification.GSThmB7QPUClBarIso

public section

namespace CFSG.ComponentClassification.GSThmB.QPUCl

open CFSG Subgroup Matrix CFSG.Blueprint CFSG.Assembly.LowTwoRank
  CFSG.ComponentClassification.CatLeaf
open CFSG.ComponentClassification.FixedCommutingProduct (fixedSubgroup)
open CFSG.ComponentClassification.CatalogueBHigherLinearAction (innerDiagonalAction
  innerDiagonalAction_mk toGL_slConjugation)

theorem innerDiagonalAction_toGL_apply {n : ℕ} {K : Type} [Field K]
    (B : SpecialLinearGroup (Fin n) K) (x : ProjectiveSpecialLinearGroup (Fin n) K) :
    innerDiagonalAction n K (SpecialLinearGroup.toGL B) x =
      QuotientGroup.mk' (center (SpecialLinearGroup (Fin n) K)) B * x *
        (QuotientGroup.mk' (center (SpecialLinearGroup (Fin n) K)) B)⁻¹ := by
  obtain ⟨g, rfl⟩ := QuotientGroup.mk'_surjective (center (SpecialLinearGroup (Fin n) K)) x
  rw [innerDiagonalAction_mk, ← map_mul, ← map_inv, ← map_mul]
  congr 1
  apply SpecialLinearGroup.toGL_injective
  rw [toGL_slConjugation, map_mul, map_mul, map_inv]

theorem false_of_barConfig_psl {P : Type} [Group P] [Finite P] {n p f f₀ : ℕ}
    (hp : p.Prime) (hp2 : p ≠ 2) (hf : 1 ≤ f) (_h5 : 5 ≤ p ^ f)
    (hP : StatedClassicalModel P .PSL n p f₀) (h : BarConfig P p f p f) : False := by
  have hadm : StatedLieAdmissible .PSL n p f₀ := hP.1
  have hn : 2 ≤ n := hadm.2.2.1
  have hf₀ : 1 ≤ f₀ := hadm.2.1
  have hLM : LieModel P .PSL n p f₀ := Or.inl ⟨by decide, hP⟩
  have : IsSimpleGroup P := (LieType.Simplicity.fam_PSL_simplicity P n p f₀ hP).2
  have h4 := four_mul_le_factorization_of_barConfig hp2 h
  have hfac := (CatLeafProof.X10Lin.lieOrder_of_lieModel_classical (Or.inl rfl) hp2
    (by omega) hLM).2
  obtain ⟨K, _, _, hK, ⟨e⟩⟩ := CatLeafProof.nonempty_mulEquiv_psl_of_lieModel hadm hLM
  have : Finite (ProjectiveSpecialLinearGroup (Fin n) K) := Finite.of_equiv _ e.toEquiv
  have : IsSimpleGroup (ProjectiveSpecialLinearGroup (Fin n) K) := e.symm.isSimpleGroup
  have h' := BarConfig.of_mulEquiv e h
  have hQ : FixedTwoComponentsQuasisimple (ProjectiveSpecialLinearGroup (Fin n) K) :=
    FixedTwoComponentsQuasisimple.of_mulEquiv e.symm
      (CatLeafProof.X10Lin.fixedTwoComponentsQuasisimple_lin hp2 (Or.inl rfl) hadm hLM)
  obtain ⟨t, -, -, hJ⟩ := exists_component_of_barConfig hQ (center_eq_bot_of_barConfig h') h'
  obtain ⟨B, rfl⟩ := QuotientGroup.mk'_surjective (center (SpecialLinearGroup (Fin n) K)) t
  obtain ⟨hA, J', hJ'c, hJ'z, hJ'm⟩ :=
    hJ (innerDiagonalAction n K (SpecialLinearGroup.toGL B)) (innerDiagonalAction_toGL_apply B)
  rcases CatLeafProof.X10Lin.inner_psl_component_cases hp hp2 hK hadm _ hA hJ'c with
    ⟨z, hz, hzc, hzz, hz1⟩ | ⟨t', k, e', hT, hcm⟩
  · exact hz1 (hJ'z z hz hzc hzz)
  · rcases hT with ⟨k', -, hk3, -, hk⟩ | ⟨⟨r, hr⟩, hk⟩
    ·
      simp only [Prod.mk.injEq] at hk
      obtain ⟨rfl, rfl, rfl⟩ := hk
      obtain ⟨-, hk2, -⟩ := eq_of_centralModel_of_lieModel hp hp2 hf hJ'm (Or.inl rfl) hcm
      omega
    ·
      simp only [Prod.mk.injEq] at hk
      obtain ⟨rfl, rfl, rfl⟩ := hk
      obtain ⟨-, hk2, he⟩ := eq_of_centralModel_of_lieModel hp hp2 hf hJ'm (Or.inl rfl) hcm
      have hn4 : n = 4 := by omega
      subst hn4
      have hS : lieSylowExponent .PSL 4 = 6 := rfl
      rw [hfac, hS] at h4
      omega

end CFSG.ComponentClassification.GSThmB.QPUCl
