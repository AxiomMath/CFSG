module

public import CFSG.LocalAnalysis.ComponentClassification.CatLeafProofX10LinDispatch
public import CFSG.LocalAnalysis.ComponentInitial.UnitaryHigherPrimeFormRealization
public import Certificates.Kernel.ThCent.Leaves

public section

namespace CFSG.ComponentClassification.GSThmB.Pump516

open CFSG Subgroup Matrix CFSG.Assembly.LowTwoRank CFSG.ComponentClassification.CatLeafProof.X10Lin
open CFSG.ComponentClassification.FixedCommutingProduct (fixedSubgroup)
open CFSG.ComponentClassification.CatalogueBHigherLinearAction
open CFSG.LocalAnalysis.ComponentInitial.UnitaryHigher
open CFSG.RankThree.PartOne.KCUnitaryModel (idGram)

theorem congr_conj {J J' : Type} [Group J] [Group J'] (e : J ≃* J') (t : J) :
    MulAut.congr e (MulAut.conj t) = MulAut.conj (e t) := by
  ext x
  simp [MulAut.congr_apply]

theorem conj_mk_eq_innerDiagonalAction {n : ℕ} {K : Type} [Field K]
    (g : SpecialLinearGroup (Fin n) K) :
    MulAut.conj ((QuotientGroup.mk' (center (SpecialLinearGroup (Fin n) K)) g :
        ProjectiveSpecialLinearGroup (Fin n) K)) =
      innerDiagonalAction n K (SpecialLinearGroup.toGL g) := by
  ext y
  obtain ⟨h, rfl⟩ := QuotientGroup.mk'_surjective (center (SpecialLinearGroup (Fin n) K)) y
  rw [innerDiagonalAction_mk, MulAut.conj_apply, ← map_mul, ← map_inv, ← map_mul]
  congr 1
  apply Subtype.ext
  rw [slConjugation_matrix]
  simp [Matrix.inv_def, g.2]

theorem psl_inner_component_cases {J : Type} [Group J] {n p f : ℕ} (hp : p.Prime) (hp2 : p ≠ 2)
    (hadm : StatedLieAdmissible .PSL n p f) (hm : Blueprint.LieModel J .PSL n p f) {t : J}
    (ht : orderOf (MulAut.conj t) = 2) {Kc : Subgroup (fixedSubgroup (MulAut.conj t))}
    (hKc : IsComponent Kc) : ComponentCases p (linInnerTuples n f) Kc := by
  obtain ⟨K, _, _, hK, ⟨e⟩⟩ := CatLeafProof.nonempty_mulEquiv_psl_of_lieModel hadm hm
  obtain ⟨g, hg⟩ := QuotientGroup.mk'_surjective (center (SpecialLinearGroup (Fin n) K)) (e t)
  have hγ : MulAut.congr e (MulAut.conj t) =
      innerDiagonalAction n K (SpecialLinearGroup.toGL g) := by
    rw [← conj_mk_eq_innerDiagonalAction, hg, congr_conj]
  have hβ : orderOf (innerDiagonalAction n K (SpecialLinearGroup.toGL g)) = 2 := by
    rw [← hγ]
    exact (orderOf_injective (MulAut.congr e).toMonoidHom (MulAut.congr e).injective _).trans ht
  exact componentCases_of_component_equiv ((CatLeafProof.fixedSubgroupCongrEquiv e _).trans
    (MulEquiv.subgroupCongr (congrArg fixedSubgroup hγ)))
    (fun L hL => inner_psl_component_cases hp hp2 hK hadm _ hβ hL) hKc

theorem psu_inner_component_cases {J : Type} [Group J] {n p f : ℕ} (hp2 : p ≠ 2)
    (hadm : StatedLieAdmissible .PSU n p f) (hm : Blueprint.LieModel J .PSU n p f) {t : J}
    (ht : orderOf (MulAut.conj t) = 2) {Kc : Subgroup (fixedSubgroup (MulAut.conj t))}
    (hKc : IsComponent Kc) : ComponentCases p (linUInnerTuples n f) Kc := by
  obtain ⟨K, _, h, ⟨ψ⟩⟩ := CatLeafProof.nonempty_mulEquiv_primeFormP_of_lieModel' hadm hm
  obtain ⟨s, hs⟩ := QuotientGroup.mk_surjective (ψ t)
  let A : primeFormUnitary h (idGram K n) := ⟨(s : GL (Fin n) K), s.2.1⟩
  have hc : primeFormConjHom h (idGram K n) A =
      MulAut.conj (s : primeFormP h (idGram K n)) :=
    primeFormConjHom_eq_conj h (idGram K n) s
  have hγ : MulAut.congr ψ (MulAut.conj t) = primeFormConjHom h (idGram K n) A := by
    rw [hc, congr_conj, hs]
  have hβ : orderOf (primeFormConjHom h (idGram K n) A) = 2 := by
    rw [← hγ]
    exact (orderOf_injective (MulAut.congr ψ).toMonoidHom (MulAut.congr ψ).injective _).trans ht
  exact componentCases_of_component_equiv ((CatLeafProof.fixedSubgroupCongrEquiv ψ _).trans
    (MulEquiv.subgroupCongr (congrArg fixedSubgroup hγ)))
    (fun L hL => inner_psu_component_cases h hp2 hadm _ hβ hL) hKc

end CFSG.ComponentClassification.GSThmB.Pump516
