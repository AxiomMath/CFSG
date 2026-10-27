module

public import CFSG.LocalAnalysis.OddStandard.HigherRank.LinUnit.LUBlockPSU
public import CFSG.LocalAnalysis.OddStandard.HigherRank.LinUnit.LUMain

public noncomputable section

namespace CFSG.OddStandard.HigherRank.LinUnit

open CFSG Subgroup Matrix CFSG.ASVolI.ChIJK CFSG.Assembly.LowTwoRank CFSG.ComponentClassification
open CFSG.ComponentClassification.CatLeafProof
open CFSG.ComponentClassification.FixedCommutingProduct (fixedSubgroup)
open CFSG.LocalAnalysis.ComponentInitial.UnitaryHigher
open CFSG.RankThree.PartOne.KCUnitaryModel (idGram)

theorem psu_inner_hasFourElt {J : Type} [Group J] {n f : ℕ}
    (hadm : StatedLieAdmissible .PSU n 3 f) (hm : Blueprint.LieModel J .PSU n 3 f) {t : J}
    (ht : orderOf (MulAut.conj t) = 2) {Kc : Subgroup (fixedSubgroup (MulAut.conj t))}
    (hKc : IsComponent Kc) : HasFourElt Kc := by
  obtain ⟨K, _, h, ⟨ψ⟩⟩ := nonempty_mulEquiv_primeFormP_of_lieModel' hadm hm
  obtain ⟨s, hs⟩ := QuotientGroup.mk_surjective (ψ t)
  let A : primeFormUnitary h (idGram K n) := ⟨(s : GL (Fin n) K), s.2.1⟩
  have hc : primeFormConjHom h (idGram K n) A =
      MulAut.conj (s : primeFormP h (idGram K n)) :=
    primeFormConjHom_eq_conj h (idGram K n) s
  have hγ : MulAut.congr ψ (MulAut.conj t) = primeFormConjHom h (idGram K n) A := by
    rw [hc, lu_congr_conj, hs]
  have hβ : orderOf (primeFormConjHom h (idGram K n) A) = 2 := by
    rw [← hγ]
    exact (orderOf_injective (MulAut.congr ψ).toMonoidHom (MulAut.congr ψ).injective _).trans ht
  exact hasFourElt_of_component_equiv ((luFixedEquiv ψ _).trans
    (MulEquiv.subgroupCongr (congrArg fixedSubgroup hγ)))
    (fun L hL => inner_psu_hasFourElt h hadm _ hβ hL) hKc

theorem isComponentIn_hasFourElt_psu {Y : Type} [Group Y] [Finite Y] [IsSimpleGroup Y]
    {n r : ℕ} (hm : Blueprint.LieModel Y .PSU n 3 r) {v : Y} (hv : orderOf v = 2)
    {C : Subgroup Y} (hC : IsComponentIn C (Subgroup.centralizer {v})) : HasFourElt C := by
  obtain ⟨Kc, hKc, ⟨e⟩⟩ := exists_component_fixedSubgroup hC
  have hv' := orderOf_conj_eq_two (exists_noncommuting_of_isComponentIn hC) hv
  exact (psu_inner_hasFourElt hm.admissible hm hv' hKc).of_mulEquiv e

end CFSG.OddStandard.HigherRank.LinUnit
