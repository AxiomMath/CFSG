module

public import CFSG.LocalAnalysis.ComponentClassification.CatFC.CentA6ClPSU
public import CFSG.LocalAnalysis.ComponentClassification.CatFC.CentA6ClPSUSmallU3Bar
public import CFSG.LocalAnalysis.ComponentClassification.CatFC.CentA6ClPSUSmallU4

public section

namespace CFSG.ComponentClassification.CatFC

open CFSG Subgroup CFSG.Blueprint CFSG.Assembly.LowTwoRank
open CFSG.ComponentClassification.CatLeaf (LieOrderFormulasInput)
open CFSG.ComponentClassification.CatLeafProof (nonempty_mulEquiv_primeFormP_of_lieModel')
open CFSG.ComponentClassification.FixedCommutingProduct (fixedSubgroup)
open CFSG.LocalAnalysis.ComponentInitial CFSG.LocalAnalysis.ComponentInitial.UnitaryHigher
open CFSG.RankThree.PartOne.KCUnitaryModel (idGram)

theorem oddA6Small_PSU
    (hO : LieOrderFormulasInput) : OddA6Small .PSU := by
  apply oddA6Small_of_concrete
  intro S _ _ n p f hp hp2 hadm hm hp3 hs
  obtain ⟨K, _, h, ⟨ψ⟩⟩ := nonempty_mulEquiv_primeFormP_of_lieModel' hadm hm
  haveI : Finite K := h.finite
  refine ⟨primeFormP h ((1 : GL (Fin n) K) : Matrix (Fin n) (Fin n) K), inferInstance,
    inferInstance, ψ, ?_⟩
  intro σ D hσ hA
  subst hp3
  rcases (a6Shape_PSU_iff n f).mp hs with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩
  · exact psu_small_three_two h hO σ hσ hA
  · exact psu_small_four_one (LieModel.of_mulEquiv ψ hm) σ hσ hA

end CFSG.ComponentClassification.CatFC
