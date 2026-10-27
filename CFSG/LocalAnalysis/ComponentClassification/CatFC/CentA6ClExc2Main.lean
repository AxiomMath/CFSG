module

public import CFSG.LocalAnalysis.ComponentClassification.CatFC.CentA6ClExc2E6
public import CFSG.LocalAnalysis.ComponentClassification.CatFC.CentA6ClExc2E7
public import CFSG.LocalAnalysis.ComponentClassification.CatFC.CentA6Transport

public section

namespace CFSG.ComponentClassification.CatFC

open Subgroup CFSG CFSG.Blueprint CFSG.Blueprint.Chevalley CFSG.Assembly.LowTwoRank
  CFSG.LieType.Chevalley
open CFSG.ComponentClassification.CatLeaf (LieOrderFormulasInput)
open CFSG.ComponentClassification.FixedCommutingProduct (fixedSubgroup)

set_option linter.unusedSectionVars false


theorem oddA6Shape_E6 (_hO : LieOrderFormulasInput)
    (_hgls : CatLeafProof.GLS3OddFamilyInput .E6) : OddA6Shape .E6 := by
  refine oddA6Shape_of_concrete fun S _ _ n p f hp hp2 hadm hm => ?_
  obtain ⟨F, _, _, hF, ⟨e⟩⟩ := nonempty_mulEquiv_adjointGroup Tag.E6
    ((GH74.chevalleyExceptionalModel_of_lieModel (by decide) hm).2 :
      UntwistedChevalleyModel S Tag.E6 (p ^ f))
  refine ⟨adjointGroup Tag.E6 F, inferInstance, Finite.of_equiv S e.toEquiv, e,
    fun σ D hσ hD => ?_⟩
  exfalso
  have hσ2 : σ ^ 2 = 1 := hσ ▸ pow_orderOf_eq_one σ
  obtain ⟨hDn, hDs, hDnab, -, ⟨eD⟩⟩ := hD.normal_simple_data
  exact a6_E6_false hp hp2 hF σ hσ2 D hDn hDs hDnab eD

theorem oddA6Shape_E7 (_hO : LieOrderFormulasInput)
    (_hgls : CatLeafProof.GLS3OddFamilyInput .E7) : OddA6Shape .E7 := by
  refine oddA6Shape_of_concrete fun S _ _ n p f hp hp2 hadm hm => ?_
  obtain ⟨F, _, _, hF, ⟨e⟩⟩ := nonempty_mulEquiv_adjointGroup Tag.E7
    ((GH74.chevalleyExceptionalModel_of_lieModel (by decide) hm).2 :
      UntwistedChevalleyModel S Tag.E7 (p ^ f))
  refine ⟨adjointGroup Tag.E7 F, inferInstance, Finite.of_equiv S e.toEquiv, e,
    fun σ D hσ hD => ?_⟩
  exfalso
  have hσ2 : σ ^ 2 = 1 := hσ ▸ pow_orderOf_eq_one σ
  obtain ⟨hDn, hDs, hDnab, -, ⟨eD⟩⟩ := hD.normal_simple_data
  exact a6_E7_false hp hp2 hF σ hσ2 D hDn hDs hDnab eD

end CFSG.ComponentClassification.CatFC
