module

public import CFSG.LocalAnalysis.OddStandard.SmallF3.HypA2Leaves.A2lCl2FamE6

public noncomputable section

namespace CFSG.OddStandard.SmallF3.HypA2Leaves

open CFSG
  CFSG.ComponentClassification.CatLeafProof
  CFSG.ComponentClassification
open CFSG Subgroup Matrix CFSG.Blueprint CFSG.Assembly.LowTwoRank
  CFSG.ComponentClassification.CatLeaf
open CFSG.ComponentClassification.FixedCommutingProduct (fixedSubgroup)

section


theorem cl24_E6_involution
    {J : Type} [Group J] {n p f : ℕ} (hp : p.Prime) (hp2 : p ≠ 2)
    (hadm : StatedLieAdmissible .E6 n p f) (hm : Blueprint.LieModel J .E6 n p f)
    {α : MulAut J} (hα : orderOf α = 2) {Kc : Subgroup (fixedSubgroup α)} (hKc : IsComponent Kc) :
    Cl24Q p (fun f' => f' = f ∨ f = 2 * f') Kc := by
  obtain ⟨F, _, _, hF, ⟨e⟩⟩ := LieType.Chevalley.nonempty_mulEquiv_adjointGroup .E6
    ((GH74.chevalleyExceptionalModel_of_lieModel (t := .E6) (by decide) hm).2 :
      UntwistedChevalleyModel J .E6 (p ^ f))
  have hβ : orderOf (MulAut.congr e α) = 2 :=
    (orderOf_injective (MulAut.congr e).toMonoidHom (MulAut.congr e).injective α).trans hα
  exact cl24_odd_E6_explicit cl24_excInnerDiag_E6 cl24_oddE6GraphInput_holds hp hp2 hadm.2.1 hF _ hβ
    (fixedSubgroupCongrEquiv e α) hKc

end

end CFSG.OddStandard.SmallF3.HypA2Leaves
