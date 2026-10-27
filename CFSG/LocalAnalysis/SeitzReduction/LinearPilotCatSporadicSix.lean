module

public import CFSG.Sporadic.ThSchreier.NodeInnerInvolution
public import CFSG.Sporadic.ThSchreier.ThSchreierCase
public import CFSG.LocalAnalysis.ComponentClassification.RestrictedSporBasic
public import CFSG.LocalAnalysis.ComponentClassification.CatLeafInputs
public import CFSG.LocalAnalysis.SeitzReduction.F4PilotCatEvenInner

public section

set_option linter.unusedSectionVars false

namespace CFSG.SeitzReduction.LinearPilot

open CFSG Subgroup CFSG.Blueprint CFSG.Assembly.LowTwoRank
open CFSG.Open (ordA)
open CFSG.ComponentClassification.FixedCommutingProduct (fixedSubgroup)
open CFSG.ComponentClassification.CatLeaf (MonsterInnerInput MonsterLocalComponentsInput
  isComponent_map_mulEquiv mulAut_conj_injective_of_simple)

section Orders

theorem false_of_th_component {S : Type} [Group S] [Finite S] (hS : IsSimpleGroup S)
    (hna : ∃ a b : S, a * b ≠ b * a) (e : S ≃* NativeSporadic.Carrier .Th) {σ : MulAut S}
    (hσ : orderOf σ = 2) {D : Subgroup (fixedSubgroup σ)} (hD : IsComponent D) : False := by
  have := hS
  have hinn : σ ∈ ComponentClassification.OuterAutomorphisms.inner S := by
    rw [(Sporadic.ThSchreier.ctuc_Th_full_automorphism_group.2 S ⟨e⟩).1]
    exact Subgroup.mem_top σ
  obtain ⟨u, rfl⟩ := hinn
  have hu : orderOf u = 2 := by
    rw [← orderOf_injective _ (mulAut_conj_injective_of_simple hna) u]
    exact hσ
  let φ := MulEquiv.subgroupCongr (F4Pilot.fixedSubgroup_conj u)
  have hB := isComponent_map_mulEquiv φ hD
  have hchar :=
    ((Sporadic.ThSchreier.ctuc_Th_inner_involution_centralizers_characteristic_two).2.2 S
      ⟨e⟩).1 u hu
  exact ComponentClassification.RestrictedStd.Spor.compsSatisfy_of_charP hchar.1
    (fun (_ : Type) [Group _] => False) _ hB

end Orders

end CFSG.SeitzReduction.LinearPilot
