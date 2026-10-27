module

public import CFSG.LocalAnalysis.OddStandard.SmallF3.HypA2Leaves.A2lTCEvenBasic
public import CFSG.LocalAnalysis.ComponentClassification.CatLeafProofEvenE6
public import CFSG.LocalAnalysis.ComponentClassification.CatLeafProofEvenTriality

public section

namespace CFSG.OddStandard.SmallF3.HypA2Leaves

open CFSG Subgroup CFSG.Blueprint CFSG.Blueprint.Chevalley CFSG.LieType.Chevalley
  CFSG.Assembly.LowTwoRank CFSG.ComponentClassification CFSG.ComponentClassification.CatLeaf
  CFSG.ComponentClassification.CatLeafProof
open CFSG.ComponentClassification.FixedCommutingProduct (fixedSubgroup)
open CFSG.ComponentClassification.OuterAutomorphisms (inner)

theorem a2l_evenTCOuter_E6
    (hO : LieOrderFormulasInput) : EvenTCOuter .E6 := by
  intro K _ n f hadm hm α hα2 hαo P hP
  have hf : 1 ≤ f := hadm.2.1
  have hu : UntwistedChevalleyModel K .E6 (2 ^ f) :=
    (GH74.chevalleyExceptionalModel_of_lieModel (by decide) hm).2
  obtain ⟨F, _, _, hF, ⟨e⟩⟩ := nonempty_mulEquiv_adjointGroup .E6 hu
  have : Finite (ModGL .E6 F) := finite_modGL
  have : Finite K := Finite.of_equiv _ e.symm.toEquiv
  have hα : α ^ 2 = 1 := hα2 ▸ pow_orderOf_eq_one α
  set β := MulAut.congr e α with hβdef
  have hβ2 : β ^ 2 = 1 := by rw [hβdef, ← map_pow, hα, map_one]
  have hβo : β ∉ inner (adjointGroup .E6 F) := by
    rw [hβdef, LocalAnalysis.ComponentInitial.FixedFourGroup.congr_mem_inner_iff]
    exact hαo
  obtain ⟨τ', n', f', hτ', hadm', hm'⟩ :=
    even_E6_outer_lieModel_tag hf hF β hβ2 hβo (fixedSubgroupCongrEquiv e α) hP
  have hne : τ' ≠ .PSU := by
    rcases hτ' with rfl | rfl | rfl <;> decide
  exact EvenTCConc.of_model_ne hO hadm' hm' hne

theorem a2l_evenTCOuter_twistedE6
    (hO : LieOrderFormulasInput) : EvenTCOuter .twistedE6 := by
  intro K _ n f hadm hm α hα2 hαo P hP
  have hf : 1 ≤ f := hadm.2.1
  have htw : TwistedChevalleyModel K .E6 (2 ^ f) :=
    (GH74.chevalleyExceptionalModel_of_lieModel (by decide) hm).2
  obtain ⟨M, _, _, σ, hM, hσ, ⟨e⟩⟩ :=
    exists_mulEquiv_graphFixedRootGroup_card .E6 Nat.prime_two hf htw
  have : Finite (ModGL TwistTag.E6.tag M) := finite_modGL
  have : Finite K := Finite.of_equiv _ e.symm.toEquiv
  have hα : α ^ 2 = 1 := hα2 ▸ pow_orderOf_eq_one α
  set β := MulAut.congr e α with hβdef
  have hβ2 : β ^ 2 = 1 := by rw [hβdef, ← map_pow, hα, map_one]
  have hβo : β ∉ inner (graphFixedRootGroup TwistTag.E6 M σ.toRingHom) := by
    rw [hβdef, LocalAnalysis.ComponentInitial.FixedFourGroup.congr_mem_inner_iff]
    exact hαo
  obtain ⟨hadm', hm'⟩ :=
    even_twistedE6_outer_lieModel hf hM σ hσ β hβ2 hβo (fixedSubgroupCongrEquiv e α) hP
  exact EvenTCConc.of_model_ne hO hadm' hm' (by decide)

theorem a2l_evenTCOuter_trialityD4
    (hO : LieOrderFormulasInput) : EvenTCOuter .trialityD4 := by
  intro K _ n f hadm hm α hα2 hαo P hP
  have hf : 1 ≤ f := hadm.2.1
  have htw : TwistedChevalleyModel K .D4 (2 ^ f) :=
    (GH74.chevalleyExceptionalModel_of_lieModel (by decide) hm).2
  obtain ⟨M, _, _, σ, hM, hσ, ⟨e⟩⟩ :=
    exists_mulEquiv_graphFixedRootGroup_card .D4 Nat.prime_two hf htw
  have : Finite (ModGL TwistTag.D4.tag M) := finite_modGL
  have : Finite K := Finite.of_equiv _ e.symm.toEquiv
  have hα : α ^ 2 = 1 := hα2 ▸ pow_orderOf_eq_one α
  set β := MulAut.congr e α with hβdef
  have hβ2 : β ^ 2 = 1 := by rw [hβdef, ← map_pow, hα, map_one]
  have hβo : β ∉ inner (graphFixedRootGroup TwistTag.D4 M σ.toRingHom) := by
    rw [hβdef, LocalAnalysis.ComponentInitial.FixedFourGroup.congr_mem_inner_iff]
    exact hαo
  obtain ⟨e', hadm', hL⟩ :=
    even_triality_outer_lieModel hf hM σ hσ β hβ2 hβo (fixedSubgroupCongrEquiv e α) hP
  exact EvenTCConc.of_model_ne hO hadm' hL (by decide)

end CFSG.OddStandard.SmallF3.HypA2Leaves
