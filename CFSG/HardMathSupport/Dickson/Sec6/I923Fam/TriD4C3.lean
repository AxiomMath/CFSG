module

public import CFSG.HardMathSupport.Dickson.Sec6.I923Fam.R2Aux.TransportTop

public section

namespace CFSG.HardMathSupport.Dickson.Sec6.I923

open CFSG.Blueprint CFSG.Blueprint.Chevalley CFSG.LieType.Chevalley
open CFSG.HardMathSupport.Dickson.DefCharOuter.TrialityChar3
open CFSG.HardMathSupport.Dickson.Sec6.I923.TriD4Aux
open CFSG.HardMathSupport.Solomon.Coordinator

set_option linter.unusedSectionVars false

section Final


theorem triD4C3NoL2_holds : TriD4C3NoL2 := by
  intro f hf K _ _ _ hK σ hσ c hc hc0
  haveI := finite_graphFixedRootGroup_D4 σ
  haveI : Finite (adjointGroup Tag.G2 (fixSubfield σ)) := generated_group_finite Tag.G2 _
  rw [noL2Layer_iff_noL2Sub, fixSubgroup_conj_mul_fieldActor_eq hf hK σ hσ hc hc0]
  have hzJ := R2Aux.longElt_mem_fix hf hK σ hσ (Or.inr (Or.inr rfl)) hc
  refine noL2Sub_of_equiv
    (R2Aux.infCentralizerEquiv (fixSubgroup (fieldActor (t := TwistTag.D4) σ σ))
      (longElt hf hK σ hσ (Or.inr (Or.inr rfl)) c hc) hzJ (R2Aux.fixEquivG2 hf hK σ hσ)) ?_
  obtain ⟨h, c'', hc'', hE⟩ := R2Aux.exists_conj_g2Top hf hK σ hσ hc hc0
  rw [hE]
  refine R2Aux.noL2Sub_centralizer_conj h _ ?_
  have hcard : Nat.card (fixSubfield σ) = 3 ^ f :=
    CFSG.RankThree.PartOne.KGD.card_fixSubfield_cube Nat.prime_three hf hK σ hσ
  haveI : CharP (fixSubfield σ) 3 := inferInstance
  exact R2Aux.noL2Sub_centralizer_g2Top (K := fixSubfield σ)
    (by rw [hcard]; exact Nat.le_self_pow (by omega) 3) hc''

end Final

end CFSG.HardMathSupport.Dickson.Sec6.I923
