module

public import CFSG.ClassicalInvolution.Q3.Q3ExcAdj
public import CFSG.ClassicalInvolution.Q3.Q3PlanTags

public section

namespace CFSG.ClassicalInvolution.Q3

open CFSG.Open CFSG.ClassicalInvolution CFSG.ClassicalInvolution.Generic CFSG.Blueprint.Chevalley
  CFSG.LieType.Chevalley CFSG.LieType.Steinberg.Adjoint CFSG.ClassicalInvolution.ModelFacts
  CFSG.Assembly.LowTwoRank

theorem classicalMembersFundamental3Tag_E8 : ClassicalMembersFundamental3Tag .E8 := by
  intro n hp hFT hadm L z hL hO
  obtain ⟨g, b, γ, hγ, hLeq, -⟩ := exc3_exists_conj_rootGroup_of_member
    (τ := .E8) (Or.inr (Or.inr (Or.inr rfl))) uniqIsolated_E8 hL hO
  have hlong := isLongestRoot_single .E8 n 3 1 hp trivial hadm
  exact ⟨g⁻¹, γ, Or.inl (isLongestRoot_of_mem_roots_of_forall_single _ rfl
    (fun k => hlong k trivial) (mem_adjDatum_roots.2 hγ.1)), hLeq⟩

theorem simpleOddCentralizerFreeTag_E8 : SimpleOddCentralizerFreeTag .E8 := by
  intro n hp hadm s hs
  exact exc3_involutionOddCore_adjoint_eq_bot (τ := .E8) (Or.inr (Or.inr (Or.inr rfl))) s hs

theorem oddCentralizerFreeTag_E8 : OddCentralizerFreeTag .E8 :=
  oddCentralizerFreeTag_of_simple _ simpleOddCentralizerFreeTag_E8

end CFSG.ClassicalInvolution.Q3
