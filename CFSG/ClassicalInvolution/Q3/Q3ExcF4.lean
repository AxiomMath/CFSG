module

public import CFSG.ClassicalInvolution.Q3.Q3ExcAdj
public import CFSG.ClassicalInvolution.ModelFacts.ClassicalIsFundamentalF4
public import CFSG.ClassicalInvolution.Q3.Q3PlanTags

public section

namespace CFSG.ClassicalInvolution.Q3

open CFSG.Open CFSG.ClassicalInvolution CFSG.ClassicalInvolution.Generic CFSG.Blueprint.Chevalley
  CFSG.LieType.Chevalley CFSG.LieType.Steinberg.Adjoint CFSG.ClassicalInvolution.ModelFacts
  CFSG.Assembly.LowTwoRank

theorem classicalMembersFundamental3Tag_F4 : ClassicalMembersFundamental3Tag .F4 := by
  intro n hp hFT hadm L z hL hO
  obtain ⟨g, b, γ, hγ, hLeq, hclass⟩ := exc3_exists_conj_rootGroup_of_member
    (τ := .F4) (Or.inr (Or.inl rfl)) uniqIsolated_F4 hL hO
  have hlong : iform γ γ = 4 := by
    rcases iform_self_F4 hγ.1 with h2 | h4
    · exfalso
      obtain ⟨δ, hδ, hδγ, hδγ', hδker, hδ0⟩ :=
        F4_short_root_has_nonorthogonal_kernel_root (signTupleBits b) hγ.1 h2 hγ.2
      have hcls : (⟦⟨γ, hγ⟩⟧ : KernelComponent (maskChar (signTupleBits b))) =
          ⟦⟨δ, ⟨hδ, hδker⟩⟩⟧ := mk_eq_of_iform_ne_zero hδ0
      have hle := rootSubgroup_le_componentRootSpan (GaloisField 3 1)
        (⟨δ, ⟨hδ, hδker⟩⟩ : kernelRoots (maskChar (signTupleBits b)))
      rw [← hcls, hclass] at hle
      exact not_rootSubgroup_le_rootSubgroup_sup hγ.1 hδ hδγ hδγ' hle
    · exact h4
  exact ⟨g⁻¹, γ, Or.inl (isLongestRoot_f4Datum_of_iform_eq_four hγ.1 hlong), hLeq⟩

theorem simpleOddCentralizerFreeTag_F4 : SimpleOddCentralizerFreeTag .F4 := by
  intro n hp hadm s hs
  exact exc3_involutionOddCore_adjoint_eq_bot (τ := .F4) (Or.inr (Or.inl rfl)) s hs

theorem oddCentralizerFreeTag_F4 : OddCentralizerFreeTag .F4 :=
  oddCentralizerFreeTag_of_simple _ simpleOddCentralizerFreeTag_F4

end CFSG.ClassicalInvolution.Q3
