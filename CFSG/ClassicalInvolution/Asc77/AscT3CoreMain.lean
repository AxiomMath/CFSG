module

public import CFSG.ClassicalInvolution.Asc77.AscT3CoreTight
public import CFSG.ClassicalInvolution.Asc77.AscT3CIIStmt

public section

namespace CFSG.ClassicalInvolution.Asc77.T3Core

open CFSG.Open CFSG.ClassicalInvolution CFSG.ClassicalInvolution.Generic
  CFSG.ClassicalInvolution.Asc77 CFSG.ClassicalInvolution.Asc77.T3
  CFSG.ClassicalInvolution.Disconnected CFSG.ComponentClassification.AS76b

variable {p f : ℕ} [Fact p.Prime]

theorem t3Core_of_cases (h4 : Asc75Theorem4) (hall : IHAllD p f) (hih : IHInterface8 p)
    (hII : T3CII.T3CaseII p f) : T3Core p f := by
  intro G _ _ _ K z hb hΩ J zK zJ a g hv ha haz hne hg hgz
  have hKΩ : K ∈ CoreAssembly.conjClass K := CoreAssembly.mem_conjClass_self K
  have hz2 : orderOf z = 2 := hb.member.orderOf_eq_two
  have hzsq : z * z = 1 := by rw [← pow_two]; exact hz2 ▸ pow_orderOf_eq_one z
  have hz1 : z ≠ 1 := fun h => by rw [h, orderOf_one] at hz2; omega
  have hzK : z = zK := (hv.hzK.unique z hb.member.mem hzsq).resolve_left hz1
  subst hzK
  by_cases hstar : aStar (CoreAssembly.conjClass K) K = CoreAssembly.conjClass K
  · exact hII G K J z zJ a g
      { branch := hb
        below := hall G K z hb
        ih := hih _ (hall G K z hb)
        hyp := hΩ
        viol := hv
        ha := ha
        haz := haz
        hne := hne
        hg := hg
        hgz := hgz
        star := hstar }
  · refine caseI_false hb.odd hb.five h4 hb.nonabelian hΩ hKΩ hv ?_ hb.below hstar
    intro M hM
    obtain ⟨g', rfl⟩ := hM
    exact ⟨g', rfl⟩

theorem aEmptyD_of_cases (h62 : L6_2 p f) (hΩ : HypOmegaModD p f) (h4 : Asc75Theorem4)
    (hall : IHAllD p f) (hih : IHInterface8 p) (hII : T3CII.T3CaseII p f) : AEmptyD p f :=
  aEmptyBranch_of_core h62 (t3Core_of_cases h4 hall hih hII) hΩ

end CFSG.ClassicalInvolution.Asc77.T3Core
