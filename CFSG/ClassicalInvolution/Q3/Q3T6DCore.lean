module

public import CFSG.ClassicalInvolution.Q3.Q3T6DConj
public import CFSG.ClassicalInvolution.Asc77.AscT3Final
public import CFSG.ClassicalInvolution.Q3.Q3T6DStmt

public section

set_option linter.unusedSectionVars false

namespace CFSG.ClassicalInvolution.Q3.Q3T6D

open CFSG.Open CFSG.ClassicalInvolution CFSG.ClassicalInvolution.Generic
  CFSG.ClassicalInvolution.Asc77 CFSG.ClassicalInvolution.Asc77.T3
  CFSG.ClassicalInvolution.Disconnected CFSG.ClassicalInvolution.Disconnected.AschTight
  CFSG.ClassicalInvolution.Uniform

section Core


variable {G : Type} [Group G] [Finite G] [IsSimpleGroup G] {K : Subgroup G} {z : G}

theorem aEmpty_of_core (hcore : T3Core3) (hb : Branch3 K z)
    (hΩK : HypOmegaModU (.sl2 3 1) (CoreAssembly.conjClass K)) :
    ∀ J ∈ CoreAssembly.conjClass K, AEmpty (CoreAssembly.conjClass K) J := by
  have hΩg : HypOmegaGen (CoreAssembly.conjClass K) := hypGen_of_modU hΩK
  have hKΩ : K ∈ CoreAssembly.conjClass K := CoreAssembly.mem_conjClass_self K
  have hall : ∀ J ∈ CoreAssembly.conjClass K, ∃ g : G, conjSub g K = J := by
    intro J hJ
    obtain ⟨g, rfl⟩ := hJ
    exact ⟨g, rfl⟩
  have hA : AEmpty (CoreAssembly.conjClass K) K := by
    by_contra hn
    obtain ⟨J, zK, zJ, hv⟩ := not_aEmpty_iff.mp hn
    obtain ⟨a, ha, hac, -, -, hne, g, hg, hgK⟩ := AViol.exists_swap hΩg hKΩ hall hv
    exact hcore G K z hb hΩK J zK zJ a g hv ha hac hne hgK hg
  exact aEmpty_forall_of_transitive' hΩg.conjInvariant hall hA

theorem t3Core3_of_cases (hI : CaseI3) (hih : ∀ n : ℕ, CITBelowT (.sl2 3 1) n → IH8T 3 1 n)
    (hII : T3CaseII3) : T3Core3 := by
  intro G _ _ _ K z hb hΩ J zK zJ a g hv ha haz hne hg hgz
  have hz2 : orderOf z = 2 := hb.member.orderOf_eq_two
  have hzsq : z * z = 1 := by rw [← pow_two]; exact hz2 ▸ pow_orderOf_eq_one z
  have hz1 : z ≠ 1 := fun h => by rw [h, orderOf_one] at hz2; omega
  have hzK : z = zK := (hv.hzK.unique z hb.member.mem hzsq).resolve_left hz1
  subst hzK
  by_cases hstar : aStar (CoreAssembly.conjClass K) K = CoreAssembly.conjClass K
  · exact hII G K J z zJ a g
      { branch := hb.toBranch3Core
        ih := hih _ hb.below
        hyp := hΩ
        viol := hv
        ha := ha
        haz := haz
        hne := hne
        hg := hg
        hgz := hgz
        star := hstar }
  · exact hI G K z hb hΩ J zJ hv hstar

end Core

section Main


theorem aEmptyDU_three_of_cases (hΩ : HypOmegaModDU 3 1) (hI : CaseI3)
    (hih : ∀ n : ℕ, CITBelowT (.sl2 3 1) n → IH8T 3 1 n) (hII : T3CaseII3) : AEmptyDU 3 1 := by
  intro G _ _ _ K z hb J hJ
  exact aEmpty_of_core (t3Core3_of_cases hI hih hII) (Branch3.of_dBranchU hb) (hΩ G K z hb) J hJ

end Main

end CFSG.ClassicalInvolution.Q3.Q3T6D
