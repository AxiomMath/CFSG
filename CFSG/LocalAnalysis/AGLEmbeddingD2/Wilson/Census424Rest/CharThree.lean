module

public import CFSG.RankThree.PartTwo.Sec4.Item423Res3ProofMcL
public import CFSG.RankThree.PartTwo.Sec15.Item152Proof

public section

namespace CFSG.AGLEmbeddingD2.Wilson.Census424Rest

open CFSG CFSG.RankThree CFSG.RankThree.LocalRank CFSG.RankThree.PartTwo
  CFSG.RankThree.PartTwo.Sec4

theorem false_of_mem_thetaComponents_charThree {C : Type*} [Group C] [Finite C]
    (hC : IsCharacteristicP 3 C) {K : Subgroup C} (hK : K ∈ thetaComponents 3 C) : False := by
  have : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  obtain ⟨-, hsub, hq⟩ := hK
  have hKc : IsCharacteristicP 3 K := Sec15.isCharacteristicP_of_isSubnormal hC hsub
  have hθ : aschbacherSolvableCore 3 K = ⊥ := Res423Three.core_eq_bot_of_isCharacteristicP hKc
  have hqK : CFSG.IsQuasisimple K :=
    CFSG.LocalCores.isQuasisimple_of_mulEquiv
      ((QuotientGroup.quotientMulEquivOfEq hθ).trans (QuotientGroup.quotientBot (G := K))) hq
  have hcomp : CFSG.IsComponent (⊤ : Subgroup K) :=
    ⟨CFSG.LocalCores.isQuasisimple_of_mulEquiv (Subgroup.topEquiv (G := K)).symm hqK,
      Subgroup.IsSubnormal.top⟩
  have hle : (⊤ : Subgroup K) ≤ CFSG.layer K := le_sSup hcomp
  rw [CFSG.layer_eq_bot_of_isCharacteristicP K 3 hKc, top_le_iff] at hle
  have : Nontrivial K := CFSG.LocalCores.isQuasisimple_nontrivial hqK
  exact (bot_ne_top (α := Subgroup K)) hle

theorem census424_of_charThree {X : Type} [Group X] [Finite X]
    (h : ∀ c : X, orderOf c = 3 → IsCharacteristicP 3 ↥(Subgroup.centralizer ({c} : Set X))) :
    Census424 X := by
  intro D c d K hcfg
  exfalso
  have hc3 : c ^ 3 = 1 := hcfg.maximal.prop.2 c hcfg.c_mem
  have hord : orderOf c = 3 := orderOf_eq_prime hc3 hcfg.c_ne_one
  exact false_of_mem_thetaComponents_charThree (h c hord)
    (mem_thetaComponentsIn_iff.mp hcfg.mem_thetaComponentsIn).2

end CFSG.AGLEmbeddingD2.Wilson.Census424Rest
