module

public import CFSG.HardMathSupport.Solomon.LocalBalance.Prop42CaseThreeProof
public import CFSG.Timmesfeld.Orders.Classical

public section

namespace CFSG.HardMathSupport.Solomon.Coordinator

open scoped commutatorElement

theorem inputD4Two_holds : CFSG.HardMathSupport.Solomon.LocalBalance.CaseThreeNs.InputD4Two := by
  intro X _ _ h
  have hs := (CFSG.ClassicalGroups.Orthogonal.isSimpleGroup_of_statedClassicalModel_POmegaPlus
    X 4 2 1 h).2
  have hcard : Nat.card X = 174182400 := by
    have := (CFSG.Timmesfeld.card_statedClassicalModel_two (t := .POmegaPlus) (n := 4) (f := 1)
      h).2.2.2.1 rfl
    rw [this]
    decide
  have hnab : ∃ a b : X, a * b ≠ b * a := by
    by_contra hc
    push Not at hc
    have hprime := @IsSimpleGroup.prime_card X ⟨fun a b => hc a b⟩ hs
    rw [hcard] at hprime
    exact absurd hprime (by norm_num)
  have : IsSimpleGroup X := hs
  have hZ : Subgroup.center X = ⊥ := (CFSG.LocalCores.isQuasisimple_of_isSimpleGroup hnab).2
  have hcomm : commutator X = ⊤ := by
    rcases IsSimpleGroup.eq_bot_or_eq_top_of_normal (commutator X) with h1 | h1
    · exfalso
      obtain ⟨a, b, hab⟩ := hnab
      apply hab
      have hm : ⁅a, b⁆ ∈ commutator X :=
        Subgroup.commutator_mem_commutator (Subgroup.mem_top a) (Subgroup.mem_top b)
      rw [h1, Subgroup.mem_bot, commutatorElement_eq_one_iff_mul_comm] at hm
      exact hm
    · exact h1
  let e : X ⧸ Subgroup.center X ≃* X :=
    (QuotientGroup.quotientMulEquivOfEq hZ).trans QuotientGroup.quotientBot
  exact ⟨⟨hcomm, e.isSimpleGroup⟩, hs, by rw [hcard]; norm_num⟩

end CFSG.HardMathSupport.Solomon.Coordinator
