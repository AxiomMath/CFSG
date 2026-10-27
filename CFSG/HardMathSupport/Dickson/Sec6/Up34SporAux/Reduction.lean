module

public import CFSG.HardMathSupport.Dickson.Sec6.Up34SporAux.Config
public import CFSG.HardMathSupport.Dickson.Sec6.Up34Aux.Descent
public import CFSG.HardMathSupport.Solomon.Coordinator.B3SporGen
public import CFSG.RankThree.PartOne.CTP.StrongPGlue

public section

namespace CFSG.HardMathSupport.Dickson.Sec6

open CFSG.Open CFSG.LocalAnalysis.GLTheoremB CFSG.HardMathSupport.Solomon.Coordinator
  CFSG.HardMathSupport.Solomon.UniquenessMaximal CFSG.HardMathSupport.Solomon.LocalBalance
  CFSG.HardMathSupport.Timmesfeld.Coordinator CFSG.ComponentClassification.OuterAutomorphisms
  CFSG.RankThree.PartOne.StrongP CFSG.Blueprint

@[expose] def SporL34Free (name : TauCeti.SporadicName) : Prop :=
  ∀ (S : Type) [Group S] [Finite S] [IsSimpleGroup S], (∃ a b : S, a * b ≠ b * a) →
    Nonempty (S ≃* (TauCeti.CFSGIndex.sporadic name).Group) →
    ∀ g : S, orderOf g = 3 → ∀ I : Subgroup S, ¬ L34Config g I

theorem up34SporLeaf_of_free (hOut : SporadicOuterLeTwo) (h : ∀ name, SporL34Free name) :
    Up34SporLeaf := by
  intro S _ _ hS hnab name he α hpump
  obtain ⟨hα3, hα1, I, hI, hI34⟩ := hpump
  haveI := hS
  have hcen : Subgroup.center S = ⊥ := up34_center_eq_bot_of_simple hnab
  have hout : Nat.card (Outer S) ≤ 2 := hOut S hS hnab name he
  obtain ⟨s, rfl, hs3⟩ := exists_conj_of_pow Nat.prime_three (by norm_num) hcen hout α hα3
  have hs1 : s ≠ 1 := by
    rintro rfl
    exact hα1 (map_one _)
  haveI : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  have hso : orderOf s = 3 := orderOf_eq_prime hs3 hs1
  rw [fixSubgroup_conj] at hI
  exact h name S hnab he s hso I ⟨hI, hI34⟩

end CFSG.HardMathSupport.Dickson.Sec6
