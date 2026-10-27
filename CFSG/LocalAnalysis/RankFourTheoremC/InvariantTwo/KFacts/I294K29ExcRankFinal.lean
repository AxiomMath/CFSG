module

public import CFSG.LocalAnalysis.RankFourTheoremC.InvariantTwo.KFacts.I294K29ExcRankGen
public import CFSG.HardMathSupport.Timmesfeld.CrossChar.PlanesToralE8Five
public import CFSG.HardMathSupport.Timmesfeld.Steinberg.FiveCharE8
public import CFSG.LocalAnalysis.RankFourTheoremC.InvariantTwo.KFacts.I294K29ExcRankModel

public section

set_option linter.unusedSectionVars false

namespace CFSG.LocalAnalysis.RankFourTheoremC

open CFSG.Open Subgroup CFSG.Blueprint CFSG.Blueprint.Chevalley CFSG.LieType.Chevalley
  CFSG.HardMathSupport.Timmesfeld.CrossChar CFSG.HardMathSupport.Timmesfeld

@[expose] def E8FiveFourCover : Prop :=
  ∀ q : ℕ, orderOf ((q : ℕ) : ZMod 5) = 4 → ExcRank.TypeCover Tag.E8 5 3 q

section E8


theorem crossRankE8FiveFour_of_cover (h : E8FiveFourCover) : CrossRankE8FiveFour := by
  intro q hv h4
  refine ExcRank.crossRankAtPrime_of_model fun hp hp5 hdp => ?_
  haveI : Fact q.p.Prime := ⟨q.prime_p⟩
  have hK : Nat.card (GaloisField q.p q.exponent) = q.card := by
    rw [GaloisField.card _ _ q.exponent_pos.ne', TauCeti.PrimePower.card_def]
  obtain ⟨φ⟩ := CFSG.TauCetiBridge.Even.chevalleyBridgesAll.e8 q hv
    (GaloisField q.p q.exponent) hK
  haveI : Finite (adjointGroup Tag.E8 (GaloisField q.p q.exponent)) :=
    generated_group_finite Tag.E8 _
  have h4' : orderOf ((Nat.card (GaloisField q.p q.exponent) : ℕ) : ZMod 5) = 4 := by
    rw [hK]; exact h4
  have hpK : ¬ 5 ∣ Nat.card (GaloisField q.p q.exponent) := by
    intro h5
    have h0 : ((Nat.card (GaloisField q.p q.exponent) : ℕ) : ZMod 5) = 0 :=
      (ZMod.natCast_eq_zero_iff _ 5).2 h5
    rw [h0, orderOf_zero] at h4'
    omega
  have hmon : MonomialToralAt Tag.E8 5 := monomialToralAt_five_of_chainBlock
    (fun _ hγ => iform_self_E8 hγ) chainBlockToral_E8_four
  refine ⟨adjointGroup Tag.E8 (GaloisField q.p q.exponent), inferInstance, inferInstance,
    ⟨φ.symm.trans (adjointQuotientEquiv Tag.E8 _)⟩, fun y hy => ?_⟩
  exact ExcRank.centralizer_rank_of_cover (p := 5) (n := 3) (d := 1) Nat.prime_five
    (by norm_num) (Or.inr (Or.inr ⟨rfl, rfl⟩)) hmon
    (fun _ _ a ha => (Steinberg.rootCharStabilizerSubgroup_eq_kernelReflectionGroup_E8_five
      a ha).le)
    (GaloisField q.p q.exponent) hpK (h _ h4') y hy

end E8

end CFSG.LocalAnalysis.RankFourTheoremC
