module

public import CFSG.LocalAnalysis.AGLEmbedding.KFactProofs.ONanMonsterThreeY
public import CFSG.LocalAnalysis.AGLEmbedding.Norton.MON5_7.OddLift

public section

namespace CFSG.AGLEmbedding.Norton

open CFSG.Open CFSG.Blueprint TauCeti CFSG.AGLEmbedding.Norton.MON5_7

private theorem center_eq_bot_of_simple_nonabelian {T : Type} [Group T] [IsSimpleGroup T]
    (hnc : ∃ a b : T, a * b ≠ b * a) : Subgroup.center T = ⊥ := by
  rcases (inferInstance : (Subgroup.center T).Normal).eq_bot_or_eq_top with h | h
  · exact h
  · obtain ⟨a, b, hab⟩ := hnc
    exact absurd (Subgroup.mem_center_iff.1 (h ▸ Subgroup.mem_top b) a) hab

theorem sporCaseThreePrimeData_monster_three_noMult {T : Type} [Group T] [Finite T]
    [IsSimpleGroup T] (hnc : ∃ a b : T, a * b ≠ b * a)
    (he : Nonempty (T ≃* CFSG.Blueprint.NativeSporadic.Carrier .M)) :
    @SporCaseThreePrimeData T _ _ 3 ⟨Nat.prime_three⟩ := by
  obtain ⟨e⟩ := he
  have hZ := center_eq_bot_of_simple_nonabelian hnc
  have hLift := MonsterThree.liftableNormalizerGen_M e.injective.nontrivial
  refine Or.inr (Or.inr ⟨fun P => Or.inl ?_, Or.inr ?_⟩)
  · exact weakCore_eq_top_of_normalizerGen hLift
      ((QuotientGroup.quotientMulEquivOfEq hZ).trans (QuotientGroup.quotientBot.trans e))
      (by rw [hZ]; exact IsPGroup.of_card (n := 0) (by simp)) P
  · exact coverWeakGen_of_liftableNormalizerGen (LiftableNormalizerGen.of_mulEquiv e.symm hLift)

end CFSG.AGLEmbedding.Norton
