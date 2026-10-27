module

public import CFSG.Goldschmidt.StatementsH
import CFSG.Goldschmidt.Steps.Glue
import CFSG.StronglyEmbedded.BenderNormalSeries
import CFSG.StronglyEmbedded

public section

namespace CFSG.Goldschmidt

open CFSG.Open

theorem N41 :
    S_N20 → S_N21 → S_N22 → S_N23 → S_simpleConcl → S_B3setup → S_N24 → S_N25 → S_B2setup →
      S_N26 → S_N27 → S_N28 → S_N29 → S_N30 → S_N31_exists → S_N31 → S_N39 → S_N40 →
      S_propH_compType → CoreStatement := by
  intro hN20 hN21 hN22 hN23 hsimple hB3 hN24 hN25 hB2 hN26 hN27 hN28 hN29 hN30 hN31e hN31
    hN39 hN40 hH
  apply coreStatement_of_step
  intro G _ _ hIH
  rw [coreFor_iff]
  intro S A hA
  by_cases hE : goldschmidtLayer G = ⊥
  · exact (hN20 G S A hA hE).2
  rcases hN22 G S A hA hIH hE with ⟨hs, hnab⟩ | ⟨K, hK, hKn, hKs, hKA, hC, hAK⟩ |
    ⟨hidx, ha, hC⟩
  ·
    have hA0 : A ≠ ⊥ := glue_ne_bot hA.gen
    rw [hsimple G hnab S A]
    by_cases hS : IsMulCommutative (S : Subgroup G)
    · obtain ⟨h1, -, h3⟩ := hN29 G hnab S hS A hA.le hA0 hA.closed
      exact ⟨h1, h3⟩
    · have hB : fusionIsBenderGroup G := by
        by_cases hSE : ∃ M : Subgroup G, CFSG.BenderSuzuki.IsStronglyEmbeddedOrder M
        · obtain ⟨M, hM⟩ := hSE
          exact fusionIsBenderGroup_of_isBenderGroup (CFSG.BenderSuzuki.bender_suzuki M hM)
        · push Not at hSE
          obtain ⟨U, hUA, hU⟩ := hN31e G S A hA.le hA0 hA.closed
          obtain ⟨hUel, hU4, -⟩ := hN31 G hnab S A U hA.le hA.comm hA.closed hUA hU
          have hrk : 2 ≤ CFSG.Assembly.twoRank G := glue_twoRank hUel hU4
          rcases Nat.lt_or_ge (CFSG.Assembly.twoRank G) 3 with h2 | h3
          · rcases hN40 G hnab (by omega) S A hA.le hA0 hA.comm hA.closed with hab | e
            · exact absurd hab hS
            · exact Or.inr (Or.inl ⟨2, le_refl 2, e⟩)
          · by_cases hct : CFSG.Assembly.IsComponentType G
            · exact (hH G hnab hIH hct h3 hSE S hS A U hA.le hA.comm hA.closed hUA hU).elim
            · exact (hN39 G hnab hIH h3 hct hSE S U (hUA.trans hA.le) hU.2.1 hUel
                hU.2.2.1).elim
      obtain ⟨h1, h2, -⟩ := hN30 G hB S hS A hA.le hA0 hA.comm hA.closed
      exact ⟨h1, h2⟩
  ·
    have hnK := glue_nonabelian hK
    obtain ⟨-, hKt, hAK'⟩ := hB3 G S A hA hIH K hKn hKs hnK hKA hC hAK
    by_cases hT : IsMulCommutative ((S : Subgroup G) ⊓ K : Subgroup G)
    · exact (hN24 G S A hA K hKn hKs hnK hKA hC hAK hKt hAK' hT).elim
    · exact (hN25 G S A hA K hKn hKs hnK hKA hC hAK hKt hAK' hT).elim
  · by_cases hq : IsComponentOf (⊤ : Subgroup G) ⊤
    ·
      have hqs := glue_quasisimple hq
      have hZ : Subgroup.center G ≠ ⊥ := glue_center A (hidx ⊤ hq)
      obtain ⟨-, hgt, hAbar⟩ := hB2 G S A hA hIH hqs hZ
      by_cases hSab :
          IsMulCommutative ((S : Subgroup G).map (QuotientGroup.mk' (Subgroup.center G)))
      · exact (hN26 G S A hA hqs hZ hgt hAbar hSab).elim
      · exact hN28 G S A hA hqs hgt hAbar (hN27 G S A hA hqs hgt hAbar hSab)
    ·
      have hc : ∀ K : Subgroup G, IsComponentOf K ⊤ →
          goldschmidtSimpleType (K ⧸ Subgroup.center K) ∧ InducesOmega1 A K S :=
        fun K hK => hN21 (Nat.card G) hIH G S A hA K hK (hidx K hK)
      exact ⟨ha, hN23 G S A hA hIH hq hc ha hC, fun K hK => (hc K hK).1⟩

end CFSG.Goldschmidt
