module

public import CFSG.LocalAnalysis.AGLEmbeddingD2.McLaughlin.WeakBlockModuleData.LowRankRow
public import CFSG.LocalAnalysis.AGLEmbedding.KFactProofs.ONanSeitzCycExc
public import CFSG.LocalAnalysis.SectionRank.ClassicalEven.Orthogonal
public import CFSG.RankThree.PartTwo.Census.Carrier.SpinTDBridge

public section

namespace CFSG.AGLEmbeddingD2.McLaughlin.WeakBlockModuleData

open CFSG.Open

theorem primePower_card_two' {q : TauCeti.PrimePower} (h : q.card = 2) :
    q.p = 2 ∧ q.exponent = 1 := by
  have hp2 : q.p = 2 := PrimePower.p_eq_two_of_card_eq_two h
  refine ⟨hp2, ?_⟩
  have h1 : 2 ^ q.exponent = 2 ^ 1 := by
    have h2 := h
    rw [TauCeti.PrimePower.card_def, hp2] at h2
    rw [h2]
    norm_num
  exact Nat.pow_right_injective (le_refl 2) h1

theorem kFactOrthogonalTwoLieRank_proved : KFactOrthogonalTwoLieRank := by
  intro Y _ _ d ⟨m, q, hq, hd⟩ ⟨e⟩
  obtain ⟨d1, hv⟩ := d
  obtain ⟨hp, hqe⟩ := primePower_card_two' hq
  rcases hd with rfl | rfl | ⟨rfl, rfl⟩
  · have h := CFSG.RankThree.PartTwo.Census.statedClassicalModel_typeD_even m q hv hp e
    obtain ⟨⟨_, _, hm⟩, F, _, hF, hcard, ⟨e'⟩⟩ := h
    have hF2 : Nat.card F = 2 := by rw [hcard, hp, hqe]; norm_num
    have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
    have : Fintype F := Fintype.ofFinite F
    have : CharP F 2 := charP_of_card_eq_prime (by rw [← Nat.card_eq_fintype_card]; exact hF2)
    have h3 := CFSG.SectionRank.ClassicalEven.omegaPlus_three_le_pRank_three (K := F) hm
    rw [CFSG.SectionRank.pRank_top_eq_of_mulEquiv Nat.prime_three.one_lt e']
    exact le_trans (by norm_num) h3
  · have h := CFSG.RankThree.PartTwo.Census.statedClassicalModel_typeTwistedD_even m q hv hp e
    obtain ⟨⟨_, _, hm⟩, F, _, hF, hcard, b, c, -, ⟨e'⟩⟩ := h
    have hF2 : Nat.card F = 2 := by rw [hcard, hp, hqe]; norm_num
    have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
    have : Fintype F := Fintype.ofFinite F
    have : CharP F 2 := charP_of_card_eq_prime (by rw [← Nat.card_eq_fintype_card]; exact hF2)
    have h3 := CFSG.SectionRank.ClassicalEven.omegaMinus_three_le_pRank_three (K := F) hm b c
    rw [CFSG.SectionRank.pRank_top_eq_of_mulEquiv Nat.prime_three.one_lt e']
    exact le_trans (by norm_num) h3
  · exact CFSG.AGLEmbedding.two_le_pRank_three_unitaryFour q hp hqe hv e

end CFSG.AGLEmbeddingD2.McLaughlin.WeakBlockModuleData
