module

public import CFSG.LocalAnalysis.AGLEmbeddingD2.McLaughlin.TightPairAndPureRank.L5Three.VecStab
public import CFSG.LocalAnalysis.AGLEmbeddingD2.McLaughlin.TightPairAndPureRank.L5Three.Order8680

public section

namespace CFSG.AGLEmbeddingD2.McLaughlin.L5Three

open Subgroup Module CFSG.GroupTheory.GL52

theorem threeBound_five : ThreeBound 5 1024 := by
  intro V _ _ _ hV Y h3
  by_cases hirr : Irreducible' Y
  · have : Module.Finite (ZMod 2) V := Module.Finite.of_finite
    have : Nontrivial V := (Module.finrank_pos_iff (R := ZMod 2) (M := V)).1 (by omega)
    have hmem := irr_orders (by omega) (by omega) hirr h3
    simp only [irrOrders, Finset.mem_insert, Finset.mem_singleton] at hmem
    rcases hmem with h | h | h | h | h | h | h | h | h | h
    · omega
    · omega
    · omega
    · omega
    · omega
    · omega
    · omega
    · exact (kill_4960_158720 hV h3 (Or.inl h)).elim
    · exact (not_card_eq_8680 (Y.map (embG52 (by omega))) (by
        rw [Subgroup.card_map_of_injective (embG52_injective (by omega)), h]; norm_num)).elim
    · exact (kill_4960_158720 hV h3 (Or.inr h)).elim
  · obtain ⟨W, hY, h0, h1⟩ := exists_invariant_of_not_irreducible hirr
    obtain ⟨hk1, hk2⟩ := finrank_proper h0 h1
    rw [hV] at hk2
    have key := fun k (hk : finrank (ZMod 2) W = k) (a b : ℕ) (hA : ThreeBound k a)
      (hB : ThreeBound (5 - k) b) => card_le_of_invariant hV hY hk hA hB h3
    interval_cases hk : finrank (ZMod 2) W
    · exact (key 1 rfl 1 64 threeBound_one threeBound_four).trans (by norm_num)
    · exact (key 2 rfl 2 8 threeBound_two threeBound_three).trans (by norm_num)
    · exact (key 3 rfl 8 2 threeBound_three threeBound_two).trans (by norm_num)
    · exact (key 4 rfl 64 1 threeBound_four threeBound_one).trans (by norm_num)

end CFSG.AGLEmbeddingD2.McLaughlin.L5Three
