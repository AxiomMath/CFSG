module

public import CFSG.LocalAnalysis.AGLEmbeddingD2.McLaughlin.TightPairAndPureRank.L5Three.IrrBound
public import CFSG.LocalAnalysis.AGLEmbeddingD2.McLaughlin.TightPairAndPureRank.L5Three.OrderFourteen

public section

namespace CFSG.AGLEmbeddingD2.McLaughlin.L5Three

open Subgroup Module CFSG.GroupTheory.GL52

variable {V : Type} [AddCommGroup V] [Module (ZMod 2) V] [Finite V]

theorem finrank_proper {W : Submodule (ZMod 2) V} (h0 : W ≠ ⊥) (h1 : W ≠ ⊤) :
    1 ≤ finrank (ZMod 2) W ∧ finrank (ZMod 2) W < finrank (ZMod 2) V := by
  have : Module.Finite (ZMod 2) V := Module.Finite.of_finite
  refine ⟨?_, ?_⟩
  · exact Submodule.one_le_finrank_iff.2 h0
  · exact Submodule.finrank_lt h1

theorem exists_invariant_of_not_irreducible {Y : Subgroup (V ≃ₗ[ZMod 2] V)} (h : ¬ Irreducible' Y) :
    ∃ W : Submodule (ZMod 2) V, Y ≤ stab W ∧ W ≠ ⊥ ∧ W ≠ ⊤ := by
  unfold Irreducible' at h
  push Not at h
  obtain ⟨W, hW, h0, h1⟩ := h
  exact ⟨W, hW, h0, h1⟩

theorem threeBound_three : ThreeBound 3 8 := by
  intro V _ _ _ hV Y h3
  by_cases hirr : Irreducible' Y
  · have : Module.Finite (ZMod 2) V := Module.Finite.of_finite
    have : Nontrivial V := (Module.finrank_pos_iff (R := ZMod 2) (M := V)).1 (by omega)
    have hmem := irr_orders (by omega) (by omega) hirr h3
    have hdvd : Nat.card Y ∣ 168 := by
      rw [← card_linEquiv_three hV]; exact Subgroup.card_subgroup_dvd_card Y
    simp only [irrOrders, Finset.mem_insert, Finset.mem_singleton] at hmem
    rcases hmem with h | h | h | h | h | h | h | h | h | h
    · omega
    · omega
    · rw [h] at hdvd; omega
    · exact (no_subgroup_fourteen hV Y h).elim
    · rw [h] at hdvd; omega
    · rw [h] at hdvd; omega
    · rw [h] at hdvd; omega
    · rw [h] at hdvd; omega
    · rw [h] at hdvd; omega
    · rw [h] at hdvd; omega
  · obtain ⟨W, hY, h0, h1⟩ := exists_invariant_of_not_irreducible hirr
    obtain ⟨hk1, hk2⟩ := finrank_proper h0 h1
    rw [hV] at hk2
    have key := fun k (hk : finrank (ZMod 2) W = k) (a b : ℕ) (hA : ThreeBound k a)
      (hB : ThreeBound (3 - k) b) => card_le_of_invariant hV hY hk hA hB h3
    interval_cases hk : finrank (ZMod 2) W
    · exact (key 1 rfl 1 2 threeBound_one threeBound_two).trans (by norm_num)
    · exact (key 2 rfl 2 1 threeBound_two threeBound_one).trans (by norm_num)

theorem threeBound_four : ThreeBound 4 64 := by
  intro V _ _ _ hV Y h3
  by_cases hirr : Irreducible' Y
  · have : Module.Finite (ZMod 2) V := Module.Finite.of_finite
    have : Nontrivial V := (Module.finrank_pos_iff (R := ZMod 2) (M := V)).1 (by omega)
    have hmem := irr_orders (by omega) (by omega) hirr h3
    have hdvd : Nat.card Y ∣ 20160 := by
      rw [← card_linEquiv_four hV]; exact Subgroup.card_subgroup_dvd_card Y
    simp only [irrOrders, Finset.mem_insert, Finset.mem_singleton] at hmem
    rcases hmem with h | h | h | h | h | h | h | h | h | h
    · omega
    · omega
    · omega
    · omega
    · omega
    · rw [h] at hdvd; omega
    · rw [h] at hdvd; omega
    · rw [h] at hdvd; omega
    · rw [h] at hdvd; omega
    · rw [h] at hdvd; omega
  · obtain ⟨W, hY, h0, h1⟩ := exists_invariant_of_not_irreducible hirr
    obtain ⟨hk1, hk2⟩ := finrank_proper h0 h1
    rw [hV] at hk2
    have key := fun k (hk : finrank (ZMod 2) W = k) (a b : ℕ) (hA : ThreeBound k a)
      (hB : ThreeBound (4 - k) b) => card_le_of_invariant hV hY hk hA hB h3
    interval_cases hk : finrank (ZMod 2) W
    · exact (key 1 rfl 1 8 threeBound_one threeBound_three).trans (by norm_num)
    · exact (key 2 rfl 2 2 threeBound_two threeBound_two).trans (by norm_num)
    · exact (key 3 rfl 8 1 threeBound_three threeBound_one).trans (by norm_num)

end CFSG.AGLEmbeddingD2.McLaughlin.L5Three
