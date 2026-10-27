module

public import CFSG.LocalAnalysis.RankFourTheoremC.PPointP.FusionOdd
public import CFSG.LocalAnalysis.RankFourTheoremC.PPointP.FusionEven

public section

namespace CFSG.LocalAnalysis.RankFourTheoremC.PPointP

open Subgroup CFSG.Open

namespace FusionData

variable {G : Type} [Group G] [Finite G] {p n : ℕ} {F : Type} [Field F] {f : F → G} {x : G}
  {W : Subgroup G} (h : FusionData G p n F f x W)

include h

theorem no_conjLine [hp : Fact p.Prime] [CharP F p] (hp2 : p ≠ 2) :
    (∀ t : F, t ≠ 0 → ¬ ConjLine x (f t)) ∧ (∀ k : F, k ≠ 0 → ¬ ConjLine x (f k * x)) := by
  have : Finite F :=
    Nat.finite_of_card_ne_zero (by rw [h.card_F]; exact pow_ne_zero _ hp.out.ne_zero)
  rcases Nat.even_or_odd n with hn | hn
  · have hnoA : ∀ k : F, k ≠ 0 → ¬ ConjLine x (f k * x) :=
      fun k hk hA => h.not_conjLine_A_of_even hp2 hn hk hA
    refine ⟨fun t ht hB => ?_, hnoA⟩
    by_cases h4 : 4 ≤ n
    · exact h.not_conjLine_B_of_even_four hp2 hn h4 ht hB
    · have hn2 : n = 2 := by
        obtain ⟨c, hc⟩ := hn
        have := h.two_le
        omega
      have hp5 : 5 ≤ p := by
        rcases h.p_n with h5 | h3
        · exact h5
        · omega
      exact h.not_conjLine_B_two hn2 hp5 hnoA ht hB
  · have hnoB : ∀ t : F, t ≠ 0 → ¬ ConjLine x (f t) :=
      fun t ht hB => h.not_conjLine_B_of_odd hp2 hn ht hB
    exact ⟨hnoB, fun k hk hA => h.not_conjLine_A_of_odd hp2 hnoB hk hA⟩

theorem mem_zpowers_of_conjLine [hp : Fact p.Prime] [CharP F p] (hp2 : p ≠ 2) {y : G}
    (hyW : y ∈ W) (hyc : ConjLine x y) : y ∈ zpowers x := by
  by_contra hyx
  obtain ⟨hnoB, hnoA⟩ := h.no_conjLine hp2
  rcases h.exists_type hyW hyc hyx with ⟨t, ht, hte⟩ | ⟨t, ht, hte⟩
  · obtain ⟨g', hg'⟩ := hyc
    exact hnoB t ht ⟨g', hte.symm.trans hg'⟩
  · obtain ⟨g', hg'⟩ := hyc
    exact hnoA t ht ⟨g', hte.symm.trans hg'⟩

theorem eq_zpowers_of_conj [hp : Fact p.Prime] [CharP F p] (hp2 : p ≠ 2) {L : Subgroup G}
    (hL : L ∈ ConjLines W x) : L = zpowers x := by
  obtain ⟨hLW, g, hg⟩ := hL
  have hLy : L = zpowers (g * x * g⁻¹) := by rw [hg, map_conj_zpowers']
  have hyL : g * x * g⁻¹ ∈ L := by rw [hLy]; exact mem_zpowers _
  have hy1 : g * x * g⁻¹ ≠ 1 := conj_ne_one h.x_ne_one g
  have hyx := h.mem_zpowers_of_conjLine hp2 (hLW hyL) ⟨g, hLy.symm.trans hg⟩
  rw [hLy]
  exact h.zpowers_eq_of_mem (conjLine_self x) hyx hy1

end FusionData

end CFSG.LocalAnalysis.RankFourTheoremC.PPointP
