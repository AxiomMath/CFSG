module

public import CFSG.LocalAnalysis.RankThreeUC.Section5.DimensionChain
public import CFSG.LocalAnalysis.RankThreeUC.Section5.WidthArithmetic.WidthArithmetic

public section

namespace CFSG.LocalAnalysis.RankThreeUC

namespace Section5

variable {G : Type} [Group G] [Finite G]

theorem half_exponent_bound_le_extraspecial_width {p : ℕ} {P T B : Subgroup G} {e : ℕ}
    {V : Type} [AddCommGroup V] [Module (ZMod 2) V] {ρ : Representation (ZMod 2) G V}
    (hc : ExtraspecialBinaryActionCounterexample G p P T B e ρ) (n : ℕ) (hn : Nat.card ↥P = p ^ (1 + 2 * n)) :
    (2 : ℝ) ^ ((e : ℝ) / 2 - 1) ≤ (n : ℝ) := by
  obtain ⟨w, hew, hw⟩ := DimensionChain.exists_width_bound hc n hn
  obtain ⟨_, k, hk⟩ := special_commutator_center_eq_centralizer_and_exponent_power_two hc
  have he2 : 2 < e := hc.oddPrimeClassTwoAction.two_lt
  have heven : Even e := by
    rw [hk]
    cases k with
    | zero => simp at he2 hk; omega
    | succ k => exact ⟨2 ^ k, by ring⟩
  exact WidthArithmetic.bound e n w heven hew hw

end Section5
end CFSG.LocalAnalysis.RankThreeUC
