module

public import CFSG.HardMathSupport.Timmesfeld.ComponentBalance.I_11_3_Defs
public import CFSG.LocalAnalysis.GLTheoremB.Lemma99Inputs

public section

namespace CFSG.HardMathSupport.Timmesfeld.ComponentBalance

open CFSG.Open CFSG.LocalAnalysis.GLTheoremB

theorem i113_pRank_eq_of_card {G : Type*} [Group G] [Finite G] {p k : ℕ} (hp : p.Prime)
    {E : Subgroup G} (hE : IsElemAbelian p E) (hcard : Nat.card E = p ^ k) :
    pRank p E = k := by
  have hbdd : BddAbove {k' | ∃ F : Subgroup G, F ≤ E ∧ IsElemAbelian p F ∧ Nat.card F = p ^ k'} := by
    refine ⟨k, fun k' ⟨F, hFE, _, hF⟩ => ?_⟩
    have hd : p ^ k' ∣ p ^ k := hF ▸ hcard ▸ Subgroup.card_dvd_of_le hFE
    exact (Nat.pow_dvd_pow_iff_le_right hp.one_lt).1 hd
  refine le_antisymm (csSup_le' fun k' ⟨F, hFE, _, hF⟩ => ?_) (le_csSup hbdd ⟨E, le_rfl, hE, hcard⟩)
  have hd : p ^ k' ∣ p ^ k := hF ▸ hcard ▸ Subgroup.card_dvd_of_le hFE
  exact (Nat.pow_dvd_pow_iff_le_right hp.one_lt).1 hd

theorem i113_rank_of_isBmax {X : Type*} [Group X] [Finite X] {p : ℕ} (hp : p.Prime)
    {B : Subgroup X} (hB : GLAIsBmax p B) : GLATwoLocalRank p X ≤ pRank p B := by
  rw [i113_pRank_eq_of_card hp hB.1 hB.2.1]

theorem input11_3_of_kernel (h112 : I112) (k : Kernel11_3a) : Input11_3 := by
  intro X _ _ hX p hp hodd B hB L hL hnL
  obtain ⟨hp3, hidx, hdich⟩ := h112 X hX p hp hodd B hB.1 (i113_rank_of_isBmax hp hB) L hL hnL
  subst hp3
  rcases hdich with h | h
  · exact h
  · exact absurd h (k X hX B hB L hL hnL hidx)

end CFSG.HardMathSupport.Timmesfeld.ComponentBalance
