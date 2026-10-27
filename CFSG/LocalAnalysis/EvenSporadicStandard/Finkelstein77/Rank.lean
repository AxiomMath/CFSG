module

public import CFSG.Open.LocalVocabulary

public section

namespace CFSG.EvenSporadicStandard.Finkelstein77

theorem three_le_twoRank_of_elemAbelian_eight {Y : Type*} [Group Y] [Finite Y]
    (E : Subgroup Y) (hE : CFSG.Open.IsElemAbelian 2 E) (hcard : Nat.card E = 8) :
    3 ≤ CFSG.Open.twoRank Y := by
  have hbdd : BddAbove {k : ℕ | ∃ E' : Subgroup Y, E' ≤ (⊤ : Subgroup Y) ∧
      CFSG.Open.IsElemAbelian 2 E' ∧ Nat.card E' = 2 ^ k} := by
    refine ⟨Nat.card Y, fun k hk => ?_⟩
    obtain ⟨E', -, -, hE'⟩ := hk
    have h1 : 2 ^ k ≤ Nat.card Y := hE' ▸ Subgroup.card_le_card_group E'
    exact (Nat.lt_two_pow_self.le).trans h1
  exact le_csSup hbdd ⟨E, le_top, hE, by rw [hcard]; norm_num⟩

end CFSG.EvenSporadicStandard.Finkelstein77
