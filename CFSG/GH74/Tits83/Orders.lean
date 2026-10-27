module

public import CFSG.GH74.Tits83.Section4D
public import CFSG.GH74.Tits83.Glue
public import CFSG.GH74.Tits83.T79
public import CFSG.Quasithin.Recognition.Stroth.Weiss80Route

public section

namespace CFSG.GH74.Tits83

open CFSG.GH74.BNPair

theorem tits83Orders : CFSG.Quasithin.Stroth.Tits83Orders := by
  intro X _ _ D
  set T := ofRankTwo D
  rcases TitsSystem.normalized_or T (center_win_ne_bot D) with hN | hN
  · obtain ⟨c⟩ := exists_octField T hN
    obtain ⟨f, hf, hK⟩ := c.exists_odd
    refine ⟨f, hf, Or.inl ⟨fun i h1 h2 hi => ?_, fun i h1 h2 hi => ?_⟩⟩
    · rw [← ofRankTwo_U D h1 h2, c.card_odd hi, hK]
    · rw [← ofRankTwo_U D h1 h2, c.card_even hi, hK, ← pow_mul, mul_comm]
  · obtain ⟨c⟩ := exists_octField (T.refl 9) hN
    obtain ⟨f, hf, hK⟩ := c.exists_odd
    refine ⟨f, hf, Or.inr ⟨fun i h1 h2 hi => ?_, fun i h1 h2 hi => ?_⟩⟩
    · have e : T.U i = (T.refl 9).U (9 - i) := by rw [refl_U, sub_sub_cancel]
      rw [← ofRankTwo_U D h1 h2, e,
        c.card_odd (by obtain ⟨k, hk⟩ := hi; exact ⟨4 - k, by omega⟩), hK]
    · have e : T.U i = (T.refl 9).U (9 - i) := by rw [refl_U, sub_sub_cancel]
      rw [← ofRankTwo_U D h1 h2, e,
        c.card_even (by obtain ⟨k, hk⟩ := hi; exact ⟨4 - k, by omega⟩), hK, ← pow_mul,
        mul_comm]

end CFSG.GH74.Tits83
