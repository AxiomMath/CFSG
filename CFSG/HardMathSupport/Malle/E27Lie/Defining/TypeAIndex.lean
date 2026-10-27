module

public import CFSG.HardMathSupport.Malle.E27Lie.Defining.TypeAFour
public import CFSG.HardMathSupport.Malle.E27Lie.Defining.TypeASmall
public import CFSG.HardMathSupport.Malle.E27Lie.Defining.TypeA

public section

namespace CFSG.HardMathSupport.Malle.E27Lie

open CFSG.HardMathSupport.Foote.E27 TauCeti

theorem false_of_typeA_charThree {X : Type} [Group X] [Finite X] {K R T : Subgroup X} {z : X}
    (h : E27Config X K R T z) (hz : z ∈ K) (r : ℕ) (q : PrimePower)
    (hv : (LieTypeIndex.A r q).Valid) (hp : q.p = 3)
    (e : ↥K ≃* (CFSGIndex.lie ⟨.A r q, hv⟩).Group) : False := by
  by_cases hfr : 4 ≤ q.exponent * r
  · exact false_of_typeA_char_three h hz r q hv hp hfr e
  have hv' := hv
  rw [LieTypeIndex.valid_iff, LieTypeIndex.inStandardRange_iff,
    LieTypeIndex.isDuplicateRepresentative_iff] at hv'
  obtain ⟨⟨hr1, hr4⟩, hdup⟩ := hv'
  have hf1 := q.exponent_pos
  have hcard : q.card = 3 ^ q.exponent := by rw [PrimePower.card_def, hp]
  have hr3 : r ≤ 3 := by
    have : r ≤ q.exponent * r := Nat.le_mul_of_pos_left r hf1
    omega
  interval_cases r
  · rcases (by omega : q.exponent = 1 ∨ q.exponent = 2 ∨ q.exponent = 3) with hf | hf | hf
    · have h4 := hr4 rfl
      rw [hcard, hf] at h4
      norm_num at h4
    · exact hdup (Or.inl ⟨rfl, Or.inr (Or.inr (by rw [hcard, hf]; norm_num))⟩)
    · exact false_of_typeA_L2_27 h q hv hp hf e
  · exact false_of_typeA_L3_3 h hz q hv hp (by omega) e
  · exact false_of_typeA_three_char_three h hz q hv hp e

end CFSG.HardMathSupport.Malle.E27Lie
