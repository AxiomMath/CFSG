module

public import CFSG.HardMathSupport.Malle.E27Lie.Defining.TypeOrthTail
public import CFSG.HardMathSupport.Malle.E27Lie.Defining.TypeAIndex
public import CFSG.HardMathSupport.Malle.E27Lie.Defining.TypeTwistedA
public import CFSG.HardMathSupport.Malle.E27Lie.Cross.Char3Split

public section

namespace CFSG.HardMathSupport.Malle.E27Lie

open CFSG.HardMathSupport.Foote.E27 TauCeti

@[expose] def IdxChar3Small (i : LieTypeIndex) : Prop :=
  ∃ q : PrimePower, q.p = 3 ∧ q.exponent = 1 ∧
    (i = .twistedA 2 q ∨ i = .twistedA 3 q ∨ i = .B 3 q ∨ i = .C 3 q)

@[expose] def IdxChar3Exc (i : LieTypeIndex) : Prop :=
  ∃ q : PrimePower, q.p = 3 ∧ (i = .G2 q ∨ i = .F4 q ∨ i = .E6 q ∨ i = .E7 q ∨ i = .E8 q ∨
    i = .twistedE6 q ∨ i = .trialityD4 q)

theorem innerLeaf_char3Rest_of_leaves (leafSmall : InnerLeaf IdxChar3Small)
    (leafExc : InnerLeaf IdxChar3Exc) : InnerLeaf IdxChar3Rest := by
  intro X _ _ K R T z h hz d hd e
  obtain ⟨i, hv⟩ := d
  obtain ⟨hd, hree⟩ := hd
  have hrange := (LieTypeIndex.inStandardRange_iff _).1 ((LieTypeIndex.valid_iff _).1 hv).1
  rcases hd with ⟨r, q, hp, hi⟩ | ⟨q, hp, hi⟩ | ⟨m, hm⟩
  · obtain ⟨e⟩ := e
    rcases hi with rfl | rfl | rfl | rfl | rfl | rfl
    · exact false_of_typeA_charThree h hz r q hv hp e
    · by_cases hs : (r = 2 ∧ q.exponent = 1) ∨ (r = 3 ∧ q.exponent = 1)
      · refine leafSmall h hz ⟨_, hv⟩ ?_ ⟨e⟩
        rcases hs with ⟨rfl, hf⟩ | ⟨rfl, hf⟩
        · exact ⟨q, hp, hf, Or.inl rfl⟩
        · exact ⟨q, hp, hf, Or.inr (Or.inl rfl)⟩
      · push Not at hs
        exact false_of_typeTwistedA_char_three h hz r q hv hp (fun h' => hs.1 h'.1 h'.2)
          (fun h' => hs.2 h'.1 h'.2) e
    · simp only at hrange
      have hr2 : 2 ≤ r := hrange.1
      rcases (by omega : r = 2 ∨ 3 ≤ r) with rfl | hr3
      · exact false_of_typeB2_char_three h hz q hv hp e
      · by_cases hfr : 4 ≤ q.exponent * r
        · exact false_of_typeB_char_three h hz r q hv hp hr3 hfr e
        · have hf := q.exponent_pos
          have hr : r ≤ q.exponent * r := Nat.le_mul_of_pos_left r hf
          obtain rfl : r = 3 := by omega
          exact leafSmall h hz ⟨_, hv⟩ ⟨q, hp, by omega, Or.inr (Or.inr (Or.inl rfl))⟩ ⟨e⟩
    · simp only at hrange
      have hr3 : 3 ≤ r := hrange.1
      by_cases hfr : 4 ≤ q.exponent * r
      · exact false_of_typeC_char_three h hz r q hv hp hfr e
      · have hf := q.exponent_pos
        have hr : r ≤ q.exponent * r := Nat.le_mul_of_pos_left r hf
        obtain rfl : r = 3 := by omega
        exact leafSmall h hz ⟨_, hv⟩ ⟨q, hp, by omega, Or.inr (Or.inr (Or.inr rfl))⟩ ⟨e⟩
    · exact false_of_typeD_char_three h hz r q hv hp e
    · exact false_of_typeTwistedD_char_three h hz r q hv hp e
  · exact leafExc h hz ⟨i, hv⟩ ⟨q, hp, hi⟩ e
  · exact absurd ⟨m, hm⟩ hree

end CFSG.HardMathSupport.Malle.E27Lie
