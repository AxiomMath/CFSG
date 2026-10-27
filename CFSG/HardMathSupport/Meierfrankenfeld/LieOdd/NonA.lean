module

public import CFSG.HardMathSupport.Meierfrankenfeld.LieOdd.AFamily
public import CFSG.HardMathSupport.Meierfrankenfeld.LieOdd.Sp
public import CFSG.HardMathSupport.Meierfrankenfeld.LieOdd.Orth
public import CFSG.HardMathSupport.Meierfrankenfeld.LieOdd.Unit

public section

namespace CFSG.HardMathSupport.Meierfrankenfeld.LieOdd

open CFSG.HardMathSupport.Cooperstein.Coordinator TauCeti

@[expose] def GF2NoFFLieOddExceptional : Prop :=
  ∀ d : ValidLieTypeIndex,
    ((∃ q, d.1 = .E6 q) ∨ (∃ q, d.1 = .E7 q) ∨ (∃ q, d.1 = .E8 q) ∨ (∃ q, d.1 = .F4 q) ∨
      (∃ q : PrimePower, q.card ≠ 3 ∧ d.1 = .G2 q) ∨ (∃ q, d.1 = .twistedE6 q) ∨
      (∃ q, d.1 = .trialityD4 q) ∨ (∃ m, d.1 = .reeG2 m)) →
    d.1.characteristic ≠ 2 → ¬ CFSG.AGLEmbedding.IsClassicalTwoOrG2 (CFSGIndex.lie d).Group →
      NoFFModule (CFSGIndex.lie d).Group

@[expose] def GF2NoFFLieOddSmall : Prop :=
  ∀ d : ValidLieTypeIndex,
    ((∃ q : PrimePower, (q.card = 5 ∨ q.card = 7) ∧ d.1 = .B 2 q) ∨
      (∃ q : PrimePower, q.card = 3 ∧
        (d.1 = .B 3 q ∨ d.1 = .C 3 q ∨ d.1 = .C 4 q ∨ d.1 = .twistedA 3 q ∨
          d.1 = .twistedA 4 q ∨ d.1 = .G2 q))) →
    ¬ CFSG.AGLEmbedding.IsClassicalTwoOrG2 (CFSGIndex.lie d).Group →
      NoFFModule (CFSGIndex.lie d).Group

theorem nine_le_of_odd_prime_pow {q : PrimePower} (hp2 : q.p ≠ 2) (h3 : q.card ≠ 3)
    (h57 : ¬ (q.card = 5 ∨ q.card = 7)) : 9 ≤ q.card := by
  have hodd : Odd q.card := by
    rw [PrimePower.card_def]
    exact (q.prime_p.eq_two_or_odd'.resolve_left hp2).pow
  have h3' : 3 ≤ q.card := by
    rw [PrimePower.card_def]
    have := q.prime_p.two_le
    exact (show 3 ≤ q.p by omega).trans (Nat.le_self_pow q.exponent_pos.ne' q.p)
  obtain ⟨k, hk⟩ := hodd
  omega

theorem gf2NoFFLieOddNonA_of_nodes (hEx : GF2NoFFLieOddExceptional)
    (hSm : GF2NoFFLieOddSmall) : GF2NoFFLieOddNonA := by
  intro d hA hchar hc hs
  obtain ⟨d, hv⟩ := d
  cases d with
  | A r q => exact absurd rfl (hA r q)
  | twistedA r q =>
    have hp : q.p ≠ 2 := by simpa using hchar
    by_cases h3 : r = 2 ∧ q.exponent = 1
    · exfalso
      obtain ⟨rfl, he⟩ := h3
      by_cases hp5 : 5 ≤ q.p
      · exact hs ⟨he, hp5⟩
      · have hp3 : q.p = 3 := by
          have h2 := q.prime_p.two_le
          have h4 : q.p ≠ 4 := by
            intro h4
            have := q.prime_p
            rw [h4] at this
            exact absurd this (by decide)
          omega
        exact hc (Or.inr (Or.inr ⟨⟨.twistedA 2 q, hv⟩,
          Or.inr ⟨q, by rw [PrimePower.card_def, hp3, he]; norm_num, rfl⟩, ⟨MulEquiv.refl _⟩⟩))
    · by_cases h4 : r = 3 ∧ q.card = 3
      · obtain ⟨rfl, hq⟩ := h4
        exact hSm ⟨_, hv⟩ (Or.inr ⟨q, hq, Or.inr (Or.inr (Or.inr (Or.inl rfl)))⟩) hc
      · by_cases h5 : r = 4 ∧ q.card = 3
        · obtain ⟨rfl, hq⟩ := h5
          exact hSm ⟨_, hv⟩ (Or.inr ⟨q, hq, Or.inr (Or.inr (Or.inr (Or.inr (Or.inl rfl))))⟩) hc
        · exact noFFModule_lie_twistedA ⟨_, hv⟩ rfl hp h3 h4 h5
  | B r q =>
    have hp : q.p ≠ 2 := by simpa using hchar
    have hr : 2 ≤ r := ((LieTypeIndex.inStandardRange_iff _).1 ((LieTypeIndex.valid_iff _).1 hv).1).1
    rcases (show r = 2 ∨ 3 ≤ r by omega) with rfl | hr3
    · by_cases h3 : q.card = 3
      · exact absurd ((LieTypeIndex.isDuplicateRepresentative_iff (.B 2 q)).2 ⟨rfl, h3⟩)
          ((LieTypeIndex.valid_iff _).1 hv).2
      · by_cases h57 : q.card = 5 ∨ q.card = 7
        · exact hSm ⟨_, hv⟩ (Or.inl ⟨q, h57, rfl⟩) hc
        · exact noFFModule_lie_B2 ⟨_, hv⟩ rfl hp (nine_le_of_odd_prime_pow hp h3 h57)
    · by_cases h73 : r = 3 ∧ q.card = 3
      · obtain ⟨rfl, hq⟩ := h73
        exact hSm ⟨_, hv⟩ (Or.inr ⟨q, hq, Or.inl rfl⟩) hc
      · exact noFFModule_lie_B ⟨_, hv⟩ rfl hp hr3 h73
  | C r q =>
    by_cases h3 : r = 3 ∧ q.card = 3
    · obtain ⟨rfl, hq⟩ := h3
      exact hSm ⟨_, hv⟩ (Or.inr ⟨q, hq, Or.inr (Or.inl rfl)⟩) hc
    · by_cases h4 : r = 4 ∧ q.card = 3
      · obtain ⟨rfl, hq⟩ := h4
        exact hSm ⟨_, hv⟩ (Or.inr ⟨q, hq, Or.inr (Or.inr (Or.inl rfl))⟩) hc
      · exact noFFModule_lie_C ⟨_, hv⟩ rfl h3 h4
  | D r q => exact noFFModule_lie_D ⟨_, hv⟩ rfl (by simpa using hchar)
  | twistedD r q => exact noFFModule_lie_twistedD ⟨_, hv⟩ rfl (by simpa using hchar)
  | E6 q => exact hEx ⟨_, hv⟩ (Or.inl ⟨q, rfl⟩) hchar hc
  | E7 q => exact hEx ⟨_, hv⟩ (Or.inr (Or.inl ⟨q, rfl⟩)) hchar hc
  | E8 q => exact hEx ⟨_, hv⟩ (Or.inr (Or.inr (Or.inl ⟨q, rfl⟩))) hchar hc
  | F4 q => exact hEx ⟨_, hv⟩ (Or.inr (Or.inr (Or.inr (Or.inl ⟨q, rfl⟩)))) hchar hc
  | G2 q =>
    by_cases h3 : q.card = 3
    · exact hSm ⟨_, hv⟩ (Or.inr ⟨q, h3, Or.inr (Or.inr (Or.inr (Or.inr (Or.inr rfl))))⟩)
        hc
    · exact hEx ⟨_, hv⟩ (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl ⟨q, h3, rfl⟩))))) hchar hc
  | twistedE6 q =>
    exact hEx ⟨_, hv⟩ (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl ⟨q, rfl⟩)))))) hchar hc
  | trialityD4 q =>
    exact hEx ⟨_, hv⟩
      (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl ⟨q, rfl⟩))))))) hchar hc
  | suzuki m => exact absurd (LieTypeIndex.characteristic_suzuki m) hchar
  | reeG2 m =>
    exact hEx ⟨_, hv⟩
      (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr ⟨m, rfl⟩))))))) hchar hc
  | reeF4 m => exact absurd (LieTypeIndex.characteristic_reeF4 m) hchar
  | tits => exact absurd LieTypeIndex.characteristic_tits hchar

theorem gf2NoFFLieOdd_of_nodes (hEx : GF2NoFFLieOddExceptional) (hSm : GF2NoFFLieOddSmall) :
    GF2NoFFLieOdd :=
  gf2NoFFLieOdd_of_nonA (gf2NoFFLieOddNonA_of_nodes hEx hSm)

end CFSG.HardMathSupport.Meierfrankenfeld.LieOdd
