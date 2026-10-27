module

public import CFSG.LocalAnalysis.GLTheoremA.CatC.KDRank3Amb

public section

namespace CFSG.LocalAnalysis.GLTheoremA

open CFSG.Open CFSG.Yardstones.Md0ec50421ce4
open CFSG.ComponentClassification.OuterAutomorphisms (inner Outer)

@[expose] def KDRank3Field : Prop :=
  ∀ (p : ℕ), p.Prime → p ≠ 2 → ∀ (S : Type) [Group S] [Finite S] (d : TauCeti.ValidLieTypeIndex),
    Nonempty (S ≃* (TauCeti.CFSGIndex.lie d).Group) → d.1.characteristic = p →
      GLATwoLocalRank p S ≤ 3 → p ∣ Nat.card (Outer S) → IsRank3Handled d.1

@[expose] def KDRank3Small : Prop :=
  ∀ (S : Type) [Group S] [Finite S] (d : TauCeti.ValidLieTypeIndex),
    Nonempty (S ≃* (TauCeti.CFSGIndex.lie d).Group) → IsRank3Small d.1 →
    ∀ E : Subgroup (MulAut S), IsElemAbelian 3 E → Nat.card E = 3 ^ 3 → ¬ E ≤ inner S →
      Nat.card ↥(E ⊓ inner S) = 3 ^ 2 → Rank3Concl 3 S E

theorem characteristic_eq_three_of_isRank3Small {d : TauCeti.LieTypeIndex} (h : IsRank3Small d) :
    d.characteristic = 3 := by
  have key : ∀ q : TauCeti.PrimePower, q.card = 27 → q.p = 3 := by
    intro q hq
    have hcard : q.p ^ q.exponent = 3 ^ 3 := by
      rw [← TauCeti.PrimePower.card_def, hq]; norm_num
    have hdvd : q.p ∣ 3 := by
      have : q.p ∣ 3 ^ 3 := by rw [← hcard]; exact dvd_pow_self q.p q.exponent_pos.ne'
      exact q.prime_p.dvd_of_dvd_pow this
    exact (Nat.prime_dvd_prime_iff_eq q.prime_p Nat.prime_three).1 hdvd
  cases d with
  | A r q =>
    rcases r with _ | _ | _ | r
    · exact h.elim
    · exact h.elim
    · simpa using key q h
    · exact h.elim
  | twistedA r q =>
    rcases r with _ | _ | _ | r
    · exact h.elim
    · exact h.elim
    · simpa using key q h
    · exact h.elim
  | reeG2 m => simp
  | B _ _ => exact h.elim
  | C _ _ => exact h.elim
  | D _ _ => exact h.elim
  | twistedD _ _ => exact h.elim
  | E6 _ => exact h.elim
  | E7 _ => exact h.elim
  | E8 _ => exact h.elim
  | F4 _ => exact h.elim
  | G2 _ => exact h.elim
  | twistedE6 _ => exact h.elim
  | trialityD4 _ => exact h.elim
  | suzuki _ => exact h.elim
  | reeF4 _ => exact h.elim
  | tits => exact h.elim

section Glue


theorem kdRank3_of_inputs {p : ℕ} (hp : p.Prime) (hp2 : p ≠ 2) (hField : KDRank3Field)
    (hSmall : KDRank3Small) : KDRank3 p := by
  intro S _ _ hs hna hChev hrank E hE hcard hnot
  have hE0 : Nat.card ↥(E ⊓ inner S) = p ^ 2 :=
    KDRank3Aux.card_inf_inner_eq hp hp2 hs hna hChev hrank hE hcard hnot
  rcases hChev with ⟨i, hi, ⟨e⟩⟩ | hamb
  · cases i with
    | cyclic _ _ => exact hi.elim
    | alternating _ _ => exact hi.elim
    | sporadic _ => exact hi.elim
    | lie d =>
      have hchar : d.1.characteristic = p := hi
      have hH := hField p hp hp2 S d ⟨e⟩ hchar hrank (KDRank3Amb.dvd_card_outer hp hE hnot)
      obtain ⟨dd, hv⟩ := d
      rcases hH with ⟨q, rfl⟩ | hsmall | ⟨q, rfl, hq3⟩
      · have hm := CFSG.Open.StatedAPI.statedClassicalModel_of_mulEquiv_typeA hv e
        have hqp : q.p = p := by simpa using hchar
        rw [hqp] at hm
        exact KDRank3L2.rank3Concl_linTwo hp hp2 hs hna hm hE hnot hE0
      · have hp3 : p = 3 := hchar.symm.trans (characteristic_eq_three_of_isRank3Small hsmall)
        subst hp3
        exact hSmall S ⟨dd, hv⟩ ⟨e⟩ hsmall E hE hcard hnot hE0
      · have h4 := kdD4TwoLocal_holds S q hv hq3 ⟨e⟩
        have hqp : q.p = p := by simpa using hchar
        have hp3 : p = 3 := hqp.symm.trans hq3
        have := q.exponent_pos
        subst hp3
        omega
  · exact (KDRank3Amb.rank3_amb_false hp hp2 hs hna hamb hE hnot hE0).elim

end Glue

end CFSG.LocalAnalysis.GLTheoremA
