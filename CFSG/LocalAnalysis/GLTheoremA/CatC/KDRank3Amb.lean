module

public import CFSG.LocalAnalysis.GLTheoremA.CatC.KDRank3L2Model
public import CFSG.RankThree.PartTwo.Sec4.T444.Item434AltSix
public import CFSG.Adapters.LinearCatalogStated

public section

namespace CFSG.LocalAnalysis.GLTheoremA

open CFSG.Open CFSG.Yardstones.Md0ec50421ce4
open CFSG.ComponentClassification.OuterAutomorphisms (inner Outer)

namespace KDRank3Amb

theorem dvd_card_outer {p : ℕ} (hp : p.Prime) {S : Type} [Group S] {E : Subgroup (MulAut S)}
    (hE : IsElemAbelian p E) (hnot : ¬ E ≤ inner S) : p ∣ Nat.card (Outer S) := by
  haveI : Fact p.Prime := ⟨hp⟩
  obtain ⟨x, hxE, hxI⟩ := Set.not_subset.1 hnot
  have hx1 : (QuotientGroup.mk x : Outer S) ≠ 1 := fun h => hxI ((QuotientGroup.eq_one_iff x).1 h)
  have hxp : (QuotientGroup.mk x : Outer S) ^ p = 1 := by
    rw [← QuotientGroup.mk_pow, hE.2 x hxE, QuotientGroup.mk_one]
  have := orderOf_dvd_natCard (QuotientGroup.mk x : Outer S)
  rwa [orderOf_eq_prime hxp hx1] at this

theorem p_exponent_of_card_two {q : TauCeti.PrimePower} (hq : q.card = 2) :
    q.p = 2 ∧ q.exponent = 1 := by
  have hcard : q.p ^ q.exponent = 2 := by rw [← TauCeti.PrimePower.card_def]; exact hq
  have hp : q.p = 2 := by
    have hdvd : q.p ∣ 2 := by
      rw [← hcard]
      exact dvd_pow_self q.p q.exponent_pos.ne'
    exact (Nat.prime_dvd_prime_iff_eq q.prime_p Nat.prime_two).1 hdvd
  refine ⟨hp, ?_⟩
  rw [hp] at hcard
  exact Nat.pow_right_injective (le_refl 2) (show 2 ^ q.exponent = 2 ^ 1 by simpa using hcard)

theorem p_exponent_of_card_eight {q : TauCeti.PrimePower} (hq : q.card = 8) :
    q.p = 2 ∧ q.exponent = 3 := by
  have hcard : q.p ^ q.exponent = 2 ^ 3 := by rw [← TauCeti.PrimePower.card_def, hq]; norm_num
  have hp : q.p = 2 := by
    have hdvd : q.p ∣ 2 := by
      have : q.p ∣ 2 ^ 3 := by rw [← hcard]; exact dvd_pow_self q.p q.exponent_pos.ne'
      exact q.prime_p.dvd_of_dvd_pow this
    exact (Nat.prime_dvd_prime_iff_eq q.prime_p Nat.prime_two).1 hdvd
  refine ⟨hp, ?_⟩
  rw [hp] at hcard
  exact Nat.pow_right_injective (le_refl 2) hcard

section U42


theorem card_outer_u42 {S : Type} [Group S] (hs : IsSimpleGroup S) (hna : ∃ a b : S, a * b ≠ b * a)
    (h : Blueprint.LieModel S .PSU 4 2 1) : Nat.card (Outer S) = 2 := by
  obtain ⟨hAut, hS⟩ := CFSG.EvenSporadicStandard.M22Std.card_mulAut_of_lieModel_psu42 h
  have hZ : Subgroup.center S = ⊥ := KDRank3L2.center_eq_bot_of_simple hs hna
  have hconj := KDRank3L2.conj_injective_of_center_eq_bot hZ
  have hinner : Nat.card (inner S) = Nat.card S := Nat.card_range_of_injective hconj
  have hidx := (inner S).card_mul_index
  have hO : (inner S).index = Nat.card (Outer S) := rfl
  rw [hinner, hS, hAut, hO] at hidx
  omega

end U42

theorem rank3_amb_false {p : ℕ} (hp : p.Prime) (hp2 : p ≠ 2)
    {S : Type} [Group S] [Finite S] (hs : IsSimpleGroup S) (hna : ∃ a b : S, a * b ≠ b * a)
    (hamb : catalogIs S (ambiguousChev p)) {E : Subgroup (MulAut S)} (hE : IsElemAbelian p E)
    (hnot : ¬ E ≤ inner S) (hE0 : Nat.card ↥(E ⊓ inner S) = p ^ 2) : False := by
  have hdvd := dvd_card_outer hp hE hnot
  obtain ⟨i, hi, ⟨e⟩⟩ := hamb
  cases i with
  | cyclic _ _ => simp [ambiguousChev] at hi
  | sporadic _ => simp [ambiguousChev] at hi
  | alternating n hn5 =>
    simp only [ambiguousChev] at hi
    have hOut : Nat.card (Outer S) = Nat.card (Outer (alternatingGroup (Fin n))) :=
      Nat.card_congr (CFSG.ComponentClassification.OuterAutomorphisms.equivalence e).toEquiv
    rw [hOut] at hdvd
    rcases hi with ⟨rfl, h5⟩ | ⟨rfl, h6⟩ | ⟨rfl, h8⟩
    · have hp5 : p = 5 := by
        rcases h5 with h | h
        · exact absurd h hp2
        · exact h
      subst hp5
      have hle := CFSG.RankThree.PartOne.card_outer_alternating_le_four (n := 5) le_rfl
      have hpos : 0 < Nat.card (Outer (alternatingGroup (Fin 5))) := Nat.card_pos
      have := Nat.le_of_dvd hpos hdvd
      omega
    · have hp3 : p = 3 := by
        rcases h6 with h | h
        · exact absurd h hp2
        · exact h
      subst hp3
      exact CFSG.RankThree.PartTwo.Sec4.Item434Alt.not_three_dvd_card_outer_six hdvd
    · exact hp2 h8
  | lie d =>
    obtain ⟨dd, hv⟩ := d
    cases dd with
    | A r q =>
      rcases r with _ | _ | r
      · simp [ambiguousChev] at hi
      · simp only [ambiguousChev] at hi
        rcases hi with ⟨-, h2⟩ | ⟨h8, h3⟩
        · exact absurd h2 hp2
        · subst h3
          obtain ⟨hq2, hq3⟩ := p_exponent_of_card_eight h8
          have hm := CFSG.Open.StatedAPI.statedClassicalModel_of_mulEquiv_typeA hv e
          rw [hq2, hq3] at hm
          obtain ⟨f₀, hff₀, hnum⟩ := KDRank3L2.exists_numerator_dvd hp hp2 hs hna hm hE hnot hE0
          have hf₀ : f₀ = 1 := by omega
          subst hf₀
          norm_num [CFSG.ComponentClassification.CatLeaf.lieOrderNumerator] at hnum
      · simp [ambiguousChev] at hi
    | twistedA r q =>
      rcases r with _ | _ | _ | _ | r
      · simp [ambiguousChev] at hi
      · simp [ambiguousChev] at hi
      · simp only [ambiguousChev] at hi
        exact hp2 hi.2
      · simp only [ambiguousChev] at hi
        obtain ⟨hq2, hp3⟩ := hi
        subst hp3
        obtain ⟨hp', hf'⟩ := p_exponent_of_card_two hq2
        have h := CFSG.QuasithinUnique.SQTK.statedClassicalModel_twistedA 3 q hv e
        rw [hp', hf'] at h
        have hmodel : Blueprint.LieModel S .PSU 4 2 1 := Or.inl ⟨by decide, h⟩
        rw [card_outer_u42 hs hna hmodel] at hdvd
        omega
      · simp [ambiguousChev] at hi
    | _ => simp [ambiguousChev] at hi

end KDRank3Amb

end CFSG.LocalAnalysis.GLTheoremA
