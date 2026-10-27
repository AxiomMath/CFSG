module

public import CFSG.Open.GriessAllModelsStatement
import CFSG.RankThree.PartOne.N143.Inspect613Even
import CFSG.LocalAnalysis.QuasithinUnique.SQTK.UnitaryTauCeti
import CFSG.RankThree.PartTwo.Census.Carrier.SpinBOdd
import CFSG.RankThree.PartTwo.Census.Carrier.SpinTDOdd

public section

namespace CFSG.AGLEmbedding.FixedThree

open CFSG.Assembly.LowTwoRank CFSG.Blueprint.Multiplier
open CFSG.Open (GriessAllModelsStatement griessHopfMultiplier)

section Table

@[expose] def TagThree (t : StatedLieTag) (n p f : ℕ) : Prop :=
  (t = .PSL ∧ 3 ∣ Nat.gcd n (p ^ f - 1)) ∨ (t = .PSU ∧ 3 ∣ Nat.gcd n (p ^ f + 1)) ∨
  (t = .E6 ∧ 3 ∣ p ^ f - 1) ∨ (t = .twistedE6 ∧ 3 ∣ p ^ f + 1) ∨
  (t = .PSL ∧ n = 2 ∧ p = 3 ∧ f = 2) ∨ (t = .POmegaOdd ∧ n = 3 ∧ p = 3 ∧ f = 1) ∨
  (t = .G2 ∧ n = 0 ∧ p = 3 ∧ f = 1) ∨ (t = .PSU ∧ n = 4 ∧ p = 3 ∧ f = 1)

theorem not_three_dvd_gcd_two (x : ℕ) : ¬ 3 ∣ Nat.gcd 2 x := fun h =>
  absurd (Nat.le_of_dvd (by norm_num) (h.trans (Nat.gcd_dvd_left 2 x))) (by norm_num)

theorem not_three_dvd_gcd_four (x : ℕ) : ¬ 3 ∣ Nat.gcd 4 x := fun h =>
  absurd (h.trans (Nat.gcd_dvd_left 4 x)) (by norm_num)

theorem tagThree_of_dvd_orders (t : StatedLieTag) (n p f : ℕ)
    (h : 3 ∣ ((genericOrders t n p f).1 * (genericOrders t n p f).2) *
      ((exceptionalOrders t n p f).1 * (exceptionalOrders t n p f).2)) : TagThree t n p f := by
  rcases (Nat.Prime.dvd_mul Nat.prime_three).1 h with hg | he
  · cases t <;> simp [genericOrders] at hg <;> unfold TagThree <;> simp_all
    all_goals first
      | exact absurd hg (not_three_dvd_gcd_two _)
      | exact absurd hg (not_three_dvd_gcd_four _)
      | exact (Nat.dvd_gcd_iff.mp hg).2
      | (split_ifs at hg <;> simp_all [not_three_dvd_gcd_four])
  · unfold exceptionalOrders at he
    split at he <;> simp_all [TagThree]

theorem card_mult_zmod (a : ℕ) : Nat.card (Multiplicative (ZMod a)) = a :=
  (Nat.card_congr Multiplicative.toAdd).trans (Nat.card_zmod a)

theorem tagThree_of_lieModel (hGA : GriessAllModelsStatement) {K : Type} [Group K]
    {t : StatedLieTag} {n p f : ℕ} (hm : CFSG.Models.LieModel K t n p f)
    (h3 : 3 ∣ Nat.card (griessHopfMultiplier K)) : TagThree t n p f := by
  obtain ⟨-, ⟨φ⟩⟩ := hGA K t n p f hm
  rw [Nat.card_congr φ.toEquiv] at h3
  apply tagThree_of_dvd_orders
  simpa only [generic, exceptional, Nat.card_prod, card_mult_zmod] using h3

end Table

section Index

open TauCeti

@[expose] def LieThree (K : Type) [Group K] (d : ValidLieTypeIndex) : Prop :=
  (∃ n p f : ℕ, StatedClassicalModel K .PSL n p f ∧ 3 ∣ Nat.gcd n (p ^ f - 1)) ∨
  (∃ n p f : ℕ, StatedClassicalModel K .PSU n p f ∧ 3 ∣ Nat.gcd n (p ^ f + 1)) ∨
  (∃ (q : PrimePower) (hv : (LieTypeIndex.E6 q).Valid),
    d = ⟨.E6 q, hv⟩ ∧ 3 ∣ q.card - 1) ∨
  (∃ (q : PrimePower) (hv : (LieTypeIndex.twistedE6 q).Valid),
    d = ⟨.twistedE6 q, hv⟩ ∧ 3 ∣ q.card + 1) ∨
  (∃ (q : PrimePower) (hv : (LieTypeIndex.twistedA 3 q).Valid),
    d = ⟨.twistedA 3 q, hv⟩ ∧ q.card = 3) ∨
  (∃ (q : PrimePower) (hv : (LieTypeIndex.B 3 q).Valid), d = ⟨.B 3 q, hv⟩ ∧ q.card = 3) ∨
  (∃ (q : PrimePower) (hv : (LieTypeIndex.G2 q).Valid), d = ⟨.G2 q, hv⟩ ∧ q.card = 3)

theorem lieModel_of_names {K : Type} [Group K] {t : StatedLieTag} {p f : ℕ}
    (d : ValidLieTypeIndex) (hadm : StatedLieAdmissible t 0 p f)
    (hN : CFSG.Models.NamesTag d.1 t p f) (e : K ≃* d.Group) : CFSG.Models.LieModel K t 0 p f :=
  ⟨hadm, Or.inr ⟨rfl, d, hN, ⟨e⟩⟩⟩


theorem lieThree_of_index (hGA : GriessAllModelsStatement) (d : ValidLieTypeIndex) {K : Type}
    [Group K] (e : K ≃* (CFSGIndex.lie d).Group)
    (h3 : 3 ∣ Nat.card (griessHopfMultiplier K)) : LieThree K d := by
  obtain ⟨d, hv⟩ := d
  cases d with
  | A r q =>
    have hm := CFSG.RankThree.PartOne.N143.statedClassicalModel_of_isoLie_A hv e
    have key := tagThree_of_lieModel hGA ⟨hm.1, Or.inl hm⟩ h3
    unfold TagThree at key
    rcases key with ⟨-, hg⟩ | ⟨h, -⟩ | ⟨h, -⟩ | ⟨h, -⟩ | ⟨-, hn, hp, hf⟩ | ⟨h, -⟩ | ⟨h, -⟩ |
      ⟨h, -⟩
    · exact Or.inl ⟨_, _, _, hm, hg⟩
    · cases h
    · cases h
    · cases h
    · exfalso
      obtain rfl : r = 1 := by omega
      exact ((LieTypeIndex.valid_iff _).1 hv).2
        ((LieTypeIndex.isDuplicateRepresentative_iff _).2
          (Or.inl ⟨rfl, Or.inr (Or.inr (by rw [PrimePower.card_def, hp, hf]; norm_num))⟩))
    · cases h
    · cases h
    · cases h
  | twistedA r q =>
    have hm := CFSG.QuasithinUnique.SQTK.statedClassicalModel_twistedA r q hv e
    have key := tagThree_of_lieModel hGA ⟨hm.1, Or.inl hm⟩ h3
    unfold TagThree at key
    rcases key with ⟨h, -⟩ | ⟨-, hg⟩ | ⟨h, -⟩ | ⟨h, -⟩ | ⟨h, -⟩ | ⟨h, -⟩ | ⟨h, -⟩ |
      ⟨-, hn, hp, hf⟩
    · cases h
    · exact Or.inr (Or.inl ⟨_, _, _, hm, hg⟩)
    · cases h
    · cases h
    · cases h
    · cases h
    · cases h
    · obtain rfl : r = 3 := by omega
      exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inl
        ⟨q, hv, rfl, by rw [PrimePower.card_def, hp, hf]; norm_num⟩))))
  | B r q =>
    by_cases h2 : r = 2
    · subst h2
      have hm := CFSG.QuasithinUnique.SQTK.statedClassicalModel_typeB2 q hv e
      have key := tagThree_of_lieModel hGA ⟨hm.1, Or.inl hm⟩ h3
      exfalso
      unfold TagThree at key
      rcases key with ⟨h, -⟩ | ⟨h, -⟩ | ⟨h, -⟩ | ⟨h, -⟩ | ⟨h, -⟩ | ⟨h, -⟩ | ⟨h, -⟩ | ⟨h, -⟩ <;>
        cases h
    · have hrange := (LieTypeIndex.inStandardRange_iff _).1 ((LieTypeIndex.valid_iff _).1 hv).1
      by_cases hq : q.p = 2
      · have hm := CFSG.RankThree.PartTwo.Census.statedClassicalModel_typeB_even r q hv hq
          (by omega) e
        have key := tagThree_of_lieModel hGA ⟨hm.1, Or.inl hm⟩ h3
        exfalso
        unfold TagThree at key
        rcases key with ⟨h, -⟩ | ⟨h, -⟩ | ⟨h, -⟩ | ⟨h, -⟩ | ⟨h, -⟩ | ⟨h, -⟩ | ⟨h, -⟩ |
          ⟨h, -⟩ <;> cases h
      · have hm := CFSG.RankThree.PartTwo.Census.statedClassicalModel_typeB_odd r q hv hq
          (by omega) e
        have key := tagThree_of_lieModel hGA ⟨hm.1, Or.inl hm⟩ h3
        unfold TagThree at key
        rcases key with ⟨h, -⟩ | ⟨h, -⟩ | ⟨h, -⟩ | ⟨h, -⟩ | ⟨h, -⟩ | ⟨-, hn, hp, hf⟩ | ⟨h, -⟩ |
          ⟨h, -⟩
        · cases h
        · cases h
        · cases h
        · cases h
        · cases h
        · obtain rfl : r = 3 := by omega
          exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl
            ⟨q, hv, rfl, by rw [PrimePower.card_def, hp, hf]; norm_num⟩)))))
        · cases h
        · cases h
  | C r q =>
    have hm := CFSG.QuasithinUnique.SQTK.statedClassicalModel_typeC r q hv e
    have key := tagThree_of_lieModel hGA ⟨hm.1, Or.inl hm⟩ h3
    exfalso
    unfold TagThree at key
    rcases key with ⟨h, -⟩ | ⟨h, -⟩ | ⟨h, -⟩ | ⟨h, -⟩ | ⟨h, -⟩ | ⟨h, -⟩ | ⟨h, -⟩ | ⟨h, -⟩ <;>
      cases h
  | D r q =>
    have hm := CFSG.RankThree.PartTwo.Census.statedClassicalModel_typeD r q hv e
    have key := tagThree_of_lieModel hGA ⟨hm.1, Or.inl hm⟩ h3
    exfalso
    unfold TagThree at key
    rcases key with ⟨h, -⟩ | ⟨h, -⟩ | ⟨h, -⟩ | ⟨h, -⟩ | ⟨h, -⟩ | ⟨h, -⟩ | ⟨h, -⟩ | ⟨h, -⟩ <;>
      cases h
  | twistedD r q =>
    have hm := CFSG.RankThree.PartTwo.Census.statedClassicalModel_typeTwistedD r q hv e
    have key := tagThree_of_lieModel hGA ⟨hm.1, Or.inl hm⟩ h3
    exfalso
    unfold TagThree at key
    rcases key with ⟨h, -⟩ | ⟨h, -⟩ | ⟨h, -⟩ | ⟨h, -⟩ | ⟨h, -⟩ | ⟨h, -⟩ | ⟨h, -⟩ | ⟨h, -⟩ <;>
      cases h
  | E6 q =>
    have hm : CFSG.Models.LieModel K .E6 0 q.p q.exponent :=
      lieModel_of_names ⟨.E6 q, hv⟩ ⟨q.prime_p, q.exponent_pos, rfl⟩ ⟨rfl, rfl⟩ e
    have key := tagThree_of_lieModel hGA hm h3
    unfold TagThree at key
    rcases key with ⟨h, -⟩ | ⟨h, -⟩ | ⟨-, hg⟩ | ⟨h, -⟩ | ⟨h, -⟩ | ⟨h, -⟩ | ⟨h, -⟩ | ⟨h, -⟩
    · cases h
    · cases h
    · exact Or.inr (Or.inr (Or.inl ⟨q, hv, rfl, by simpa [PrimePower.card_def] using hg⟩))
    · cases h
    · cases h
    · cases h
    · cases h
    · cases h
  | E7 q =>
    have hm : CFSG.Models.LieModel K .E7 0 q.p q.exponent :=
      lieModel_of_names ⟨.E7 q, hv⟩ ⟨q.prime_p, q.exponent_pos, rfl⟩ ⟨rfl, rfl⟩ e
    have key := tagThree_of_lieModel hGA hm h3
    exfalso
    unfold TagThree at key
    rcases key with ⟨h, -⟩ | ⟨h, -⟩ | ⟨h, -⟩ | ⟨h, -⟩ | ⟨h, -⟩ | ⟨h, -⟩ | ⟨h, -⟩ | ⟨h, -⟩ <;>
      cases h
  | E8 q =>
    have hm : CFSG.Models.LieModel K .E8 0 q.p q.exponent :=
      lieModel_of_names ⟨.E8 q, hv⟩ ⟨q.prime_p, q.exponent_pos, rfl⟩ ⟨rfl, rfl⟩ e
    have key := tagThree_of_lieModel hGA hm h3
    exfalso
    unfold TagThree at key
    rcases key with ⟨h, -⟩ | ⟨h, -⟩ | ⟨h, -⟩ | ⟨h, -⟩ | ⟨h, -⟩ | ⟨h, -⟩ | ⟨h, -⟩ | ⟨h, -⟩ <;>
      cases h
  | F4 q =>
    have hm : CFSG.Models.LieModel K .F4 0 q.p q.exponent :=
      lieModel_of_names ⟨.F4 q, hv⟩ ⟨q.prime_p, q.exponent_pos, rfl⟩ ⟨rfl, rfl⟩ e
    have key := tagThree_of_lieModel hGA hm h3
    exfalso
    unfold TagThree at key
    rcases key with ⟨h, -⟩ | ⟨h, -⟩ | ⟨h, -⟩ | ⟨h, -⟩ | ⟨h, -⟩ | ⟨h, -⟩ | ⟨h, -⟩ | ⟨h, -⟩ <;>
      cases h
  | G2 q =>
    have hq3 : 3 ≤ q.card :=
      (LieTypeIndex.inStandardRange_iff _).1 ((LieTypeIndex.valid_iff _).1 hv).1
    have hm : CFSG.Models.LieModel K .G2 0 q.p q.exponent :=
      lieModel_of_names ⟨.G2 q, hv⟩
        ⟨q.prime_p, q.exponent_pos, rfl, by rw [← PrimePower.card_def]; exact hq3⟩ ⟨rfl, rfl⟩ e
    have key := tagThree_of_lieModel hGA hm h3
    unfold TagThree at key
    rcases key with ⟨h, -⟩ | ⟨h, -⟩ | ⟨h, -⟩ | ⟨h, -⟩ | ⟨h, -⟩ | ⟨h, -⟩ | ⟨-, -, hp, hf⟩ |
      ⟨h, -⟩
    · cases h
    · cases h
    · cases h
    · cases h
    · cases h
    · cases h
    · exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr
        ⟨q, hv, rfl, by rw [PrimePower.card_def, hp, hf]; norm_num⟩)))))
    · cases h
  | twistedE6 q =>
    have hm : CFSG.Models.LieModel K .twistedE6 0 q.p q.exponent :=
      lieModel_of_names ⟨.twistedE6 q, hv⟩ ⟨q.prime_p, q.exponent_pos, rfl⟩ ⟨rfl, rfl⟩ e
    have key := tagThree_of_lieModel hGA hm h3
    unfold TagThree at key
    rcases key with ⟨h, -⟩ | ⟨h, -⟩ | ⟨h, -⟩ | ⟨-, hg⟩ | ⟨h, -⟩ | ⟨h, -⟩ | ⟨h, -⟩ | ⟨h, -⟩
    · cases h
    · cases h
    · cases h
    · exact Or.inr (Or.inr (Or.inr (Or.inl ⟨q, hv, rfl, by simpa [PrimePower.card_def] using hg⟩)))
    · cases h
    · cases h
    · cases h
    · cases h
  | trialityD4 q =>
    have hm : CFSG.Models.LieModel K .trialityD4 0 q.p q.exponent :=
      lieModel_of_names ⟨.trialityD4 q, hv⟩ ⟨q.prime_p, q.exponent_pos, rfl⟩ ⟨rfl, rfl⟩ e
    have key := tagThree_of_lieModel hGA hm h3
    exfalso
    unfold TagThree at key
    rcases key with ⟨h, -⟩ | ⟨h, -⟩ | ⟨h, -⟩ | ⟨h, -⟩ | ⟨h, -⟩ | ⟨h, -⟩ | ⟨h, -⟩ | ⟨h, -⟩ <;>
      cases h
  | suzuki m =>
    have hm1 : 1 ≤ m := (LieTypeIndex.inStandardRange_iff _).1 ((LieTypeIndex.valid_iff _).1 hv).1
    have hm : CFSG.Models.LieModel K .twistedB2 0 2 (2 * m + 1) :=
      lieModel_of_names ⟨.suzuki m, hv⟩
        ⟨Nat.prime_two, by omega, rfl, rfl, ⟨m, rfl⟩, by omega⟩ ⟨rfl, rfl⟩ e
    have key := tagThree_of_lieModel hGA hm h3
    exfalso
    unfold TagThree at key
    rcases key with ⟨h, -⟩ | ⟨h, -⟩ | ⟨h, -⟩ | ⟨h, -⟩ | ⟨h, -⟩ | ⟨h, -⟩ | ⟨h, -⟩ | ⟨h, -⟩ <;>
      cases h
  | reeG2 m =>
    have hm1 : 1 ≤ m := (LieTypeIndex.inStandardRange_iff _).1 ((LieTypeIndex.valid_iff _).1 hv).1
    have hm : CFSG.Models.LieModel K .twistedG2 0 3 (2 * m + 1) :=
      lieModel_of_names ⟨.reeG2 m, hv⟩
        ⟨Nat.prime_three, by omega, rfl, rfl, ⟨m, rfl⟩, by omega⟩ ⟨rfl, rfl⟩ e
    have key := tagThree_of_lieModel hGA hm h3
    exfalso
    unfold TagThree at key
    rcases key with ⟨h, -⟩ | ⟨h, -⟩ | ⟨h, -⟩ | ⟨h, -⟩ | ⟨h, -⟩ | ⟨h, -⟩ | ⟨h, -⟩ | ⟨h, -⟩ <;>
      cases h
  | reeF4 m =>
    have hm1 : 1 ≤ m := (LieTypeIndex.inStandardRange_iff _).1 ((LieTypeIndex.valid_iff _).1 hv).1
    have hm : CFSG.Models.LieModel K .twistedF4 0 2 (2 * m + 1) :=
      lieModel_of_names ⟨.reeF4 m, hv⟩
        ⟨Nat.prime_two, by omega, rfl, rfl, ⟨m, rfl⟩, by omega⟩ ⟨rfl, rfl⟩ e
    have key := tagThree_of_lieModel hGA hm h3
    exfalso
    unfold TagThree at key
    rcases key with ⟨h, -⟩ | ⟨h, -⟩ | ⟨h, -⟩ | ⟨h, -⟩ | ⟨h, -⟩ | ⟨h, -⟩ | ⟨h, -⟩ | ⟨h, -⟩ <;>
      cases h
  | tits =>
    have hm : CFSG.Models.LieModel K .Tits 0 2 1 :=
      lieModel_of_names ⟨.tits, hv⟩ ⟨Nat.prime_two, le_rfl, rfl, rfl, rfl⟩ ⟨rfl, rfl⟩ e
    have key := tagThree_of_lieModel hGA hm h3
    exfalso
    unfold TagThree at key
    rcases key with ⟨h, -⟩ | ⟨h, -⟩ | ⟨h, -⟩ | ⟨h, -⟩ | ⟨h, -⟩ | ⟨h, -⟩ | ⟨h, -⟩ | ⟨h, -⟩ <;>
      cases h

end Index

end CFSG.AGLEmbedding.FixedThree
