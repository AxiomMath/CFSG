module

public import CFSG.LocalAnalysis.RankThreeTheoremC.SmallRankE3.FongLeviE3Out
public import CFSG.LocalAnalysis.RankThreeTheoremC.SmallRankE3.FongLeviSetting
public import CFSG.LocalAnalysis.RankThreeTheoremC.SmallRankE3.FongNoncycE3Rank

public section

namespace CFSG.LocalAnalysis.RankThreeTheoremC.SmallRankE3.FongLevi

open TauCeti Subgroup CFSG.Open
open CFSG.LocalAnalysis.RankFourTheoremC.PEmpty (S622IsSimpleSection IsParabolicTwo)
open CFSG.Yardstones.Md0ec50421ce4 (IsChevSimple catalogIs onLie ambiguousChev)

structure E3Inputs : Prop where
  a1 : ∀ {A : Type} [Group A] [Finite A] {K K₀ B : Subgroup A} {z : A} {p : ℕ},
    E3Setting K K₀ B z p → ∀ {q : PrimePower}, q.p = 2 → ∀ (hv : (LieTypeIndex.A 1 q).Valid),
      Nonempty (↥K ≃* ValidLieTypeIndex.Group ⟨.A 1 q, hv⟩) → False
  a3 : ∀ {A : Type} [Group A] [Finite A] {K K₀ B : Subgroup A} {z : A} {p : ℕ},
    E3Setting K K₀ B z p → ∀ {q : PrimePower}, q.p = 2 → ∀ (hv : (LieTypeIndex.A 3 q).Valid),
      Nonempty (↥K ≃* ValidLieTypeIndex.Group ⟨.A 3 q, hv⟩) → E3Concl K₀ B z p
  aBig : ∀ {A : Type} [Group A] [Finite A] {K K₀ B : Subgroup A} {z : A} {p : ℕ},
    E3Setting K K₀ B z p → ∀ {n : ℕ}, 4 ≤ n → ∀ {q : PrimePower}, q.p = 2 → Odd q.exponent →
      ∀ (hv : (LieTypeIndex.A n q).Valid),
        Nonempty (↥K ≃* ValidLieTypeIndex.Group ⟨.A n q, hv⟩) → False
  tA2 : ∀ {A : Type} [Group A] [Finite A] {K K₀ B : Subgroup A} {z : A} {p : ℕ},
    E3Setting K K₀ B z p → ∀ {q : PrimePower}, q.p = 2 → ∀ (hv : (LieTypeIndex.twistedA 2 q).Valid),
      Nonempty (↥K ≃* ValidLieTypeIndex.Group ⟨.twistedA 2 q, hv⟩) → False
  tABig : ∀ {A : Type} [Group A] [Finite A] {K K₀ B : Subgroup A} {z : A} {p : ℕ},
    E3Setting K K₀ B z p → ∀ {n : ℕ}, 4 ≤ n → ∀ {q : PrimePower}, q.p = 2 →
      ∀ (hv : (LieTypeIndex.twistedA n q).Valid),
        Nonempty (↥K ≃* ValidLieTypeIndex.Group ⟨.twistedA n q, hv⟩) → False
  b2 : ∀ {A : Type} [Group A] [Finite A] {K K₀ B : Subgroup A} {z : A} {p : ℕ},
    E3Setting K K₀ B z p → ∀ {q : PrimePower}, q.p = 2 → ∀ (hv : (LieTypeIndex.B 2 q).Valid),
      Nonempty (↥K ≃* ValidLieTypeIndex.Group ⟨.B 2 q, hv⟩) → False
  b3 : ∀ {A : Type} [Group A] [Finite A] {K K₀ B : Subgroup A} {z : A} {p : ℕ},
    E3Setting K K₀ B z p → ∀ {q : PrimePower}, q.p = 2 → ∀ (hv : (LieTypeIndex.B 3 q).Valid),
      Nonempty (↥K ≃* ValidLieTypeIndex.Group ⟨.B 3 q, hv⟩) → E3Concl K₀ B z p
  bBig : ∀ {A : Type} [Group A] [Finite A] {K K₀ B : Subgroup A} {z : A} {p : ℕ},
    E3Setting K K₀ B z p → ∀ {n : ℕ}, 4 ≤ n → ∀ {q : PrimePower}, q.p = 2 →
      ∀ (hv : (LieTypeIndex.B n q).Valid),
        Nonempty (↥K ≃* ValidLieTypeIndex.Group ⟨.B n q, hv⟩) → False
  tD4 : ∀ {A : Type} [Group A] [Finite A] {K K₀ B : Subgroup A} {z : A} {p : ℕ},
    E3Setting K K₀ B z p → ∀ {q : PrimePower}, q.p = 2 → ∀ (hv : (LieTypeIndex.twistedD 4 q).Valid),
      Nonempty (↥K ≃* ValidLieTypeIndex.Group ⟨.twistedD 4 q, hv⟩) → E3Concl K₀ B z p
  g2 : ∀ {A : Type} [Group A] [Finite A] {K K₀ B : Subgroup A} {z : A} {p : ℕ},
    E3Setting K K₀ B z p → ∀ {q : PrimePower}, q.p = 2 → ∀ (hv : (LieTypeIndex.G2 q).Valid),
      Nonempty (↥K ≃* ValidLieTypeIndex.Group ⟨.G2 q, hv⟩) → False
  tri : ∀ {A : Type} [Group A] [Finite A] {K K₀ B : Subgroup A} {z : A} {p : ℕ},
    E3Setting K K₀ B z p → ∀ {q : PrimePower}, q.p = 2 → ∀ (hv : (LieTypeIndex.trialityD4 q).Valid),
      Nonempty (↥K ≃* ValidLieTypeIndex.Group ⟨.trialityD4 q, hv⟩) → False
  suz : ∀ {A : Type} [Group A] [Finite A] {K K₀ B : Subgroup A} {z : A} {p : ℕ},
    E3Setting K K₀ B z p → ∀ {m : ℕ} (hv : (LieTypeIndex.suzuki m).Valid),
      Nonempty (↥K ≃* ValidLieTypeIndex.Group ⟨.suzuki m, hv⟩) → False
  ree : ∀ {A : Type} [Group A] [Finite A] {K K₀ B : Subgroup A} {z : A} {p : ℕ},
    E3Setting K K₀ B z p → ∀ {m : ℕ} (hv : (LieTypeIndex.reeF4 m).Valid),
      Nonempty (↥K ≃* ValidLieTypeIndex.Group ⟨.reeF4 m, hv⟩) → False
  tits : ∀ {A : Type} [Group A] [Finite A] {K K₀ B : Subgroup A} {z : A} {p : ℕ},
    E3Setting K K₀ B z p → ∀ (hv : LieTypeIndex.tits.Valid),
      Nonempty (↥K ≃* ValidLieTypeIndex.Group ⟨.tits, hv⟩) → False
  alt : ∀ {A : Type} [Group A] [Finite A] {K K₀ B : Subgroup A} {z : A} {p : ℕ},
    E3Setting K K₀ B z p → ∀ {n : ℕ} (hn : 5 ≤ n), (n = 5 ∨ n = 6 ∨ n = 8) →
      Nonempty (↥K ≃* alternatingGroup (Fin n)) → False
  a1seven : ∀ {A : Type} [Group A] [Finite A] {K K₀ B : Subgroup A} {z : A} {p : ℕ},
    E3Setting K K₀ B z p → ∀ {q : PrimePower}, q.card = 7 → ∀ (hv : (LieTypeIndex.A 1 q).Valid),
      Nonempty (↥K ≃* ValidLieTypeIndex.Group ⟨.A 1 q, hv⟩) → False
  tA2three : ∀ {A : Type} [Group A] [Finite A] {K K₀ B : Subgroup A} {z : A} {p : ℕ},
    E3Setting K K₀ B z p → ∀ {q : PrimePower}, q.card = 3 →
      ∀ (hv : (LieTypeIndex.twistedA 2 q).Valid),
        Nonempty (↥K ≃* ValidLieTypeIndex.Group ⟨.twistedA 2 q, hv⟩) → False


section Assembly

set_option linter.unusedSectionVars false


theorem kFactGammaLeviE3_of_inputs (I : E3Inputs) :
    CFSG.LocalAnalysis.RankThreeTheoremC.SmallRankE3.KFactGammaLeviE3 := by
  intro A _ _ K K₀ B z p hchev hp hp5 hKr hz hzK₀ hpar hne hcore hB hBc hzB hBK hBK₀ hnb hℓ
  have S : E3Setting K K₀ B z p :=
    ⟨hp, hp5, hKr, hz, hzK₀, hpar, hne, hcore, hB, hBc, hzB, hBK, hBK₀, hnb, hℓ⟩
  have h3 : catalogIs ↥K (onLie CFSG.LocalAnalysis.RankThreeTheoremC.SmallRankE3.KGThreeRankBig) →
      False := by
    intro h
    have h1 := CFSG.LocalAnalysis.RankThreeTheoremC.SmallRankE3.FongNoncyc.four_le_pRank_three_of_big h
    have h2 : CFSG.Open.pRank 3 K ≤ 3 := hℓ 3 Nat.prime_three (by norm_num)
    rw [CFSG.SectionRank.pRank_eq_pRank_top_subgroup K] at h2
    omega
  suffices hmain : E3Concl K₀ B z p from hmain
  rcases hchev with ⟨i, hi, ⟨e⟩⟩ | ⟨i, hi, ⟨e⟩⟩
  · cases i with
    | cyclic _ _ => exact absurd hi (by simp [onLie])
    | alternating _ _ => exact absurd hi (by simp [onLie])
    | sporadic _ => exact absurd hi (by simp [onLie])
    | lie dd =>
      obtain ⟨d, hv⟩ := dd
      change d.characteristic = 2 at hi
      have hr := (LieTypeIndex.inStandardRange_iff _).mp ((LieTypeIndex.valid_iff _).mp hv).1
      cases d with
      | A n q =>
        have hp2 : q.p = 2 := by simpa using hi
        have hn1 : 1 ≤ n := hr.1
        rcases Nat.lt_or_ge n 4 with hn4 | hn4
        · interval_cases n
          · exact (I.a1 S hp2 hv ⟨e⟩).elim
          · exact l3_e3_full hp hp5 hKr hz hzK₀ hpar hne hB hBc hBK hBK₀ hnb hp2 hv e
          · exact I.a3 S hp2 hv ⟨e⟩
        · by_cases hev : Even q.exponent
          · exact (h3 ⟨.lie ⟨.A n q, hv⟩, ⟨hn4, hp2, hev⟩, ⟨e⟩⟩).elim
          · exact (I.aBig S hn4 hp2 (Nat.not_even_iff_odd.mp hev) hv ⟨e⟩).elim
      | twistedA n q =>
        have hp2 : q.p = 2 := by simpa using hi
        have hn2 : 2 ≤ n := hr.1
        rcases Nat.lt_or_ge n 4 with hn4 | hn4
        · interval_cases n
          · exact (I.tA2 S hp2 hv ⟨e⟩).elim
          · exact u4_e3_full hp hp5 hKr hz hzK₀ hpar hne hB hBc hBK hBK₀ hnb hp2 hv e
        · exact (I.tABig S hn4 hp2 hv ⟨e⟩).elim
      | B n q =>
        have hp2 : q.p = 2 := by simpa using hi
        have hn2 : 2 ≤ n := hr.1
        rcases Nat.lt_or_ge n 4 with hn4 | hn4
        · interval_cases n
          · exact (I.b2 S hp2 hv ⟨e⟩).elim
          · exact I.b3 S hp2 hv ⟨e⟩
        · exact (I.bBig S hn4 hp2 hv ⟨e⟩).elim
      | C n q =>
        exfalso
        have hp2 : q.p = 2 := by simpa using hi
        exact hr.2 hp2
      | D n q =>
        have hp2 : q.p = 2 := by simpa using hi
        exact (h3 ⟨.lie ⟨.D n q, hv⟩, hp2, ⟨e⟩⟩).elim
      | twistedD n q =>
        have hp2 : q.p = 2 := by simpa using hi
        have hn4 : 4 ≤ n := hr
        by_cases hn5 : 5 ≤ n
        · exact (h3 ⟨.lie ⟨.twistedD n q, hv⟩, ⟨hn5, hp2⟩, ⟨e⟩⟩).elim
        · have hn : n = 4 := by omega
          subst hn
          exact I.tD4 S hp2 hv ⟨e⟩
      | E6 q => exact (h3 ⟨.lie ⟨.E6 q, hv⟩, trivial, ⟨e⟩⟩).elim
      | E7 q => exact (h3 ⟨.lie ⟨.E7 q, hv⟩, trivial, ⟨e⟩⟩).elim
      | E8 q => exact (h3 ⟨.lie ⟨.E8 q, hv⟩, trivial, ⟨e⟩⟩).elim
      | F4 q => exact (h3 ⟨.lie ⟨.F4 q, hv⟩, trivial, ⟨e⟩⟩).elim
      | twistedE6 q => exact (h3 ⟨.lie ⟨.twistedE6 q, hv⟩, trivial, ⟨e⟩⟩).elim
      | G2 q => exact (I.g2 S (by simpa using hi) hv ⟨e⟩).elim
      | trialityD4 q => exact (I.tri S (by simpa using hi) hv ⟨e⟩).elim
      | reeG2 m => exact absurd hi (by simp)
      | suzuki m => exact (I.suz S hv ⟨e⟩).elim
      | reeF4 m => exact (I.ree S hv ⟨e⟩).elim
      | tits => exact (I.tits S hv ⟨e⟩).elim
  · cases i with
    | cyclic _ _ => exact absurd hi (by simp [ambiguousChev])
    | sporadic _ => exact absurd hi (by simp [ambiguousChev])
    | alternating n hn5 =>
      rcases hi with ⟨h5, -⟩ | ⟨h6, -⟩ | ⟨h8, -⟩
      · exact (I.alt S hn5 (Or.inl h5) ⟨e⟩).elim
      · exact (I.alt S hn5 (Or.inr (Or.inl h6)) ⟨e⟩).elim
      · exact (I.alt S hn5 (Or.inr (Or.inr h8)) ⟨e⟩).elim
    | lie dd =>
      obtain ⟨d, hv⟩ := dd
      change ambiguousChev 2 (.lie ⟨d, hv⟩) at hi
      cases d with
      | A r q =>
        by_cases hr1 : r = 1
        · subst hr1
          rcases hi with ⟨h7, -⟩ | ⟨-, h23⟩
          · exact (I.a1seven S h7 hv ⟨e⟩).elim
          · exact absurd h23 (by norm_num)
        · exfalso
          simp [ambiguousChev, hr1] at hi
      | twistedA r q =>
        rcases Nat.lt_or_ge r 4 with h4 | h4
        · interval_cases r
          · exact hi.elim
          · exact hi.elim
          · exact (I.tA2three S hi.1 hv ⟨e⟩).elim
          · exact absurd hi.2 (by norm_num)
        · obtain ⟨r', rfl⟩ := Nat.exists_eq_add_of_le' h4
          exact False.elim hi
      | _ => exact absurd hi (by simp [ambiguousChev])

end Assembly

end CFSG.LocalAnalysis.RankThreeTheoremC.SmallRankE3.FongLevi
