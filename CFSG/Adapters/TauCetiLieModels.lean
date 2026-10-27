module

public import CFSG.Models
import CFSG.Adapters.LinearCatalog
import CFSG.LocalAnalysis.QuasithinUnique.SQTK.UnitaryTauCeti
import CFSG.RankThree.PartTwo.Census.Carrier.SpinBOdd
import CFSG.RankThree.PartTwo.Census.Carrier.SpinTDOdd

public section

namespace CFSG.Models

open TauCeti Assembly.LowTwoRank

theorem oddLieType_or_evenLieType_of_lieModel {G : Type} [Group G] {t : StatedLieTag}
    {n p f : ℕ} (h : LieModel G t n p f) : OddLieType G ∨ EvenLieType G := by
  by_cases hp : p = 2
  · subst hp
    exact .inr ⟨t, n, f, h⟩
  · exact .inl ⟨t, n, p, f, hp, h⟩

theorem lieModel_of_statedClassicalModel {G : Type} [Group G] {t : StatedLieTag} {n p f : ℕ}
    (h : StatedClassicalModel G t n p f) : LieModel G t n p f :=
  ⟨h.1, .inl h⟩

theorem lieModel_of_namesTag {G : Type} [Group G] {t : StatedLieTag} {p f : ℕ}
    (hadm : StatedLieAdmissible t 0 p f) (d : ValidLieTypeIndex) (hd : NamesTag d.1 t p f)
    (e : G ≃* d.Group) : LieModel G t 0 p f :=
  ⟨hadm, .inr ⟨rfl, d, hd, ⟨e⟩⟩⟩

theorem card_fixedField_of {d : ValidLieTypeIndex} {q : PrimePower}
    (h1 : d.1.characteristic = q.p) (h2 : d.1.fieldExponent = q.exponent) :
    Nat.card ↥(ValidLieTypeIndex.fixedField d) = q.p ^ q.exponent := by
  rw [ValidLieTypeIndex.card_fixedField, ValidLieTypeIndex.fieldOrder_eq_characteristic_pow,
    ValidLieTypeIndex.characteristic, ValidLieTypeIndex.fieldExponent, h1, h2]

theorem card_galoisField (q : PrimePower) [Fact q.p.Prime] :
    Nat.card (GaloisField q.p q.exponent) = q.p ^ q.exponent :=
  GaloisField.card q.p q.exponent q.exponent_pos.ne'

theorem lieModel_A {G : Type} [Group G] (r : ℕ) (q : PrimePower)
    (hv : (LieTypeIndex.A r q).Valid) (e : G ≃* ValidLieTypeIndex.Group ⟨.A r q, hv⟩) :
    LieModel G .PSL (r + 1) q.p q.exponent := by
  have : Fact q.p.Prime := ⟨q.prime_p⟩
  have hr := (LieTypeIndex.inStandardRange_iff _).mp ((LieTypeIndex.valid_iff _).mp hv).1
  have hq : q.card = q.p ^ q.exponent := PrimePower.card_def q
  refine lieModel_of_statedClassicalModel ⟨⟨q.prime_p, q.exponent_pos, by omega, ?_, ?_⟩,
    GaloisField q.p q.exponent, inferInstance, inferInstance, card_galoisField q,
    ⟨e.trans ((CFSG.ClassicalModels.linearCatalogCandidateEquivPSL r q hv).trans
      (projectiveSpecialLinearGroupEquivStatedProj _ _))⟩⟩
  · intro h
    simp only [Prod.mk.injEq] at h
    have := hr.2 (by omega)
    omega
  · intro h
    simp only [Prod.mk.injEq] at h
    have := hr.2 (by omega)
    omega

theorem lieModel_twistedA {G : Type} [Group G] (r : ℕ) (q : PrimePower)
    (hv : (LieTypeIndex.twistedA r q).Valid)
    (e : G ≃* ValidLieTypeIndex.Group ⟨.twistedA r q, hv⟩) :
    LieModel G .PSU (r + 1) (ValidLieTypeIndex.characteristic ⟨.twistedA r q, hv⟩)
      (ValidLieTypeIndex.fieldExponent ⟨.twistedA r q, hv⟩) := by
  have hr := (LieTypeIndex.inStandardRange_iff _).mp ((LieTypeIndex.valid_iff _).mp hv).1
  have hq : q.card = q.p ^ q.exponent := PrimePower.card_def q
  have hc : ValidLieTypeIndex.characteristic ⟨.twistedA r q, hv⟩ = q.p :=
    LieTypeIndex.characteristic_twistedA r q
  have hf : ValidLieTypeIndex.fieldExponent ⟨.twistedA r q, hv⟩ = q.exponent :=
    LieTypeIndex.fieldExponent_twistedA r q
  have hf0 := ValidLieTypeIndex.fieldExponent_pos ⟨.twistedA r q, hv⟩
  refine lieModel_of_statedClassicalModel ⟨⟨ValidLieTypeIndex.characteristic_prime _, hf0,
    by omega, ?_⟩, _, inferInstance, inferInstance, ?_,
    ⟨e.trans (CFSG.QuasithinUnique.SQTK.typeTwistedAGroupEquivStatedProj r q hv)⟩⟩
  · intro h
    simp only [Prod.mk.injEq] at h
    rw [hc, hf] at h
    have := hr.2 (by omega)
    omega
  · rw [GaloisField.card _ _ (by omega)]
    ring

theorem lieModel_B {G : Type} [Group G] (r : ℕ) (q : PrimePower)
    (hv : (LieTypeIndex.B r q).Valid) (e : G ≃* ValidLieTypeIndex.Group ⟨.B r q, hv⟩) :
    LieModel G .PSp r q.p q.exponent ∨ LieModel G .POmegaOdd r q.p q.exponent := by
  have hr := (LieTypeIndex.inStandardRange_iff _).mp ((LieTypeIndex.valid_iff _).mp hv).1
  have hq : q.card = q.p ^ q.exponent := PrimePower.card_def q
  have hK : Nat.card ↥(ValidLieTypeIndex.fixedField ⟨.B r q, hv⟩) = q.p ^ q.exponent :=
    card_fixedField_of (LieTypeIndex.characteristic_B r q) (LieTypeIndex.fieldExponent_B r q)
  rcases (show r = 2 ∨ 3 ≤ r by omega) with rfl | hr3
  · refine .inl (lieModel_of_statedClassicalModel ⟨⟨q.prime_p, q.exponent_pos, le_rfl, ?_⟩,
      _, inferInstance, CFSG.QuasithinUnique.SQTK.finite_validIndex_fixedField _, hK,
      ⟨e.trans (CFSG.QuasithinUnique.SQTK.typeB2GroupEquivStatedProj q hv)⟩⟩)
    intro h
    simp only [Prod.mk.injEq] at h
    exact hr.2 ⟨rfl, by omega⟩
  · by_cases hp : q.p = 2
    · refine .inl (lieModel_of_statedClassicalModel ⟨⟨q.prime_p, q.exponent_pos, by omega, ?_⟩,
        _, inferInstance, CFSG.QuasithinUnique.SQTK.finite_validIndex_fixedField _, hK,
        ⟨e.trans (CFSG.RankThree.PartTwo.Census.Carrier.SpinB.typeBGroupEquivStatedProj r q hv hp
          hr3)⟩⟩)
      intro h
      simp only [Prod.mk.injEq] at h
      omega
    · exact .inr (lieModel_of_statedClassicalModel ⟨⟨q.prime_p, q.exponent_pos, hr3, hp⟩,
        _, inferInstance, CFSG.QuasithinUnique.SQTK.finite_validIndex_fixedField _, hK,
        ⟨e.trans (CFSG.RankThree.PartTwo.Census.Carrier.SpinB.typeBGroupEquivStatedProj_odd r q
          hv hp hr3)⟩⟩)

theorem lieModel_C {G : Type} [Group G] (r : ℕ) (q : PrimePower)
    (hv : (LieTypeIndex.C r q).Valid) (e : G ≃* ValidLieTypeIndex.Group ⟨.C r q, hv⟩) :
    LieModel G .PSp r q.p q.exponent := by
  have hr := (LieTypeIndex.inStandardRange_iff _).mp ((LieTypeIndex.valid_iff _).mp hv).1
  refine lieModel_of_statedClassicalModel ⟨⟨q.prime_p, q.exponent_pos, by omega, ?_⟩,
    _, inferInstance, CFSG.QuasithinUnique.SQTK.finite_validIndex_fixedField _,
    card_fixedField_of (LieTypeIndex.characteristic_C r q) (LieTypeIndex.fieldExponent_C r q),
    ⟨e.trans (CFSG.QuasithinUnique.SQTK.typeCGroupEquivStatedProj r q hv)⟩⟩
  intro h
  simp only [Prod.mk.injEq] at h
  omega

theorem lieModel_D {G : Type} [Group G] (r : ℕ) (q : PrimePower)
    (hv : (LieTypeIndex.D r q).Valid) (e : G ≃* ValidLieTypeIndex.Group ⟨.D r q, hv⟩) :
    LieModel G .POmegaPlus r q.p q.exponent := by
  have hr := (LieTypeIndex.inStandardRange_iff _).mp ((LieTypeIndex.valid_iff _).mp hv).1
  exact lieModel_of_statedClassicalModel ⟨⟨q.prime_p, q.exponent_pos, hr⟩,
    _, inferInstance, CFSG.QuasithinUnique.SQTK.finite_validIndex_fixedField _,
    card_fixedField_of (LieTypeIndex.characteristic_D r q) (LieTypeIndex.fieldExponent_D r q),
    ⟨e.trans (CFSG.RankThree.PartTwo.Census.Carrier.SpinD.typeDGroupEquivStatedProj_of_valid r q
      hv)⟩⟩

theorem lieModel_twistedD {G : Type} [Group G] (r : ℕ) (q : PrimePower)
    (hv : (LieTypeIndex.twistedD r q).Valid)
    (e : G ≃* ValidLieTypeIndex.Group ⟨.twistedD r q, hv⟩) :
    LieModel G .POmegaMinus r q.p q.exponent := by
  have hr := (LieTypeIndex.inStandardRange_iff _).mp ((LieTypeIndex.valid_iff _).mp hv).1
  obtain ⟨b, c, hirr, ⟨e'⟩⟩ :=
    CFSG.RankThree.PartTwo.Census.Carrier.SpinD.exists_typeTwistedDGroupEquivStatedProj_of_valid
      r q hv
  exact lieModel_of_statedClassicalModel ⟨⟨q.prime_p, q.exponent_pos, hr⟩,
    _, inferInstance, CFSG.QuasithinUnique.SQTK.finite_validIndex_fixedField _,
    card_fixedField_of (LieTypeIndex.characteristic_twistedD r q)
      (LieTypeIndex.fieldExponent_twistedD r q), b, c, hirr, ⟨e.trans e'⟩⟩

theorem oddLieType_or_evenLieType_of_valid {G : Type} [Group G] (d : ValidLieTypeIndex)
    (he : Nonempty (G ≃* d.Group)) : OddLieType G ∨ EvenLieType G := by
  obtain ⟨d, hv⟩ := d
  obtain ⟨e⟩ := he
  have hr := (LieTypeIndex.inStandardRange_iff _).mp ((LieTypeIndex.valid_iff _).mp hv).1
  cases d with
  | A r q => exact oddLieType_or_evenLieType_of_lieModel (lieModel_A r q hv e)
  | twistedA r q => exact oddLieType_or_evenLieType_of_lieModel (lieModel_twistedA r q hv e)
  | B r q =>
    exact (lieModel_B r q hv e).elim oddLieType_or_evenLieType_of_lieModel
      oddLieType_or_evenLieType_of_lieModel
  | C r q => exact oddLieType_or_evenLieType_of_lieModel (lieModel_C r q hv e)
  | D r q => exact oddLieType_or_evenLieType_of_lieModel (lieModel_D r q hv e)
  | twistedD r q => exact oddLieType_or_evenLieType_of_lieModel (lieModel_twistedD r q hv e)
  | E6 q =>
    exact oddLieType_or_evenLieType_of_lieModel (lieModel_of_namesTag (t := .E6) (p := q.p)
      (f := q.exponent) ⟨q.prime_p, q.exponent_pos, rfl⟩ ⟨_, hv⟩ ⟨rfl, rfl⟩ e)
  | E7 q =>
    exact oddLieType_or_evenLieType_of_lieModel (lieModel_of_namesTag (t := .E7) (p := q.p)
      (f := q.exponent) ⟨q.prime_p, q.exponent_pos, rfl⟩ ⟨_, hv⟩ ⟨rfl, rfl⟩ e)
  | E8 q =>
    exact oddLieType_or_evenLieType_of_lieModel (lieModel_of_namesTag (t := .E8) (p := q.p)
      (f := q.exponent) ⟨q.prime_p, q.exponent_pos, rfl⟩ ⟨_, hv⟩ ⟨rfl, rfl⟩ e)
  | F4 q =>
    exact oddLieType_or_evenLieType_of_lieModel (lieModel_of_namesTag (t := .F4) (p := q.p)
      (f := q.exponent) ⟨q.prime_p, q.exponent_pos, rfl⟩ ⟨_, hv⟩ ⟨rfl, rfl⟩ e)
  | G2 q =>
    have hq : q.card = q.p ^ q.exponent := PrimePower.card_def q
    exact oddLieType_or_evenLieType_of_lieModel (lieModel_of_namesTag (t := .G2) (p := q.p)
      (f := q.exponent) ⟨q.prime_p, q.exponent_pos, rfl, hq ▸ hr⟩ ⟨_, hv⟩ ⟨rfl, rfl⟩ e)
  | twistedE6 q =>
    exact oddLieType_or_evenLieType_of_lieModel (lieModel_of_namesTag (t := .twistedE6)
      (p := q.p) (f := q.exponent) ⟨q.prime_p, q.exponent_pos, rfl⟩ ⟨_, hv⟩ ⟨rfl, rfl⟩ e)
  | trialityD4 q =>
    exact oddLieType_or_evenLieType_of_lieModel (lieModel_of_namesTag (t := .trialityD4)
      (p := q.p) (f := q.exponent) ⟨q.prime_p, q.exponent_pos, rfl⟩ ⟨_, hv⟩ ⟨rfl, rfl⟩ e)
  | suzuki m =>
    exact oddLieType_or_evenLieType_of_lieModel (lieModel_of_namesTag (t := .twistedB2) (p := 2)
      (f := 2 * m + 1) ⟨Nat.prime_two, by omega, rfl, rfl, odd_two_mul_add_one m, by omega⟩
      ⟨_, hv⟩ ⟨rfl, rfl⟩ e)
  | reeG2 m =>
    exact oddLieType_or_evenLieType_of_lieModel (lieModel_of_namesTag (t := .twistedG2) (p := 3)
      (f := 2 * m + 1) ⟨Nat.prime_three, by omega, rfl, rfl, odd_two_mul_add_one m, by omega⟩
      ⟨_, hv⟩ ⟨rfl, rfl⟩ e)
  | reeF4 m =>
    exact oddLieType_or_evenLieType_of_lieModel (lieModel_of_namesTag (t := .twistedF4) (p := 2)
      (f := 2 * m + 1) ⟨Nat.prime_two, by omega, rfl, rfl, odd_two_mul_add_one m, by omega⟩
      ⟨_, hv⟩ ⟨rfl, rfl⟩ e)
  | tits =>
    exact oddLieType_or_evenLieType_of_lieModel (lieModel_of_namesTag (t := .Tits) (p := 2)
      (f := 1) ⟨Nat.prime_two, le_rfl, rfl, rfl, rfl⟩ ⟨_, hv⟩ ⟨rfl, rfl⟩ e)

end CFSG.Models
