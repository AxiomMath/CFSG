module

public import CFSG.HardMathSupport.Timmesfeld.Tables.T1b.Bridge
public import CFSG.Adapters.TauCetiLieModels
public import CFSG.HardMathSupport.Solomon.LocalBalance.Lemma53
public import CFSG.HardMathSupport.Solomon.LocalBalance.Lemma54
public import CFSG.Quasithin.Vol2.Ch10SecKGA318

public section

namespace CFSG.HardMathSupport.Dickson.Sec6

open CFSG.Assembly.LowTwoRank CFSG.Blueprint TauCeti

theorem blueprintLieModel_D {G : Type} [Group G] (r : ℕ) (q : PrimePower)
    (hv : (LieTypeIndex.D r q).Valid) (e : G ≃* ValidLieTypeIndex.Group ⟨.D r q, hv⟩) :
    Blueprint.LieModel G .POmegaPlus r q.p q.exponent := by
  obtain ⟨hadm, hcl | ⟨h0, -⟩⟩ := CFSG.Models.lieModel_D r q hv e
  · exact Or.inl ⟨by decide, hcl⟩
  · have hr : 4 ≤ r := hadm.2.2
    omega

theorem blueprintLieModel_twistedD {G : Type} [Group G] (r : ℕ) (q : PrimePower)
    (hv : (LieTypeIndex.twistedD r q).Valid)
    (e : G ≃* ValidLieTypeIndex.Group ⟨.twistedD r q, hv⟩) :
    Blueprint.LieModel G .POmegaMinus r q.p q.exponent := by
  obtain ⟨hadm, hcl | ⟨h0, -⟩⟩ := CFSG.Models.lieModel_twistedD r q hv e
  · exact Or.inl ⟨by decide, hcl⟩
  · have hr : 4 ≤ r := hadm.2.2
    omega


theorem blueprintLieModel_A {G : Type} [Group G] (r : ℕ) (q : PrimePower)
    (hv : (LieTypeIndex.A r q).Valid) (e : G ≃* ValidLieTypeIndex.Group ⟨.A r q, hv⟩) :
    Blueprint.LieModel G .PSL (r + 1) q.p q.exponent :=
  CFSG.HardMathSupport.Timmesfeld.Tables.T1b.blueprintLieModel_of_models
    (CFSG.Models.lieModel_A r q hv e)

theorem blueprintLieModel_twistedA {G : Type} [Group G] (r : ℕ) (q : PrimePower)
    (hv : (LieTypeIndex.twistedA r q).Valid)
    (e : G ≃* ValidLieTypeIndex.Group ⟨.twistedA r q, hv⟩) :
    Blueprint.LieModel G .PSU (r + 1) q.p q.exponent := by
  have h := CFSG.HardMathSupport.Timmesfeld.Tables.T1b.blueprintLieModel_of_models
    (CFSG.Models.lieModel_twistedA r q hv e)
  have hc : ValidLieTypeIndex.characteristic ⟨.twistedA r q, hv⟩ = q.p :=
    LieTypeIndex.characteristic_twistedA r q
  have hf : ValidLieTypeIndex.fieldExponent ⟨.twistedA r q, hv⟩ = q.exponent :=
    LieTypeIndex.fieldExponent_twistedA r q
  rwa [hc, hf] at h

theorem blueprintLieModel_B {G : Type} [Group G] (r : ℕ) (q : PrimePower)
    (hv : (LieTypeIndex.B r q).Valid) (hp : q.p = 2)
    (e : G ≃* ValidLieTypeIndex.Group ⟨.B r q, hv⟩) :
    Blueprint.LieModel G .PSp r q.p q.exponent := by
  rcases CFSG.Models.lieModel_B r q hv e with h | h
  · exact CFSG.HardMathSupport.Timmesfeld.Tables.T1b.blueprintLieModel_of_models h
  · exfalso
    obtain ⟨⟨-, -, -, hp2⟩, -⟩ := h
    exact hp2 hp

theorem blueprintLieModel_E6 {G : Type} [Group G] (q : PrimePower)
    (hv : (LieTypeIndex.E6 q).Valid) (e : G ≃* ValidLieTypeIndex.Group ⟨.E6 q, hv⟩) :
    Blueprint.LieModel G .E6 0 q.p q.exponent :=
  CFSG.HardMathSupport.Timmesfeld.Tables.T1b.blueprintLieModel_of_models
    (CFSG.Models.lieModel_of_namesTag (t := .E6) (p := q.p) (f := q.exponent)
      ⟨q.prime_p, q.exponent_pos, rfl⟩ ⟨_, hv⟩ ⟨rfl, rfl⟩ e)

theorem blueprintLieModel_E7 {G : Type} [Group G] (q : PrimePower)
    (hv : (LieTypeIndex.E7 q).Valid) (e : G ≃* ValidLieTypeIndex.Group ⟨.E7 q, hv⟩) :
    Blueprint.LieModel G .E7 0 q.p q.exponent :=
  CFSG.HardMathSupport.Timmesfeld.Tables.T1b.blueprintLieModel_of_models
    (CFSG.Models.lieModel_of_namesTag (t := .E7) (p := q.p) (f := q.exponent)
      ⟨q.prime_p, q.exponent_pos, rfl⟩ ⟨_, hv⟩ ⟨rfl, rfl⟩ e)

theorem blueprintLieModel_E8 {G : Type} [Group G] (q : PrimePower)
    (hv : (LieTypeIndex.E8 q).Valid) (e : G ≃* ValidLieTypeIndex.Group ⟨.E8 q, hv⟩) :
    Blueprint.LieModel G .E8 0 q.p q.exponent :=
  CFSG.HardMathSupport.Timmesfeld.Tables.T1b.blueprintLieModel_of_models
    (CFSG.Models.lieModel_of_namesTag (t := .E8) (p := q.p) (f := q.exponent)
      ⟨q.prime_p, q.exponent_pos, rfl⟩ ⟨_, hv⟩ ⟨rfl, rfl⟩ e)

theorem blueprintLieModel_F4 {G : Type} [Group G] (q : PrimePower)
    (hv : (LieTypeIndex.F4 q).Valid) (e : G ≃* ValidLieTypeIndex.Group ⟨.F4 q, hv⟩) :
    Blueprint.LieModel G .F4 0 q.p q.exponent :=
  CFSG.HardMathSupport.Timmesfeld.Tables.T1b.blueprintLieModel_of_models
    (CFSG.Models.lieModel_of_namesTag (t := .F4) (p := q.p) (f := q.exponent)
      ⟨q.prime_p, q.exponent_pos, rfl⟩ ⟨_, hv⟩ ⟨rfl, rfl⟩ e)

theorem blueprintLieModel_G2 {G : Type} [Group G] (q : PrimePower)
    (hv : (LieTypeIndex.G2 q).Valid) (e : G ≃* ValidLieTypeIndex.Group ⟨.G2 q, hv⟩) :
    Blueprint.LieModel G .G2 0 q.p q.exponent := by
  have hr := (LieTypeIndex.inStandardRange_iff _).mp ((LieTypeIndex.valid_iff _).mp hv).1
  have hq : q.card = q.p ^ q.exponent := PrimePower.card_def q
  exact CFSG.HardMathSupport.Timmesfeld.Tables.T1b.blueprintLieModel_of_models
    (CFSG.Models.lieModel_of_namesTag (t := .G2) (p := q.p) (f := q.exponent)
      ⟨q.prime_p, q.exponent_pos, rfl, hq ▸ hr⟩ ⟨_, hv⟩ ⟨rfl, rfl⟩ e)

theorem blueprintLieModel_twistedE6 {G : Type} [Group G] (q : PrimePower)
    (hv : (LieTypeIndex.twistedE6 q).Valid)
    (e : G ≃* ValidLieTypeIndex.Group ⟨.twistedE6 q, hv⟩) :
    Blueprint.LieModel G .twistedE6 0 q.p q.exponent :=
  CFSG.HardMathSupport.Timmesfeld.Tables.T1b.blueprintLieModel_of_models
    (CFSG.Models.lieModel_of_namesTag (t := .twistedE6) (p := q.p) (f := q.exponent)
      ⟨q.prime_p, q.exponent_pos, rfl⟩ ⟨_, hv⟩ ⟨rfl, rfl⟩ e)

theorem blueprintLieModel_trialityD4 {G : Type} [Group G] (q : PrimePower)
    (hv : (LieTypeIndex.trialityD4 q).Valid)
    (e : G ≃* ValidLieTypeIndex.Group ⟨.trialityD4 q, hv⟩) :
    Blueprint.LieModel G .trialityD4 0 q.p q.exponent :=
  CFSG.HardMathSupport.Timmesfeld.Tables.T1b.blueprintLieModel_of_models
    (CFSG.Models.lieModel_of_namesTag (t := .trialityD4) (p := q.p) (f := q.exponent)
      ⟨q.prime_p, q.exponent_pos, rfl⟩ ⟨_, hv⟩ ⟨rfl, rfl⟩ e)

theorem blueprintLieModel_suzuki {G : Type} [Group G] (m : ℕ)
    (hv : (LieTypeIndex.suzuki m).Valid) (e : G ≃* ValidLieTypeIndex.Group ⟨.suzuki m, hv⟩) :
    Blueprint.LieModel G .twistedB2 0 2 (2 * m + 1) :=
  have hm : 1 ≤ m := by
    have h := ((LieTypeIndex.valid_iff _).1 hv).1
    simpa only [LieTypeIndex.inStandardRange_iff] using h
  CFSG.HardMathSupport.Timmesfeld.Tables.T1b.blueprintLieModel_of_models
    (CFSG.Models.lieModel_of_namesTag (t := .twistedB2) (p := 2) (f := 2 * m + 1)
      ⟨Nat.prime_two, by omega, rfl, rfl, odd_two_mul_add_one m, by omega⟩ ⟨_, hv⟩ ⟨rfl, rfl⟩ e)

theorem blueprintLieModel_reeF4 {G : Type} [Group G] (m : ℕ)
    (hv : (LieTypeIndex.reeF4 m).Valid) (e : G ≃* ValidLieTypeIndex.Group ⟨.reeF4 m, hv⟩) :
    Blueprint.LieModel G .twistedF4 0 2 (2 * m + 1) :=
  have hm : 1 ≤ m := by
    have h := ((LieTypeIndex.valid_iff _).1 hv).1
    simpa only [LieTypeIndex.inStandardRange_iff] using h
  CFSG.HardMathSupport.Timmesfeld.Tables.T1b.blueprintLieModel_of_models
    (CFSG.Models.lieModel_of_namesTag (t := .twistedF4) (p := 2) (f := 2 * m + 1)
      ⟨Nat.prime_two, by omega, rfl, rfl, odd_two_mul_add_one m, by omega⟩ ⟨_, hv⟩ ⟨rfl, rfl⟩ e)

theorem blueprintLieModel_tits {G : Type} [Group G] (hv : (LieTypeIndex.tits).Valid)
    (e : G ≃* ValidLieTypeIndex.Group ⟨.tits, hv⟩) : Blueprint.LieModel G .Tits 0 2 1 :=
  CFSG.HardMathSupport.Timmesfeld.Tables.T1b.blueprintLieModel_of_models
    (CFSG.Models.lieModel_of_namesTag (t := .Tits) (p := 2) (f := 1)
      ⟨Nat.prime_two, le_rfl, rfl, rfl, rfl⟩ ⟨_, hv⟩ ⟨rfl, rfl⟩ e)

end CFSG.HardMathSupport.Dickson.Sec6
