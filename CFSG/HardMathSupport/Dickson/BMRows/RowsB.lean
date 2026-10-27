module

public import CFSG.HardMathSupport.Dickson.BMRows.Rows

public section

namespace CFSG.HardMathSupport.Dickson.BMRows

open CFSG.Open CFSG.Yardstones.Md0ec50421ce4 CFSG.LocalAnalysis.GLTheoremA
open CFSG.Blueprint.NativeSporadic (Carrier)
open CFSG.HardMathSupport.Timmesfeld.Proving (sporadicOuterLeTwo_holds)

theorem model_B
    :
    Finite (Carrier .B) ∧ IsSimpleGroup (Carrier .B) ∧
      Nonempty (Carrier .B ≃* (TauCeti.CFSGIndex.sporadic .B).Group) ∧
      ∃ a c : Carrier .B, a * c ≠ c * a := by
  haveI : Finite (Carrier .B) := CFSG.Sporadic.finite_carrier_of_ne_M .B (by decide)
  haveI : IsSimpleGroup (Carrier .B) := CFSG.Sporadic.B.fam_b_simplicity
  refine ⟨inferInstance, inferInstance, CFSG.Sporadic.Bridge.B.nonempty_mulEquiv,
    CFSG.LocalAnalysis.GLTheoremA.S8.HNRows.exists_noncomm_of_simple fun hp => ?_⟩
  have h91 : 7 * 13 ∣ Nat.card (Carrier .B) :=
    (by norm_num : 7 * 13 ∣ 7 * 13 * 17 * 19 * 31 * 47).trans
      CFSG.Sporadic.Bridge.B.six_primes_dvd
  rcases hp.eq_one_or_self_of_dvd _ h91 with h | h
  · norm_num at h
  · rw [← h] at hp
    norm_num at hp

section Rows


theorem row_B_of_census {p : ℕ} {P : TauCeti.CFSGIndex → Prop} (hC : PCompCensus p (Carrier .B) P)
    (hT : ∀ (T : Type) [Group T], catalogIs T P → I1416Rows.TypeOK p T) :
    I1416Rows.I1416SporRow .B p := by
  obtain ⟨_, _, ⟨b⟩, hnc⟩ := model_B
  exact row_of_census sporadicOuterLeTwo_holds b hnc hC hT

theorem qrow_B_of_census {p : ℕ} {P : TauCeti.CFSGIndex → Prop} (hC : PCompCensus p (Carrier .B) P)
    (hT : ∀ (T : Type) [Group T], catalogIs T P → I1416QRows.QTypeOK p T) :
    I1416QRows.I1416QRow .B p := by
  obtain ⟨_, _, ⟨b⟩, hnc⟩ := model_B
  exact qrow_of_census sporadicOuterLeTwo_holds b hnc hC hT

theorem arow_B_of_census {p : ℕ} {P : TauCeti.CFSGIndex → Prop} (hC : PCompCensus p (Carrier .B) P)
    (hT : ∀ (T : Type) [Group T], catalogIs T P → I1415Rows.ATypeOK p T) :
    I1415Rows.I1415Row .B p := by
  obtain ⟨_, _, ⟨b⟩, hnc⟩ := model_B
  exact arow_of_census sporadicOuterLeTwo_holds b hnc hC hT

theorem srow_B_of_census {p : ℕ} {P : TauCeti.CFSGIndex → Prop} (hC : PCompCensus p (Carrier .B) P)
    (hT : ∀ (T : Type) [Group T], catalogIs T P → SporAltRows.STypeOK p T) :
    SporAltRows.SRow .B p := by
  obtain ⟨_, _, ⟨b⟩, hnc⟩ := model_B
  exact srow_of_census sporadicOuterLeTwo_holds b hnc hC hT

theorem kdSporRow_B_of_census {p : ℕ} (hp : p.Prime) (hp2 : p ≠ 2) {P : TauCeti.CFSGIndex → Prop}
    (hC : PCompCensus p (Carrier .B) P)
    (hT : ∀ (T : Type) [Group T], catalogIs T P → kLevel p T ≤ 2) : KDSporRow .B p := by
  obtain ⟨_, _, ⟨b⟩, hnc⟩ := model_B
  exact kdSporRow_of_census sporadicOuterLeTwo_holds b hnc hp hp2 hC hT

theorem kdl227Row_B_of_census {P : TauCeti.CFSGIndex → Prop} (hC : PCompCensus 3 (Carrier .B) P)
    (hT : ∀ (T : Type) [Group T], catalogIs T P → ¬ catalogIs T (onLie (isL2 27))) :
    KDL227Rows.KDL227SporRow .B := by
  obtain ⟨_, _, ⟨b⟩, hnc⟩ := model_B
  exact kdl227Row_of_census sporadicOuterLeTwo_holds b hnc hC hT

theorem row_B_of_cardCensus {p N : ℕ} (hC : PCardCensus p (Carrier .B) N)
    (hT : ∀ (T : Type) [Group T], Nat.card T ∣ N → I1416Rows.TypeOK p T) :
    I1416Rows.I1416SporRow .B p := by
  obtain ⟨_, _, ⟨b⟩, hnc⟩ := model_B
  exact row_of_cardCensus sporadicOuterLeTwo_holds b hnc hC hT

theorem qrow_B_of_cardCensus {p N : ℕ} (hC : PCardCensus p (Carrier .B) N)
    (hT : ∀ (T : Type) [Group T], Nat.card T ∣ N → I1416QRows.QTypeOK p T) :
    I1416QRows.I1416QRow .B p := by
  obtain ⟨_, _, ⟨b⟩, hnc⟩ := model_B
  exact qrow_of_cardCensus sporadicOuterLeTwo_holds b hnc hC hT

theorem arow_B_of_cardCensus {p N : ℕ} (hC : PCardCensus p (Carrier .B) N)
    (hT : ∀ (T : Type) [Group T], Nat.card T ∣ N → I1415Rows.ATypeOK p T) :
    I1415Rows.I1415Row .B p := by
  obtain ⟨_, _, ⟨b⟩, hnc⟩ := model_B
  exact arow_of_cardCensus sporadicOuterLeTwo_holds b hnc hC hT

end Rows

end CFSG.HardMathSupport.Dickson.BMRows
