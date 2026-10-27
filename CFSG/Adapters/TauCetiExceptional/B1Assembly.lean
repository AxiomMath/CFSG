module

public import CFSG.Adapters.TauCetiExceptional.B1Exceptional
public import CFSG.LocalAnalysis.QuasithinUnique.B1.Classical
public import CFSG.LocalAnalysis.QuasithinUnique.B1.Suzuki

public section

namespace CFSG.TauCetiBridge

open TauCeti CFSG.QuasithinUnique CFSG.QuasithinUnique.B1

structure B1Remaining : Prop where
  orthogonalOdd : ∀ (r : ℕ) (q : PrimePower) (hv : (LieTypeIndex.B r q).Valid), 3 ≤ r →
    CatalogBridgeFor (.lie ⟨.B r q, hv⟩)
  orthogonalPlus : ∀ (r : ℕ) (q : PrimePower) (hv : (LieTypeIndex.D r q).Valid),
    CatalogBridgeFor (.lie ⟨.D r q, hv⟩)
  orthogonalMinus : ∀ (r : ℕ) (q : PrimePower) (hv : (LieTypeIndex.twistedD r q).Valid),
    CatalogBridgeFor (.lie ⟨.twistedD r q, hv⟩)
  g2Even : ∀ (q : PrimePower) (hv : (LieTypeIndex.G2 q).Valid), q.p = 2 →
    CatalogBridgeFor (.lie ⟨.G2 q, hv⟩)
  f4Even : ∀ (q : PrimePower) (hv : (LieTypeIndex.F4 q).Valid), q.p = 2 →
    CatalogBridgeFor (.lie ⟨.F4 q, hv⟩)
  e6Even : ∀ (q : PrimePower) (hv : (LieTypeIndex.E6 q).Valid), q.p = 2 →
    CatalogBridgeFor (.lie ⟨.E6 q, hv⟩)
  e7Even : ∀ (q : PrimePower) (hv : (LieTypeIndex.E7 q).Valid), q.p = 2 →
    CatalogBridgeFor (.lie ⟨.E7 q, hv⟩)
  e8Even : ∀ (q : PrimePower) (hv : (LieTypeIndex.E8 q).Valid), q.p = 2 →
    CatalogBridgeFor (.lie ⟨.E8 q, hv⟩)
  twistedE6Even : ∀ (q : PrimePower) (hv : (LieTypeIndex.twistedE6 q).Valid), q.p = 2 →
    CatalogBridgeFor (.lie ⟨.twistedE6 q, hv⟩)
  trialityD4Even : ∀ (q : PrimePower) (hv : (LieTypeIndex.trialityD4 q).Valid), q.p = 2 →
    CatalogBridgeFor (.lie ⟨.trialityD4 q, hv⟩)
  reeG2 : ∀ (m : ℕ) (hv : (LieTypeIndex.reeG2 m).Valid), CatalogBridgeFor (.lie ⟨.reeG2 m, hv⟩)
  reeF4 : ∀ (m : ℕ) (hv : (LieTypeIndex.reeF4 m).Valid), CatalogBridgeFor (.lie ⟨.reeF4 m, hv⟩)
  tits : ∀ hv : LieTypeIndex.tits.Valid, CatalogBridgeFor (.lie ⟨.tits, hv⟩)
  sporadic : ∀ s : SporadicName, CatalogBridgeFor (.sporadic s)

theorem catalogBridgeFor_of_remaining
    (h : B1Remaining) (i : CFSGIndex) : CatalogBridgeFor i := by
  rcases i with ⟨p, hp⟩ | ⟨n, hn⟩ | ⟨d, hv⟩ | s
  · exact catalogBridgeFor_cyclic p hp
  · exact catalogBridgeFor_alternating n hn
  · cases d with
    | A r q => exact catalogBridgeFor_A r q hv
    | twistedA r q => exact catalogBridgeFor_twistedA r q hv
    | B r q =>
      by_cases hr : r = 2
      · subst hr
        exact catalogBridgeFor_B2 q hv
      · have h2 := ((LieTypeIndex.valid_iff _).1 hv).1
        rw [LieTypeIndex.inStandardRange_iff] at h2
        exact h.orthogonalOdd r q hv (by omega)
    | C r q => exact catalogBridgeFor_C r q hv
    | D r q => exact h.orthogonalPlus r q hv
    | twistedD r q => exact h.orthogonalMinus r q hv
    | E6 q =>
      by_cases hq : q.p = 2
      · exact h.e6Even q hv hq
      · exact catalogBridgeFor_E6_of_odd q hv hq
    | E7 q =>
      by_cases hq : q.p = 2
      · exact h.e7Even q hv hq
      · exact catalogBridgeFor_E7_of_odd q hv hq
    | E8 q =>
      by_cases hq : q.p = 2
      · exact h.e8Even q hv hq
      · exact catalogBridgeFor_E8_of_odd q hv hq
    | F4 q =>
      by_cases hq : q.p = 2
      · exact h.f4Even q hv hq
      · exact catalogBridgeFor_F4_of_odd q hv hq
    | G2 q =>
      by_cases hq : q.p = 2
      · exact h.g2Even q hv hq
      · exact catalogBridgeFor_G2_of_odd q hv hq
    | twistedE6 q =>
      by_cases hq : q.p = 2
      · exact h.twistedE6Even q hv hq
      · exact catalogBridgeFor_twistedE6_of_odd q hv hq
    | trialityD4 q =>
      by_cases hq : q.p = 2
      · exact h.trialityD4Even q hv hq
      · exact catalogBridgeFor_trialityD4_of_odd q hv hq
    | suzuki m => exact catalogBridgeFor_suzuki m hv
    | reeG2 m => exact h.reeG2 m hv
    | reeF4 m => exact h.reeF4 m hv
    | tits => exact h.tits hv
  · exact h.sporadic s

theorem tcKGroupBridge_of_remaining
    (h : B1Remaining) : TCKGroupBridge :=
  tcKGroupBridge_of_bridges (catalogBridgeFor_of_remaining h)

end CFSG.TauCetiBridge
