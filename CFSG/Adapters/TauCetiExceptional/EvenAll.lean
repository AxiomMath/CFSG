module

public import CFSG.Adapters.TauCetiExceptional.EvenBridgeG2
public import CFSG.Adapters.TauCetiExceptional.EvenBridgeF4
public import CFSG.Adapters.TauCetiExceptional.EvenBridgeE8
public import CFSG.Adapters.TauCetiExceptional.EvenBridgeE6E7
public import CFSG.Adapters.TauCetiExceptional.EvenD4
public import CFSG.Adapters.TauCetiExceptional.EvenBridgeTwistedE6
public import CFSG.Adapters.TauCetiExceptional.BridgeAll

public section

namespace CFSG.TauCetiBridge.Even

open CFSG.Blueprint CFSG.Blueprint.Chevalley TauCeti

theorem chevalleyBridgesEven
    : ChevalleyBridgesEven where
  g2 := untwistedBridgeEven_G2
  f4 := untwistedBridgeEven_F4
  e6 := untwistedBridgeEven_E6
  e7 := untwistedBridgeEven_E7
  e8 := untwistedBridgeEven_E8
  twistedE6 := twistedBridgeEven_twistedE6
  trialityD4 := twistedBridgeEven_trialityD4

@[expose] def UntwistedBridgeAll (τ : Tag) (c : PrimePower → LieTypeIndex) : Prop :=
  ∀ (q : PrimePower) (hv : (c q).Valid) (K : Type) [Field K] [Finite K], Nat.card K = q.card →
    Nonempty (AdjointQuotient τ K ≃* ValidLieTypeIndex.Group ⟨c q, hv⟩)

@[expose] def TwistedBridgeAll (t : TwistTag) (c : PrimePower → LieTypeIndex) : Prop :=
  ∀ (q : PrimePower) (hv : (c q).Valid) (K : Type) [Field K] [Finite K],
    Nat.card K = q.card ^ t.order → ∀ σ : K →+* K, (∀ x, σ x = x ^ q.card) →
      Nonempty (CFSG.Blueprint.DerivedCentralQuotient (twistedFixedGroup t K σ) ≃*
        ValidLieTypeIndex.Group ⟨c q, hv⟩)

theorem untwistedBridgeAll_of {τ : Tag} {c : PrimePower → LieTypeIndex}
    (hodd : UntwistedBridge τ c) (heven : UntwistedBridgeEven τ c) : UntwistedBridgeAll τ c :=
  fun q hv K _ _ hK => by
    by_cases hq : q.p = 2
    · exact heven q hv hq K hK
    · exact hodd q hv hq K hK

theorem twistedBridgeAll_of {t : TwistTag} {c : PrimePower → LieTypeIndex}
    (hodd : TwistedBridge t c) (heven : TwistedBridgeEven t c) : TwistedBridgeAll t c :=
  fun q hv K _ _ hK σ hσ => by
    by_cases hq : q.p = 2
    · exact heven q hv hq K hK σ hσ
    · exact hodd q hv hq K hK σ hσ

structure ChevalleyBridgesAll : Prop where
  g2 : UntwistedBridgeAll .G2 LieTypeIndex.G2
  f4 : UntwistedBridgeAll .F4 LieTypeIndex.F4
  e6 : UntwistedBridgeAll .E6 LieTypeIndex.E6
  e7 : UntwistedBridgeAll .E7 LieTypeIndex.E7
  e8 : UntwistedBridgeAll .E8 LieTypeIndex.E8
  twistedE6 : TwistedBridgeAll .E6 LieTypeIndex.twistedE6
  trialityD4 : TwistedBridgeAll .D4 LieTypeIndex.trialityD4

theorem chevalleyBridgesAll
    : ChevalleyBridgesAll where
  g2 := untwistedBridgeAll_of chevalleyBridges.g2 chevalleyBridgesEven.g2
  f4 := untwistedBridgeAll_of chevalleyBridges.f4 chevalleyBridgesEven.f4
  e6 := untwistedBridgeAll_of chevalleyBridges.e6 chevalleyBridgesEven.e6
  e7 := untwistedBridgeAll_of chevalleyBridges.e7 chevalleyBridgesEven.e7
  e8 := untwistedBridgeAll_of chevalleyBridges.e8 chevalleyBridgesEven.e8
  twistedE6 := twistedBridgeAll_of chevalleyBridges.twistedE6 chevalleyBridgesEven.twistedE6
  trialityD4 := twistedBridgeAll_of chevalleyBridges.trialityD4 chevalleyBridgesEven.trialityD4

end CFSG.TauCetiBridge.Even
