module

public import CFSG.Adapters.TauCetiExceptional.EvenAll
public import CFSG.Adapters.TauCetiExceptional.B1Assembly

public section

namespace CFSG.TauCetiBridge.Even

open TauCeti CFSG.QuasithinUnique CFSG.QuasithinUnique.B1 CFSG.Blueprint CFSG.Blueprint.Chevalley
  CFSG.Assembly.LowTwoRank

theorem untwistedModel_of_bridgeEven {τ : Tag} {c : PrimePower → LieTypeIndex}
    (hB : UntwistedBridgeEven τ c) (q : PrimePower) (hv : (c q).Valid) (hq : q.p = 2)
    {S : Type} [Group S] (e : S ≃* ValidLieTypeIndex.Group ⟨c q, hv⟩) :
    UntwistedChevalleyModel S τ (q.p ^ q.exponent) := by
  have hK := card_fieldOf q Nat.one_pos
  rw [pow_one] at hK
  obtain ⟨φ⟩ := hB q hv hq (fieldOf q 1) hK
  exact ⟨fieldOf q 1, inferInstance, inferInstance, hK.trans q.card_def, ⟨e.trans φ.symm⟩⟩

theorem twistedModel_of_bridgeEven {t : TwistTag} {c : PrimePower → LieTypeIndex}
    (hB : TwistedBridgeEven t c) (q : PrimePower) (hv : (c q).Valid) (hq : q.p = 2)
    (hm : 0 < t.order) {S : Type} [Group S] (e : S ≃* ValidLieTypeIndex.Group ⟨c q, hv⟩) :
    TwistedChevalleyModel S t (q.p ^ q.exponent) := by
  obtain ⟨φ⟩ := hB q hv hq (fieldOf q t.order) (card_fieldOf q hm) (frobOf q t.order)
    (frobOf_apply q t.order)
  refine ⟨fieldOf q t.order, inferInstance, inferInstance, ?_, frobOf q t.order, ?_,
    ⟨e.trans φ.symm⟩⟩
  · rw [card_fieldOf q hm, q.card_def]
  · intro x
    rw [frobOf_apply, q.card_def]

theorem catalogBridgeFor_G2_of_even
    (q : PrimePower) (hv : (LieTypeIndex.G2 q).Valid)
    (hq : q.p = 2) : CatalogBridgeFor (.lie ⟨.G2 q, hv⟩) := by
  intro S _ _ _ ⟨e⟩
  refine catalog_of_chevalleyExceptionalModel .G2 (by decide) q.p q.exponent
    ⟨⟨q.prime_p, q.exponent_pos, rfl, ?_⟩,
      untwistedModel_of_bridgeEven chevalleyBridgesEven.g2 q hv hq e⟩
  have h := ((LieTypeIndex.valid_iff _).1 hv).1
  simpa only [LieTypeIndex.inStandardRange_iff, PrimePower.card_def] using h

theorem catalogBridgeFor_F4_of_even
    (q : PrimePower) (hv : (LieTypeIndex.F4 q).Valid)
    (hq : q.p = 2) : CatalogBridgeFor (.lie ⟨.F4 q, hv⟩) := fun _ _ _ _ ⟨e⟩ =>
  catalog_of_chevalleyExceptionalModel .F4 (by decide) q.p q.exponent
    ⟨⟨q.prime_p, q.exponent_pos, rfl⟩,
      untwistedModel_of_bridgeEven chevalleyBridgesEven.f4 q hv hq e⟩

theorem catalogBridgeFor_E6_of_even
    (q : PrimePower) (hv : (LieTypeIndex.E6 q).Valid)
    (hq : q.p = 2) : CatalogBridgeFor (.lie ⟨.E6 q, hv⟩) := fun _ _ _ _ ⟨e⟩ =>
  catalog_of_chevalleyExceptionalModel .E6 (by decide) q.p q.exponent
    ⟨⟨q.prime_p, q.exponent_pos, rfl⟩,
      untwistedModel_of_bridgeEven chevalleyBridgesEven.e6 q hv hq e⟩

theorem catalogBridgeFor_E7_of_even
    (q : PrimePower) (hv : (LieTypeIndex.E7 q).Valid)
    (hq : q.p = 2) : CatalogBridgeFor (.lie ⟨.E7 q, hv⟩) := fun _ _ _ _ ⟨e⟩ =>
  catalog_of_chevalleyExceptionalModel .E7 (by decide) q.p q.exponent
    ⟨⟨q.prime_p, q.exponent_pos, rfl⟩,
      untwistedModel_of_bridgeEven chevalleyBridgesEven.e7 q hv hq e⟩

theorem catalogBridgeFor_E8_of_even
    (q : PrimePower) (hv : (LieTypeIndex.E8 q).Valid)
    (hq : q.p = 2) : CatalogBridgeFor (.lie ⟨.E8 q, hv⟩) := fun _ _ _ _ ⟨e⟩ =>
  catalog_of_chevalleyExceptionalModel .E8 (by decide) q.p q.exponent
    ⟨⟨q.prime_p, q.exponent_pos, rfl⟩,
      untwistedModel_of_bridgeEven chevalleyBridgesEven.e8 q hv hq e⟩

theorem catalogBridgeFor_twistedE6_of_even
    (q : PrimePower)
    (hv : (LieTypeIndex.twistedE6 q).Valid) (hq : q.p = 2) :
    CatalogBridgeFor (.lie ⟨.twistedE6 q, hv⟩) := fun _ _ _ _ ⟨e⟩ =>
  catalog_of_chevalleyExceptionalModel .twistedE6 (by decide) q.p q.exponent
    ⟨⟨q.prime_p, q.exponent_pos, rfl⟩,
      twistedModel_of_bridgeEven chevalleyBridgesEven.twistedE6 q hv hq (by decide) e⟩

theorem catalogBridgeFor_trialityD4_of_even
    (q : PrimePower)
    (hv : (LieTypeIndex.trialityD4 q).Valid) (hq : q.p = 2) :
    CatalogBridgeFor (.lie ⟨.trialityD4 q, hv⟩) := fun _ _ _ _ ⟨e⟩ =>
  catalog_of_chevalleyExceptionalModel .trialityD4 (by decide) q.p q.exponent
    ⟨⟨q.prime_p, q.exponent_pos, rfl⟩,
      twistedModel_of_bridgeEven chevalleyBridgesEven.trialityD4 q hv hq (by decide) e⟩

structure B1RemainingNonEven : Prop where
  orthogonalOdd : ∀ (r : ℕ) (q : PrimePower) (hv : (LieTypeIndex.B r q).Valid), 3 ≤ r →
    CatalogBridgeFor (.lie ⟨.B r q, hv⟩)
  orthogonalPlus : ∀ (r : ℕ) (q : PrimePower) (hv : (LieTypeIndex.D r q).Valid),
    CatalogBridgeFor (.lie ⟨.D r q, hv⟩)
  orthogonalMinus : ∀ (r : ℕ) (q : PrimePower) (hv : (LieTypeIndex.twistedD r q).Valid),
    CatalogBridgeFor (.lie ⟨.twistedD r q, hv⟩)
  reeG2 : ∀ (m : ℕ) (hv : (LieTypeIndex.reeG2 m).Valid), CatalogBridgeFor (.lie ⟨.reeG2 m, hv⟩)
  reeF4 : ∀ (m : ℕ) (hv : (LieTypeIndex.reeF4 m).Valid), CatalogBridgeFor (.lie ⟨.reeF4 m, hv⟩)
  tits : ∀ hv : LieTypeIndex.tits.Valid, CatalogBridgeFor (.lie ⟨.tits, hv⟩)
  sporadic : ∀ s : SporadicName, CatalogBridgeFor (.sporadic s)

theorem b1Remaining_of_nonEven
    (h : B1RemainingNonEven) : B1Remaining where
  orthogonalOdd := h.orthogonalOdd
  orthogonalPlus := h.orthogonalPlus
  orthogonalMinus := h.orthogonalMinus
  g2Even := catalogBridgeFor_G2_of_even
  f4Even := catalogBridgeFor_F4_of_even
  e6Even := catalogBridgeFor_E6_of_even
  e7Even := catalogBridgeFor_E7_of_even
  e8Even := catalogBridgeFor_E8_of_even
  twistedE6Even := catalogBridgeFor_twistedE6_of_even
  trialityD4Even := catalogBridgeFor_trialityD4_of_even
  reeG2 := h.reeG2
  reeF4 := h.reeF4
  tits := h.tits
  sporadic := h.sporadic

theorem catalogBridgeFor_of_nonEven
    (h : B1RemainingNonEven) (i : CFSGIndex) :
    CatalogBridgeFor i :=
  catalogBridgeFor_of_remaining (b1Remaining_of_nonEven h) i

theorem tcKGroupBridge_of_nonEven
    (h : B1RemainingNonEven) : TCKGroupBridge :=
  tcKGroupBridge_of_remaining (b1Remaining_of_nonEven h)

end CFSG.TauCetiBridge.Even
