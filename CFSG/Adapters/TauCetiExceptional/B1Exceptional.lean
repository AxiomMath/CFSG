module

public import CFSG.Adapters.TauCetiExceptional.BridgeAll
public import CFSG.LocalAnalysis.QuasithinUnique.B1.Interface

public section

namespace CFSG.TauCetiBridge

open TauCeti CFSG.QuasithinUnique.B1 CFSG.Blueprint CFSG.Blueprint.Chevalley
  CFSG.Assembly.LowTwoRank

instance (q : PrimePower) : Fact q.p.Prime := ⟨q.prime_p⟩

abbrev fieldOf (q : PrimePower) (m : ℕ) : Type := GaloisField q.p (q.exponent * m)

theorem card_fieldOf (q : PrimePower) {m : ℕ} (hm : 0 < m) :
    Nat.card (fieldOf q m) = q.card ^ m := by
  rw [GaloisField.card q.p (q.exponent * m) (Nat.mul_ne_zero q.exponent_pos.ne' hm.ne'),
    PrimePower.card_def, pow_mul]

noncomputable abbrev frobOf (q : PrimePower) (m : ℕ) : fieldOf q m →+* fieldOf q m :=
  iterateFrobenius (fieldOf q m) q.p q.exponent

theorem frobOf_apply (q : PrimePower) (m : ℕ) (x : fieldOf q m) :
    frobOf q m x = x ^ q.card := by
  rw [iterateFrobenius_def, PrimePower.card_def]

theorem catalog_of_chevalleyExceptionalModel {S : Type} [Group S] (t : StatedLieTag)
    (ht : t ∈ chevalleyExceptionalTags) (p f : ℕ) (hmodel : ChevalleyExceptionalModel S t p f) :
    CFSG.Blueprint.Catalog S :=
  Or.inr (Or.inr (Or.inr (Or.inl (Or.inl ⟨t, p, f, ht, hmodel⟩))))

theorem untwistedModel_of_bridge {τ : Tag} {c : PrimePower → LieTypeIndex}
    (hB : UntwistedBridge τ c) (q : PrimePower) (hv : (c q).Valid) (hq : q.p ≠ 2)
    {S : Type} [Group S] (e : S ≃* ValidLieTypeIndex.Group ⟨c q, hv⟩) :
    UntwistedChevalleyModel S τ (q.p ^ q.exponent) := by
  have hK := card_fieldOf q Nat.one_pos
  rw [pow_one] at hK
  obtain ⟨φ⟩ := hB q hv hq (fieldOf q 1) hK
  exact ⟨fieldOf q 1, inferInstance, inferInstance, hK.trans q.card_def, ⟨e.trans φ.symm⟩⟩

theorem twistedModel_of_bridge {t : TwistTag} {c : PrimePower → LieTypeIndex}
    (hB : TwistedBridge t c) (q : PrimePower) (hv : (c q).Valid) (hq : q.p ≠ 2)
    (hm : 0 < t.order) {S : Type} [Group S] (e : S ≃* ValidLieTypeIndex.Group ⟨c q, hv⟩) :
    TwistedChevalleyModel S t (q.p ^ q.exponent) := by
  obtain ⟨φ⟩ := hB q hv hq (fieldOf q t.order) (card_fieldOf q hm) (frobOf q t.order)
    (frobOf_apply q t.order)
  refine ⟨fieldOf q t.order, inferInstance, inferInstance, ?_, frobOf q t.order, ?_,
    ⟨e.trans φ.symm⟩⟩
  · rw [card_fieldOf q hm, q.card_def]
  · intro x
    rw [frobOf_apply, q.card_def]

theorem catalogBridgeFor_G2_of_odd
    (q : PrimePower) (hv : (LieTypeIndex.G2 q).Valid)
    (hq : q.p ≠ 2) : CatalogBridgeFor (.lie ⟨.G2 q, hv⟩) := by
  intro S _ _ _ ⟨e⟩
  refine catalog_of_chevalleyExceptionalModel .G2 (by decide) q.p q.exponent
    ⟨⟨q.prime_p, q.exponent_pos, rfl, ?_⟩, untwistedModel_of_bridge chevalleyBridges.g2 q hv hq e⟩
  have h := ((LieTypeIndex.valid_iff _).1 hv).1
  simpa only [LieTypeIndex.inStandardRange_iff, PrimePower.card_def] using h

theorem catalogBridgeFor_F4_of_odd
    (q : PrimePower) (hv : (LieTypeIndex.F4 q).Valid)
    (hq : q.p ≠ 2) : CatalogBridgeFor (.lie ⟨.F4 q, hv⟩) := fun _ _ _ _ ⟨e⟩ =>
  catalog_of_chevalleyExceptionalModel .F4 (by decide) q.p q.exponent
    ⟨⟨q.prime_p, q.exponent_pos, rfl⟩, untwistedModel_of_bridge chevalleyBridges.f4 q hv hq e⟩

theorem catalogBridgeFor_E6_of_odd
    (q : PrimePower) (hv : (LieTypeIndex.E6 q).Valid)
    (hq : q.p ≠ 2) : CatalogBridgeFor (.lie ⟨.E6 q, hv⟩) := fun _ _ _ _ ⟨e⟩ =>
  catalog_of_chevalleyExceptionalModel .E6 (by decide) q.p q.exponent
    ⟨⟨q.prime_p, q.exponent_pos, rfl⟩, untwistedModel_of_bridge chevalleyBridges.e6 q hv hq e⟩

theorem catalogBridgeFor_E7_of_odd
    (q : PrimePower) (hv : (LieTypeIndex.E7 q).Valid)
    (hq : q.p ≠ 2) : CatalogBridgeFor (.lie ⟨.E7 q, hv⟩) := fun _ _ _ _ ⟨e⟩ =>
  catalog_of_chevalleyExceptionalModel .E7 (by decide) q.p q.exponent
    ⟨⟨q.prime_p, q.exponent_pos, rfl⟩, untwistedModel_of_bridge chevalleyBridges.e7 q hv hq e⟩

theorem catalogBridgeFor_E8_of_odd
    (q : PrimePower) (hv : (LieTypeIndex.E8 q).Valid)
    (hq : q.p ≠ 2) : CatalogBridgeFor (.lie ⟨.E8 q, hv⟩) := fun _ _ _ _ ⟨e⟩ =>
  catalog_of_chevalleyExceptionalModel .E8 (by decide) q.p q.exponent
    ⟨⟨q.prime_p, q.exponent_pos, rfl⟩, untwistedModel_of_bridge chevalleyBridges.e8 q hv hq e⟩

theorem catalogBridgeFor_twistedE6_of_odd
    (q : PrimePower)
    (hv : (LieTypeIndex.twistedE6 q).Valid) (hq : q.p ≠ 2) :
    CatalogBridgeFor (.lie ⟨.twistedE6 q, hv⟩) := fun _ _ _ _ ⟨e⟩ =>
  catalog_of_chevalleyExceptionalModel .twistedE6 (by decide) q.p q.exponent
    ⟨⟨q.prime_p, q.exponent_pos, rfl⟩,
      twistedModel_of_bridge Twisted.twistedBridge_twistedE6 q hv hq (by decide) e⟩

theorem catalogBridgeFor_trialityD4_of_odd
    (q : PrimePower)
    (hv : (LieTypeIndex.trialityD4 q).Valid) (hq : q.p ≠ 2) :
    CatalogBridgeFor (.lie ⟨.trialityD4 q, hv⟩) := fun _ _ _ _ ⟨e⟩ =>
  catalog_of_chevalleyExceptionalModel .trialityD4 (by decide) q.p q.exponent
    ⟨⟨q.prime_p, q.exponent_pos, rfl⟩,
      twistedModel_of_bridge Twisted.twistedBridge_trialityD4 q hv hq (by decide) e⟩

end CFSG.TauCetiBridge
