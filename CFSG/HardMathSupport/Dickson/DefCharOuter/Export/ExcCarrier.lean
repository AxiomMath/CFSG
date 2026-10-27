module

public import CFSG.HardMathSupport.Dickson.DefCharOuter.Export.ExcFacts
public import CFSG.Adapters.TauCetiExceptional.B1Exceptional
public import CFSG.LieType.Simplicity.ExceptionalConverse
public import CFSG.HardMathSupport.Dickson.DefCharOuter.Export.Defs

public section

namespace CFSG.HardMathSupport.Dickson.DefCharOuter.Export

open CFSG.Open CFSG.Blueprint CFSG.Blueprint.Chevalley CFSG.LieType.Chevalley
  CFSG.HardMathSupport.Solomon.Coordinator CFSG.Yardstones.Md0ec50421ce4
  CFSG.ComponentClassification.CatLeaf
open CFSG.Yardstones.Md42047359a2a (LieFamily lieFamily)


theorem excCarrier_model (d : TauCeti.ValidLieTypeIndex)
    (hfam : lieFamily d.1 = LieFamily.exceptional) (hp2 : d.1.characteristic ≠ 2) :
    ∃ (t : StatedLieTag) (p f : ℕ), t ∈ chevalleyExceptionalTags ∧ p ≠ 2 ∧
      ChevalleyExceptionalModel (TauCeti.CFSGIndex.lie d).Group t p f := by
  obtain ⟨d, hv⟩ := d
  have hB := CFSG.TauCetiBridge.chevalleyBridges
  cases d with
  | G2 q =>
    have hq2 : q.p ≠ 2 := by simpa using hp2
    have h3 : 3 ≤ q.p ^ q.exponent := by
      have h := ((TauCeti.LieTypeIndex.valid_iff _).1 hv).1
      simpa only [TauCeti.LieTypeIndex.inStandardRange_iff, TauCeti.PrimePower.card_def] using h
    exact ⟨.G2, q.p, q.exponent, by decide, hq2, ⟨q.prime_p, q.exponent_pos, rfl, h3⟩,
      CFSG.TauCetiBridge.untwistedModel_of_bridge hB.g2 q hv hq2 (MulEquiv.refl _)⟩
  | F4 q =>
    have hq2 : q.p ≠ 2 := by simpa using hp2
    exact ⟨.F4, q.p, q.exponent, by decide, hq2, ⟨q.prime_p, q.exponent_pos, rfl⟩,
      CFSG.TauCetiBridge.untwistedModel_of_bridge hB.f4 q hv hq2 (MulEquiv.refl _)⟩
  | E6 q =>
    have hq2 : q.p ≠ 2 := by simpa using hp2
    exact ⟨.E6, q.p, q.exponent, by decide, hq2, ⟨q.prime_p, q.exponent_pos, rfl⟩,
      CFSG.TauCetiBridge.untwistedModel_of_bridge hB.e6 q hv hq2 (MulEquiv.refl _)⟩
  | E7 q =>
    have hq2 : q.p ≠ 2 := by simpa using hp2
    exact ⟨.E7, q.p, q.exponent, by decide, hq2, ⟨q.prime_p, q.exponent_pos, rfl⟩,
      CFSG.TauCetiBridge.untwistedModel_of_bridge hB.e7 q hv hq2 (MulEquiv.refl _)⟩
  | E8 q =>
    have hq2 : q.p ≠ 2 := by simpa using hp2
    exact ⟨.E8, q.p, q.exponent, by decide, hq2, ⟨q.prime_p, q.exponent_pos, rfl⟩,
      CFSG.TauCetiBridge.untwistedModel_of_bridge hB.e8 q hv hq2 (MulEquiv.refl _)⟩
  | twistedE6 q =>
    have hq2 : q.p ≠ 2 := by simpa using hp2
    exact ⟨.twistedE6, q.p, q.exponent, by decide, hq2, ⟨q.prime_p, q.exponent_pos, rfl⟩,
      CFSG.TauCetiBridge.twistedModel_of_bridge hB.twistedE6 q hv hq2 (by decide)
        (MulEquiv.refl _)⟩
  | trialityD4 q =>
    have hq2 : q.p ≠ 2 := by simpa using hp2
    exact ⟨.trialityD4, q.p, q.exponent, by decide, hq2, ⟨q.prime_p, q.exponent_pos, rfl⟩,
      CFSG.TauCetiBridge.twistedModel_of_bridge hB.trialityD4 q hv hq2 (by decide)
        (MulEquiv.refl _)⟩
  | _ => simp [lieFamily] at hfam

theorem carrierOn_exceptional : CarrierOn LieFamily.exceptional := by
  intro d hfam hp2
  obtain ⟨t, p, f, ht, hp, h⟩ := excCarrier_model d hfam hp2
  haveI : Finite (TauCeti.CFSGIndex.lie d).Group :=
    CFSG.LieType.Simplicity.fam_chevalley_exceptional_finiteness _ t p f h
  obtain ⟨-, hs⟩ := CFSG.LieType.Simplicity.fam_chevalley_exceptional_simplicity _ t p f h
  refine ⟨inferInstance, hs, ?_⟩
  by_contra hcon
  push Not at hcon
  haveI := hs
  let _ : CommGroup (TauCeti.CFSGIndex.lie d).Group :=
    { (inferInstance : Group (TauCeti.CFSGIndex.lie d).Group) with mul_comm := hcon }
  have hprime := IsSimpleGroup.prime_card (α := (TauCeti.CFSGIndex.lie d).Group)
  have hdvd := excModel_pow_dvd_card ht hp h
  have hN := excSylowExponent_ge ht
  have hf : 1 ≤ f := h.1.2.1
  have hpp : p.Prime := h.1.1
  have h6 : p ^ 6 ∣ Nat.card (TauCeti.CFSGIndex.lie d).Group :=
    (pow_dvd_pow p (by nlinarith)).trans hdvd
  have hpd : p ∣ Nat.card (TauCeti.CFSGIndex.lie d).Group := (dvd_pow_self p (by norm_num)).trans h6
  have hpeq : p = Nat.card (TauCeti.CFSGIndex.lie d).Group :=
    ((Nat.dvd_prime hprime).1 hpd).resolve_left hpp.ne_one
  rw [← hpeq] at h6
  have h1 : p ^ 6 ≤ p := Nat.le_of_dvd hpp.pos h6
  have h2 : p < p ^ 6 := by
    calc p = p ^ 1 := (pow_one p).symm
      _ < p ^ 6 := Nat.pow_lt_pow_right hpp.one_lt (by norm_num)
  exact absurd h1 (not_le.2 h2)

end CFSG.HardMathSupport.Dickson.DefCharOuter.Export
