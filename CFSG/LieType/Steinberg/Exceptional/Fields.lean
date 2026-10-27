module

public import CFSG.LieType.Steinberg.TwistedE6.Defs
public import Mathlib.FieldTheory.Finite.GaloisField
public import Certificates.Certificate113
public import Certificates.Certificate114
public import Certificates.Certificate115
public import Certificates.Certificate116
public import Certificates.Certificate123

public noncomputable section

namespace CFSG.LieType.Steinberg.Exceptional

open CFSG.LieType.Steinberg.TwistedE6

variable (p f : ℕ) [Fact p.Prime]

@[expose] def frobQ : GaloisField p (2 * f) →+* GaloisField p (2 * f) :=
  iterateFrobenius (GaloisField p (2 * f)) p f

theorem frobQ_apply (c : GaloisField p (2 * f)) : frobQ p f c = c ^ (p ^ f) :=
  iterateFrobenius_def p f c

theorem frobQ_frobQ (hf : 1 ≤ f) (c : GaloisField p (2 * f)) : frobQ p f (frobQ p f c) = c := by
  classical
  have : Fintype (GaloisField p (2 * f)) := Fintype.ofFinite _
  rw [frobQ_apply, frobQ_apply, ← pow_mul, ← pow_add]
  have h := FiniteField.pow_card c
  rw [Fintype.card_eq_nat_card, GaloisField.card p (2 * f) (by omega)] at h
  rw [show f + f = 2 * f by ring]
  exact h

abbrev twistedE6Group : Type :=
  ↥(fixedGroup (GaloisField p (2 * f)) (frobQ p f))

abbrev twistedE6Datum : CFSG.LieType.Universal.UniversalRootDatum (twistedE6Group p f) :=
  twistedDatum (GaloisField p (2 * f)) (frobQ p f)

end CFSG.LieType.Steinberg.Exceptional
