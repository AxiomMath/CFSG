module

public import CFSG.HardMathSupport.Solomon.Coordinator.B3SporExact
public import CFSG.HardMathSupport.Timmesfeld.SporadicBalance.Parts

public section

namespace CFSG.HardMathSupport.Solomon.Coordinator

open CFSG.HardMathSupport.Timmesfeld.SporadicBalance CFSG.HardMathSupport.Timmesfeld.Tables.Census
  CFSG.HardMathSupport.Timmesfeld.Coordinator

theorem b3SporPair_of_sporadicOPrimeHolds {name : TauCeti.SporadicName} {p : ℕ} (hp : p.Prime)
    (hp2 : p ≠ 2) (hbr : SporadicBridges) (hOut : SporadicOuterLeTwo)
    (h : SporadicOPrimeHolds name p) : B3SporPair name p :=
  b3SporPair_of_oPrimeCoreTrivial hp hp2 hOut fun S _ _ _ ⟨e⟩ =>
    h S ⟨e.trans (hbr name).some.symm⟩

@[expose] def B3SporRestPair (name : TauCeti.SporadicName) (p : ℕ) : Prop :=
  (p = 3 ∧ name ∈ ({.M11, .M12, .M22, .M23, .M24, .J2, .J4, .HS, .Ru, .He} :
    Finset TauCeti.SporadicName)) ∨
  (p = 5 ∧ name ∈ ({.J2, .HS, .McL, .Suz, .He, .Ru, .Co2, .Co3, .Fi22, .Fi23, .Fi24Prime, .Th} :
    Finset TauCeti.SporadicName)) ∨
  (p = 7 ∧ name ∈ ({.He, .ONan, .Co1, .Fi24Prime, .Th, .B} : Finset TauCeti.SporadicName)) ∨
  (p = 11 ∧ name ∈ ({.J4, .M} : Finset TauCeti.SporadicName)) ∨
  (p = 13 ∧ name = .M)

@[expose] def SporadicP2Table : Prop :=
  ∀ (name : TauCeti.SporadicName) (p : ℕ), p.Prime → p ≠ 2 →
    p ^ 2 ∣ Nat.card (TauCeti.CFSGIndex.sporadic name).Group →
      SporadicOnePair name p ∨ B3SporRestPair name p

theorem b3SporPair_all (hbr : SporadicBridges) (hOut : SporadicOuterLeTwo)
    (hO : ∀ name p, SporadicOnePair name p → SporadicOPrimeHolds name p)
    (hTab : SporadicP2Table)
    (hrest : ∀ name p, B3SporRestPair name p → B3SporPair name p) :
    ∀ name p, p.Prime → p ≠ 2 → B3SporPair name p := by
  intro name p hp hp2
  by_cases h2 : p ^ 2 ∣ Nat.card (TauCeti.CFSGIndex.sporadic name).Group
  · rcases hTab name p hp hp2 h2 with h | h
    · exact b3SporPair_of_sporadicOPrimeHolds hp hp2 hbr hOut (hO name p h)
    · exact hrest name p h
  · refine b3SporPair_of_card_exact hp hp2 hOut fun S _ _ he => ?_
    rw [Nat.card_congr he.some.toEquiv]
    exact h2

theorem sporadicOPrime_of_parts (hOne : SporadicOneParts) :
    ∀ name p, SporadicOnePair name p → SporadicOPrimeHolds name p :=
  fun name p h => (hOne.holds name p h).1

theorem b3SimpleSpor_of_parts (hbr : SporadicBridges) (hOut : SporadicOuterLeTwo)
    (hO : ∀ name p, SporadicOnePair name p → SporadicOPrimeHolds name p)
    (hTab : SporadicP2Table)
    (hrest : ∀ name p, B3SporRestPair name p → B3SporPair name p) : B3SimpleSpor :=
  b3SimpleSpor_of_pairs fun name => b3SporPair_all hbr hOut hO hTab hrest name 3
    Nat.prime_three (by norm_num)

theorem input14_5Spor_of_parts (hbr : SporadicBridges) (hOut : SporadicOuterLeTwo)
    (hO : ∀ name p, SporadicOnePair name p → SporadicOPrimeHolds name p)
    (hTab : SporadicP2Table)
    (hrest : ∀ name p, B3SporRestPair name p → B3SporPair name p) : Input14_5Spor :=
  input14_5Spor_of_pairs (b3SporPair_all hbr hOut hO hTab hrest)

end CFSG.HardMathSupport.Solomon.Coordinator
