module

public import CFSG.HardMathSupport.Timmesfeld.SporadicBalance.OuterTrivial
public import CFSG.Sporadic.NativeFinite
public import CFSG.Sporadic.B

public section

namespace CFSG.HardMathSupport.Timmesfeld.SporadicBalance

open CFSG.Blueprint CFSG.Monster.Generated

theorem sporadicOPrimeHolds_of_carrier {name : TauCeti.SporadicName} {p : ℕ}
    (h : OPrimeCoreTrivialAt p (NativeSporadic.Carrier name)) : SporadicOPrimeHolds name p :=
  fun _ _ _ _ ⟨e⟩ => OPrimeCoreTrivialAt.of_mulEquiv e h

theorem oPrimeCoreTrivialAt_carrier_of_sporadicOPrimeHolds {name : TauCeti.SporadicName} {p : ℕ}
    [Finite (NativeSporadic.Carrier name)] [IsSimpleGroup (NativeSporadic.Carrier name)]
    (h : SporadicOPrimeHolds name p) : OPrimeCoreTrivialAt p (NativeSporadic.Carrier name) :=
  h _ ⟨MulEquiv.refl _⟩

theorem sporadicOPrimeHolds_B_iff
    (p : ℕ) : SporadicOPrimeHolds .B p ↔ OPrimeCoreTrivialAt p NativeSporadic.B := by
  have : IsSimpleGroup (NativeSporadic.Carrier .B) := CFSG.Sporadic.B.fam_b_simplicity
  have : Finite (NativeSporadic.Carrier .B) :=
    CFSG.Sporadic.finite_carrier_of_ne_M .B (by decide)
  exact ⟨oPrimeCoreTrivialAt_carrier_of_sporadicOPrimeHolds,
    sporadicOPrimeHolds_of_carrier (name := .B)⟩

theorem sporadicOPrimeHolds_M_of_gmat
    {p : ℕ} (h : OPrimeCoreTrivialAt p Gmat) : SporadicOPrimeHolds .M p := by
  intro S _ _ _ ⟨e⟩
  obtain ⟨f⟩ := CFSG.RankThree.PartOne.SPOR.mulEquiv_Gmat_of_simple e
  exact OPrimeCoreTrivialAt.of_mulEquiv f h

theorem sporadicOnePairHolds_B_of_oPrime
    {p : ℕ} (h : OPrimeCoreTrivialAt p NativeSporadic.B) : SporadicOnePairHolds .B p :=
  ⟨sporadicOPrimeHolds_of_carrier (name := .B) h, sporadicOuterHolds_B p⟩

theorem sporadicOnePairHolds_M_of_gmat
    {p : ℕ} (h : OPrimeCoreTrivialAt p Gmat) : SporadicOnePairHolds .M p :=
  ⟨sporadicOPrimeHolds_M_of_gmat h, sporadicOuterHolds_M p⟩

end CFSG.HardMathSupport.Timmesfeld.SporadicBalance
