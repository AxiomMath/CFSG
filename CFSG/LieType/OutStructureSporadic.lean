module

public import CFSG.HardMathSupport.Timmesfeld.Proving.SporadicOuterLeTwo

public section

namespace CFSG.LieType.OutStructure

open CFSG.ComponentClassification.OuterAutomorphisms

theorem i713_of_mulEquiv_sporadic
    {K : Type} [Group K] [Finite K] (hK : IsSimpleGroup K)
    (hnab : ∃ a b : K, a * b ≠ b * a)
    {s : TauCeti.SporadicName} (e : K ≃* (TauCeti.CFSGIndex.sporadic s).Group)
    {p : ℕ} (hp : p.Prime) (hp2 : p ≠ 2) :
    ¬ p ∣ Nat.card (Outer K) := by
  have hle : Nat.card (Outer K) ≤ 2 :=
    CFSG.HardMathSupport.Timmesfeld.Proving.sporadicOuterLeTwo_holds K hK hnab s ⟨e⟩
  intro hdvd
  have hpos : 0 < Nat.card (Outer K) := Nat.card_pos
  have hp3 : 2 < p := lt_of_le_of_ne hp.two_le (Ne.symm hp2)
  have h1 : p ≤ Nat.card (Outer K) := Nat.le_of_dvd hpos hdvd
  omega

end CFSG.LieType.OutStructure
