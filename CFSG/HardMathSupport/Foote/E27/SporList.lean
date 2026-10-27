module

public import CFSG.HardMathSupport.Foote.E27.Spor
public import CFSG.RankThree.PartOne.KS.ONPlane

public section

namespace CFSG.HardMathSupport.Foote.E27

open CFSG.Blueprint

@[expose] def sporBigNames : Finset TauCeti.SporadicName :=
  {.J3, .McL, .Suz, .Ly, .Co1, .Co2, .Co3, .Fi22, .Fi23, .Fi24Prime, .HN, .Th, .B, .M}

section Certificates


theorem not_three_pow_five_dvd_card_carrier (s : TauCeti.SporadicName) (hs : s ∉ sporBigNames) :
    ¬ 3 ^ 5 ∣ Nat.card (NativeSporadic.Carrier s) := by
  cases s <;> simp [sporBigNames] at hs
  · show ¬ 3 ^ 5 ∣ Nat.card NativeSporadic.M11
    rw [CFSG.Sporadic.Schreier.m11_card]; decide
  · show ¬ 3 ^ 5 ∣ Nat.card NativeSporadic.M12
    rw [CFSG.Sporadic.Schreier.m12_card]; decide
  · show ¬ 3 ^ 5 ∣ Nat.card NativeSporadic.M22
    rw [CFSG.Sporadic.Schreier.m22_card]; decide
  · show ¬ 3 ^ 5 ∣ Nat.card NativeSporadic.M23
    rw [CFSG.Sporadic.Schreier.m23_card]; decide
  · show ¬ 3 ^ 5 ∣ Nat.card NativeSporadic.M24
    rw [CFSG.Sporadic.Schreier.m24_card]; decide
  · show ¬ 3 ^ 5 ∣ Nat.card NativeSporadic.J1
    rw [CFSG.Sporadic.J1.card_J1]; decide
  · show ¬ 3 ^ 5 ∣ Nat.card NativeSporadic.J2
    rw [CFSG.Sporadic.J2.card_J2]; decide
  · show ¬ 3 ^ 5 ∣ Nat.card NativeSporadic.J4
    rw [CFSG.Sporadic.J4.card_J4]; decide
  · show ¬ 3 ^ 5 ∣ Nat.card NativeSporadic.HS
    rw [CFSG.Sporadic.HS.card_HS]; decide
  · show ¬ 3 ^ 5 ∣ Nat.card NativeSporadic.He
    rw [(CFSG.Sporadic.He.fam_he_order).1]; decide
  · show ¬ 3 ^ 5 ∣ Nat.card NativeSporadic.Ru
    rw [CFSG.Sporadic.Ru.card_Ru]; decide
  · show ¬ 3 ^ 5 ∣ Nat.card NativeSporadic.ON
    rw [CFSG.RankThree.PartOne.card_ON_eq_card_Pv]; decide

theorem mem_sporBigNames_of_dvd
    (hbr : ∀ s : TauCeti.SporadicName,
      Nonempty (NativeSporadic.Carrier s ≃* (TauCeti.CFSGIndex.sporadic s).Group))
    {s : TauCeti.SporadicName} (h : 3 ^ 5 ∣ Nat.card (TauCeti.CFSGIndex.sporadic s).Group) :
    s ∈ sporBigNames := by
  by_contra hs
  obtain ⟨e⟩ := hbr s
  rw [← Nat.card_congr e.toEquiv] at h
  exact not_three_pow_five_dvd_card_carrier s hs h

theorem e27SporBig_of_names
    (hbr : ∀ s : TauCeti.SporadicName,
      Nonempty (NativeSporadic.Carrier s ≃* (TauCeti.CFSGIndex.sporadic s).Group))
    (h : ∀ (X : Type) [Group X] [Finite X] (K R T : Subgroup X) (z : X), E27Config X K R T z →
      z ∈ K → ∀ s ∈ sporBigNames, Nonempty (↥K ≃* (TauCeti.CFSGIndex.sporadic s).Group) →
        False) : E27SporBig :=
  fun X _ _ K R T z hc hz s hs e => h X K R T z hc hz s (mem_sporBigNames_of_dvd hbr hs) e

end Certificates

end CFSG.HardMathSupport.Foote.E27
