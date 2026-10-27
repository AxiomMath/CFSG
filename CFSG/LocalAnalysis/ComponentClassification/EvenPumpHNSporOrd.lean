module

public import CFSG.LocalAnalysis.ComponentClassification.EvenPumpHNLeaf
public import CFSG.Sporadic.Fi24.Simple
public import CFSG.LocalAnalysis.ComponentClassification.UnbalancedCorrSporadicDihedralGW
public import CFSG.LocalAnalysis.SectionRank.SporadicCover
public import CFSG.Sporadic.Co1
public import CFSG.Sporadic.Co2
public import CFSG.Sporadic.Co3
public import CFSG.Sporadic.Fi22.Simple
public import CFSG.Sporadic.HS
public import CFSG.Sporadic.J2
public import CFSG.Sporadic.J3
public import CFSG.Sporadic.J4
public import CFSG.Sporadic.Ly
public import CFSG.Sporadic.McL.Simple
public import CFSG.Sporadic.ONOddCore.Block
public import CFSG.Sporadic.Ru
public import CFSG.Sporadic.Suz.Simple

public section

namespace CFSG.ComponentClassification.EvenPump

open CFSG Subgroup CFSG.Blueprint CFSG.ComponentClassification.CatLeaf

theorem not_hn_order_carrier
    {s : TauCeti.SporadicName} (hB : s ≠ .B) (hM : s ≠ .M) :
    ¬ (273030912000000 ∣ Nat.card (NativeSporadic.Carrier s) ∧
      2 * 273030912000000 ≤ Nat.card (NativeSporadic.Carrier s)) := by
  cases s with
  | M11 => rw [show Nat.card (NativeSporadic.Carrier .M11) = Nat.card NativeSporadic.M11 from rfl,
      Sporadic.Mathieu.card_M11]; decide
  | M12 => rw [show Nat.card (NativeSporadic.Carrier .M12) = Nat.card NativeSporadic.M12 from rfl,
      Sporadic.Mathieu.card_M12]; decide
  | M22 => rw [show Nat.card (NativeSporadic.Carrier .M22) = Nat.card NativeSporadic.M22 from rfl,
      Sporadic.Mathieu.card_M22]; decide
  | M23 => rw [show Nat.card (NativeSporadic.Carrier .M23) = Nat.card NativeSporadic.M23 from rfl,
      Sporadic.Schreier.m23_card]; decide
  | M24 => rw [show Nat.card (NativeSporadic.Carrier .M24) = Nat.card NativeSporadic.M24 from rfl,
      Sporadic.Mathieu.card_M24]; decide
  | J1 =>
    rcases SectionRank.card_small_sporadic (s := .J1) (Or.inr (Or.inr (Or.inr rfl))) with
      h | h | h | h <;> rw [h] <;> decide
  | J2 => rw [show Nat.card (NativeSporadic.Carrier .J2) = Nat.card NativeSporadic.J2 from rfl,
      Sporadic.J2.card_J2]; decide
  | J3 => rw [show Nat.card (NativeSporadic.Carrier .J3) = Nat.card NativeSporadic.J3 from rfl,
      Sporadic.J3.card_J3]; decide
  | J4 => rw [show Nat.card (NativeSporadic.Carrier .J4) = Nat.card NativeSporadic.J4 from rfl,
      Sporadic.J4.card_J4]; decide
  | HS => rw [show Nat.card (NativeSporadic.Carrier .HS) = Nat.card NativeSporadic.HS from rfl,
      Sporadic.HS.card_HS]; decide
  | McL => rw [show Nat.card (NativeSporadic.Carrier .McL) = Nat.card NativeSporadic.McL from rfl,
      Sporadic.McL.card_McL]; decide
  | He => rw [show Nat.card (NativeSporadic.Carrier .He) = Nat.card NativeSporadic.He from rfl,
      Sporadic.He.card_He]; decide
  | Ru => rw [show Nat.card (NativeSporadic.Carrier .Ru) = Nat.card NativeSporadic.Ru from rfl,
      Sporadic.Ru.card_Ru]; decide
  | Suz => rw [show Nat.card (NativeSporadic.Carrier .Suz) = Nat.card NativeSporadic.Suz from rfl,
      Sporadic.Suz.card_Suz]; decide
  | ONan => rw [show Nat.card (NativeSporadic.Carrier .ONan) = Nat.card NativeSporadic.ON from rfl,
      Sporadic.ONOddCore.card_native_ON]; decide
  | Co1 => rw [show Nat.card (NativeSporadic.Carrier .Co1) = Nat.card NativeSporadic.Co1 from rfl,
      Sporadic.Co1.card_Co1]; decide
  | Co2 => rw [show Nat.card (NativeSporadic.Carrier .Co2) = Nat.card NativeSporadic.Co2 from rfl,
      Sporadic.Co2.card_Co2]; decide
  | Co3 => rw [show Nat.card (NativeSporadic.Carrier .Co3) = Nat.card NativeSporadic.Co3 from rfl,
      Sporadic.Co3.card_Co3]; decide
  | Fi22 =>
    rw [show Nat.card (NativeSporadic.Carrier .Fi22) = Nat.card NativeSporadic.Fi22 from rfl,
      Sporadic.Fi22.card_Fi22]; decide
  | Fi23 =>
    rw [show Nat.card (NativeSporadic.Carrier .Fi23) = Nat.card NativeSporadic.Fi23 from rfl,
      Sporadic.Fi23.card_Fi23]; decide
  | Fi24Prime =>
    rw [show Nat.card (NativeSporadic.Carrier .Fi24Prime) =
      Nat.card NativeSporadic.Fi24prime from rfl, Sporadic.Fi24.card_Fi24prime]; decide
  | HN => rw [show Nat.card (NativeSporadic.Carrier .HN) = Nat.card NativeSporadic.HN from rfl,
      Sporadic.HNSchreier.card_HN]; decide
  | Ly => rw [show Nat.card (NativeSporadic.Carrier .Ly) = Nat.card NativeSporadic.Ly from rfl,
      Sporadic.Ly.card_Ly]; decide
  | Th => rw [show Nat.card (NativeSporadic.Carrier .Th) = Nat.card NativeSporadic.Th from rfl,
      UnbalancedCorr.card_nativeTh]; decide
  | B => exact absurd rfl hB
  | M => exact absurd rfl hM


theorem not_isHNType_of_properFixedComponent_sporadic_order
    {S : Type} [Group S] [Finite S] [IsSimpleGroup S] {s : TauCeti.SporadicName}
    (hB : s ≠ .B) (hM : s ≠ .M) (e : S ≃* NativeSporadic.Carrier s) {σ : MulAut S} {P : Subgroup S}
    (h : ProperFixedComponent σ P) : ¬ IsHNType (P ⧸ Open.fusionZStar P) := by
  intro hH
  obtain ⟨h1, h2⟩ := hn_dvd_and_double_le h hH
  rw [Nat.card_congr e.toEquiv] at h1 h2
  exact not_hn_order_carrier hB hM ⟨h1, h2⟩

end CFSG.ComponentClassification.EvenPump
