module

public import CFSG.LocalAnalysis.EvenSporadicStandard.HSStd.Zassenhaus.ONanProps

public section

namespace CFSG.EvenSporadicStandard.HSStd.Zassenhaus.ONan

open Subgroup CFSG.Blueprint CFSG.Blueprint.NativeSporadic

@[expose] def InspectionArm (Q : (N : Type) → [Group N] → Prop) : Prop :=
  ∀ (Y : Type) [Group Y] [Finite Y] (N : Subgroup Y), N.Normal → centralizer (N : Set Y) ≤ N →
    Q ↥N →
    ∀ P : Subgroup Y, (∀ a ∈ P, ∀ b ∈ P, a * b = b * a) → (∀ a ∈ P, a ^ 3 = 1) →
    Nat.card P = 9 → (∀ a ∈ P, a ≠ 1 → Nat.card (centralizer ({a} : Set Y)) = 360) →
    (∃ w : Y, orderOf w = 2 ∧ ∃ H : Subgroup Y, H ≤ centralizer ({w} : Set Y) ∧
      Nonempty (↥H ≃* ↥CFSG.QuasithinUnique.A6Models.pgl29)) →
    IsSporadic Y .HS

theorem onanInspection_of_arms
    (hU35 : InspectionArm fun N _ => LieModel N .PSU 3 5 1)
    (hL37 : InspectionArm fun N _ => LieModel N .PSL 3 7 1)
    (hM22 : InspectionArm fun N _ => IsSporadic N .M22)
    (hM23 : InspectionArm fun N _ => IsSporadic N .M23)
    (hM24 : InspectionArm fun N _ => IsSporadic N .M24)
    (hHS : InspectionArm fun N _ => IsSporadic N .HS)
    (hRu : InspectionArm fun N _ => IsSporadic N .Ru)
    (hL52 : InspectionArm fun N _ => LieModel N .PSL 5 2 1)
    (hJ2 : InspectionArm fun N _ => IsSporadic N .J2)
    (hSp44 : InspectionArm fun N _ => LieModel N .PSp 2 2 2) :
    ONanInspection := by
  intro Y _ _ N hN hC hList P hPab hP3 hP9 hPc hw
  rcases hList with h | h | h | h | h | h | h | h | h | h
  · exact hU35 Y N hN hC h P hPab hP3 hP9 hPc hw
  · exact hL37 Y N hN hC h P hPab hP3 hP9 hPc hw
  · exact hM22 Y N hN hC h P hPab hP3 hP9 hPc hw
  · exact hM23 Y N hN hC h P hPab hP3 hP9 hPc hw
  · exact hM24 Y N hN hC h P hPab hP3 hP9 hPc hw
  · exact hHS Y N hN hC h P hPab hP3 hP9 hPc hw
  · exact hRu Y N hN hC h P hPab hP3 hP9 hPc hw
  · exact hL52 Y N hN hC h P hPab hP3 hP9 hPc hw
  · exact hJ2 Y N hN hC h P hPab hP3 hP9 hPc hw
  · exact hSp44 Y N hN hC h P hPab hP3 hP9 hPc hw

end CFSG.EvenSporadicStandard.HSStd.Zassenhaus.ONan
