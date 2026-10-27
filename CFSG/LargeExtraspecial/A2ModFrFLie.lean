module

public import CFSG.LargeExtraspecial.A2ModFrFTwo
public import CFSG.LargeExtraspecial.A2ModFrFNSL
public import CFSG.LargeExtraspecial.A2ModOrdCard
public import CFSG.LargeExtraspecial.A2ModFrFMain

public section

namespace CFSG.LargeExtraspecial.A2Mod.FrF

open Module CFSG.LieType.Universal CFSG.LieType.CurtisTits CFSG.LieType.RootSystem
  CFSG.LieType.Steinberg CFSG.Timmesfeld.ARS CFSG.Timmesfeld.ARS.ExclNS CFSG.Blueprint.Chevalley
  CFSG.RankThree.OrthogonalInvolutions CFSG.Open CFSG.Blueprint

theorem ordF4_two_eq : ordF4 2 = 2 ^ 24 * 197358525 := by decide

theorem ordTwistedE6_two_eq : ordTwistedE6 2 = 2 ^ 36 * 1113694156575 := by decide

theorem thirteen_not_dvd : ∀ j, 1 ≤ j → j ≤ 7 + 2 * 2 → ¬ 13 ∣ 2 ^ j - 1 := by decide

theorem nineteen_not_dvd : ∀ j, 1 ≤ j → j ≤ 7 + 2 * 4 → ¬ 19 ∣ 2 ^ j - 1 := by decide


variable {G : Type} [Group G] {R : Set (Subgroup G)} {D : Set G} {V : Type} [AddCommGroup V]
  [Module (ZMod 2) V] [FiniteDimensional (ZMod 2) V] {Q : QuadraticForm (ZMod 2) V}
  {ρ : G →* (V ≃ₗ[ZMod 2] V)}

namespace F4Frame

theorem false_of_lieModel_F4 [Finite G] (F : F4Frame G R) (hR : IsRootClass R)
    (hiso : NoIsolated R) (hRD : ∀ E ∈ R, ∃ d ∈ D, E = Subgroup.zpowers d)
    (hDc : ∀ g, ∀ d ∈ D, g * d * g⁻¹ ∈ D) (hA : A2Action D Q ρ) {n : ℕ}
    (hG : LieModel G .F4 n 2 1) : False := by
  have hcard : Nat.card G = ordF4 2 := Ord.card_of_lieModel_F4 hG
  have hm : Nat.card (F.X a2v) ≤ 2 ^ 1 :=
    F.card_a2v_le_of_card hR hRD (hcard.trans ordF4_two_eq) (by decide) (by norm_num)
  exact F.false_of_a2Action hR hRD hDc hiso hA hm (by norm_num) (by norm_num)
    (by rw [hcard, ordF4_two_eq]; decide) thirteen_not_dvd

theorem false_of_lieModel_twistedE6 [Finite G] (F : F4Frame G R) (hR : IsRootClass R)
    (hiso : NoIsolated R) (hRD : ∀ E ∈ R, ∃ d ∈ D, E = Subgroup.zpowers d)
    (hDc : ∀ g, ∀ d ∈ D, g * d * g⁻¹ ∈ D) (hA : A2Action D Q ρ) {n : ℕ}
    (hG : LieModel G .twistedE6 n 2 1) : False := by
  have hcard : Nat.card G = ordTwistedE6 2 := Ord.card_of_lieModel_twistedE6 hG
  have hm : Nat.card (F.X a2v) ≤ 2 ^ 2 :=
    F.card_a2v_le_of_card hR hRD (hcard.trans ordTwistedE6_two_eq) (by decide)
      (by norm_num)
  exact F.false_of_a2Action hR hRD hDc hiso hA hm (by norm_num) (by norm_num)
    (by rw [hcard, ordTwistedE6_two_eq]; decide) nineteen_not_dvd

end F4Frame


theorem false_of_nslFrame_lieModel [Finite G] (F : NSLFrameData G R)
    (hF4 : F.D.rank = Tag.rank .F4 ∧ HEq F.D.cartan (Tag.cartan .F4)) (hR : IsRootClass R)
    (hiso : NoIsolated R) (hRD : ∀ E ∈ R, ∃ d ∈ D, E = Subgroup.zpowers d)
    (hDc : ∀ g, ∀ d ∈ D, g * d * g⁻¹ ∈ D) (hA : A2Action D Q ρ) {n : ℕ}
    (hG : LieModel G .F4 n 2 1 ∨ LieModel G .twistedE6 n 2 1) : False := by
  obtain ⟨F', -⟩ := exists_f4Frame_of_nslFrame F hF4
  rcases hG with hG | hG
  · exact F'.false_of_lieModel_F4 hR hiso hRD hDc hA hG
  · exact F'.false_of_lieModel_twistedE6 hR hiso hRD hDc hA hG

end CFSG.LargeExtraspecial.A2Mod.FrF
