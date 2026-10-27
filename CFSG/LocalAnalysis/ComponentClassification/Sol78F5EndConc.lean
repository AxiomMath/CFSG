module

public import CFSG.LocalAnalysis.ComponentClassification.Sol78F5EndOne

public noncomputable section

namespace CFSG.ComponentClassification.Sol78.F514

open CFSG Subgroup CFSG.ComponentClassification.UnbalancedLayer
  CFSG.ComponentClassification.UnbalancedCorr CFSG.ComponentClassification.FooteLit
  CFSG.ABGLocalTools CFSG.ComponentClassification.Foote5

variable {G : Type} [Group G] [Finite G]

theorem footeFamilyType_of_quotient_equiv {X Y : Type} [Group X] [Group Y] {A : Subgroup X}
    {B : Subgroup Y} [IsSimpleGroup (A ⧸ pPrimeCore 2 A)]
    (hna : ∃ a b : A ⧸ pPrimeCore 2 A, a * b ≠ b * a)
    (e : A ⧸ pPrimeCore 2 A ≃* B ⧸ pPrimeCore 2 B) (h : FooteFamilyType A) :
    FooteFamilyType B := by
  have : IsSimpleGroup (B ⧸ pPrimeCore 2 B) := e.symm.isSimpleGroup
  have hnb : ∃ a b : B ⧸ pPrimeCore 2 B, a * b ≠ b * a := by
    obtain ⟨a, b, hab⟩ := hna
    exact ⟨e a, e b, fun h => hab (e.injective (by rw [map_mul, map_mul, h]))⟩
  let eA : A ⧸ Open.fusionZStar A ≃* A ⧸ pPrimeCore 2 A :=
    QuotientGroup.quotientMulEquivOfEq (fusionZStar_eq_pPrimeCore A hna)
  let eB : B ⧸ Open.fusionZStar B ≃* B ⧸ pPrimeCore 2 B :=
    QuotientGroup.quotientMulEquivOfEq (fusionZStar_eq_pPrimeCore B hnb)
  let f : B ⧸ Open.fusionZStar B ≃* A ⧸ Open.fusionZStar A := eB.trans (e.symm.trans eA.symm)
  rcases h with ⟨⟨e7⟩⟩ | ⟨p, q, hp, hp2, hq, h5, hL⟩
  · exact Or.inl ⟨f.trans e7⟩
  · exact Or.inr ⟨p, q, hp, hp2, hq, h5, LieType.CurtisTits.lieModel_of_mulEquiv f.symm hL⟩

namespace Hyp

variable {L₀ L Q S T : Subgroup G} {z t s : G} {𝕊 : Type} [Group 𝕊] [Finite 𝕊]
  {ε : L ⧸ pPrimeCore 2 L ≃* 𝕊} {Lin : Subgroup (MulAut 𝕊)} (H : Hyp L₀ L Q S T z t s ε Lin)
include H

theorem eight_le_card_R : 8 ≤ Nat.card ↥(S ⊓ L) := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  obtain ⟨a, ha⟩ := H.sec5.R_sylow.isPGroup.exists_card_eq
  have h4 := H.four_lt_card_R
  rw [ha] at h4 ⊢
  have ha3 : 3 ≤ a := by
    by_contra h
    push Not at h
    have : 2 ^ a ≤ 2 ^ 2 := Nat.pow_le_pow_right (by norm_num) (by omega)
    omega
  calc 8 = 2 ^ 3 := by norm_num
    _ ≤ 2 ^ a := Nat.pow_le_pow_right (by norm_num) ha3

end Hyp

end CFSG.ComponentClassification.Sol78.F514
