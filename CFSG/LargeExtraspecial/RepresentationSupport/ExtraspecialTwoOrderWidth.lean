module

public import CFSG.LargeExtraspecial.RepresentationSupport.ExtraspecialTwoCommutatorForm
public import CFSG.LinearAlgebra.CoprimeActions.AlternatingFormEvenDimension

public section

namespace CFSG.LargeExtraspecial.RepresentationSupport.ExtraspecialTwoOrderWidth

open CFSG.LargeExtraspecial.RepresentationSupport.ExtraspecialTwoQuotientLinearAction

open CFSG.LargeExtraspecial.RepresentationSupport.ExtraspecialTwoCommutatorForm

theorem exists_width (E : Type*) [Group E] [Finite E]
    (hE : CFSG.IsExtraspecialPGroup 2 E) :
    ∃ w : ℕ, 0 < w ∧ Nat.card E = 2 ^ (2 * w + 1) := by
  haveI : Fact (CFSG.IsExtraspecialPGroup 2 E) := ⟨hE⟩
  haveI : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hc : Nat.card (Subgroup.center E) = 2 := hE.2.2.2
  have hM : Nat.card (Multiplicative (ZMod 2)) = 2 := by simp [Nat.card_eq_fintype_card]
  let ζ : Subgroup.center E ≃* Multiplicative (ZMod 2) := mulEquivOfPrimeCardEq hc hM
  haveI : Finite (QSpace E) := inferInstanceAs (Finite (Additive (E ⧸ Subgroup.center E)))
  haveI : FiniteDimensional (ZMod 2) (QSpace E) := Module.Finite.of_finite
  obtain ⟨n, hn⟩ := CFSG.LinearAlgebra.CoprimeActions.AlternatingFormEvenDimension.exists_half_finrank (form ζ)
    (alternating ζ) (nondegenerate ζ)
  have h1 := Subgroup.card_eq_card_quotient_mul_card_subgroup (Subgroup.center E)
  have h2 : Nat.card (QSpace E) = 2 ^ (2 * n) := by
    have h4 := Module.natCard_eq_pow_finrank (K := ZMod 2) (V := QSpace E)
    rw [hn, Nat.card_zmod] at h4
    exact h4
  have h3 : Nat.card (QSpace E) = Nat.card (E ⧸ Subgroup.center E) :=
    Nat.card_congr Additive.toMul
  have hcard : Nat.card E = 2 ^ (2 * n + 1) := by
    rw [h1, hc, ← h3, h2, pow_succ]
  refine ⟨n, ?_, hcard⟩
  rcases Nat.eq_zero_or_pos n with rfl | hpos
  · exfalso
    have hE2 : Nat.card (Subgroup.center E) = Nat.card E := by rw [hcard, hc]; rfl
    have htop : Subgroup.center E = ⊤ := Subgroup.eq_top_of_card_eq _ hE2
    have hb : commutator E = ⊥ := (commutator_eq_bot_iff_center_eq_top E).2 htop
    have h5 : Subgroup.center E = ⊥ := by rw [← hE.2.1]; exact hb
    rw [h5] at hc
    simp at hc
  · exact hpos

end CFSG.LargeExtraspecial.RepresentationSupport.ExtraspecialTwoOrderWidth
