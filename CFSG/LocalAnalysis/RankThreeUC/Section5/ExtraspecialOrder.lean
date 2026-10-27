module

public import CFSG.LocalAnalysis.RankThreeUC.Section5.ExtraspecialQuotientForm
public import CFSG.LinearAlgebra.CoprimeActions.AlternatingFormEvenDimension

public section

namespace CFSG.LocalAnalysis.RankThreeUC

namespace Section5

namespace ExtraspecialOrder

open Quotient

theorem exists_width {G : Type} [Group G] [Finite G] (P : Subgroup G) (p : ℕ) [hp : Fact p.Prime]
    (hexp : Monoid.exponent ↥P = p) (hclass : ⁅⁅P, P⁆, P⁆ = ⊥)
    (hext : CFSG.IsExtraspecialPGroup p ↥P) :
    ∃ n : ℕ, Nat.card ↥P = p ^ (1 + 2 * n) := by
  haveI : Fact (⁅⁅P, P⁆, P⁆ = ⊥) := ⟨hclass⟩
  haveI : Fact (Monoid.exponent ↥P = p) := ⟨hexp⟩
  have hZ : Nat.card (Subgroup.center ↥P) = p := hext.2.2.2
  have hZ' : Nat.card (Multiplicative (ZMod p)) = p := by
    simp [Nat.card_eq_fintype_card]
  let ζ : Subgroup.center ↥P ≃* Multiplicative (ZMod p) := mulEquivOfPrimeCardEq hZ hZ'
  have hnd : (ExtraspecialQuotientForm.form ζ).Nondegenerate := by
    refine ⟨fun a h => ExtraspecialQuotientForm.form_nondegenerate ζ a h, fun b h => ?_⟩
    apply ExtraspecialQuotientForm.form_nondegenerate ζ b
    intro a
    have h1 := h a
    have h2 := ExtraspecialQuotientForm.form_alt ζ (a + b)
    simp only [map_add, LinearMap.add_apply, ExtraspecialQuotientForm.form_alt, h1] at h2
    simpa using h2
  have hfin : Finite (Additive (Pbar P)) := inferInstanceAs (Finite (↥P ⧸ Subgroup.center ↥P))
  haveI : Module.Finite (ZMod p) (Additive (Pbar P)) := Module.Finite.of_finite
  obtain ⟨n, hn⟩ := CFSG.LinearAlgebra.CoprimeActions.AlternatingFormEvenDimension.exists_half_finrank
    (ExtraspecialQuotientForm.form ζ) (fun a => ExtraspecialQuotientForm.form_alt ζ a) hnd
  have hcard : Nat.card (Additive (Pbar P)) = p ^ (2 * n) := by
    rw [Module.natCard_eq_pow_finrank (K := ZMod p), hn, Nat.card_zmod]
  refine ⟨n, ?_⟩
  have hmul := Subgroup.card_eq_card_quotient_mul_card_subgroup (Subgroup.center ↥P)
  have hq : Nat.card (Pbar P) = p ^ (2 * n) := by
    rw [← hcard]; exact (Nat.card_congr Additive.ofMul).symm
  rw [hmul, hq, hZ]; ring

end ExtraspecialOrder
end Section5
end CFSG.LocalAnalysis.RankThreeUC
