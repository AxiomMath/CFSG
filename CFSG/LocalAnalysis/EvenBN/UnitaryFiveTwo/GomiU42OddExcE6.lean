module

public import CFSG.LocalAnalysis.EvenBN.UnitaryFiveTwo.GomiU42OddExc
public import CFSG.LocalAnalysis.EvenBN.UnitaryFiveTwo.GomiU42OddExcE6GF
public import CFSG.LocalAnalysis.EvenBN.UnitaryFiveTwo.GomiU42OddExcE6Gr
public import CFSG.LocalAnalysis.EvenBN.UnitaryFiveTwo.GomiU42OddExcComp
public import CFSG.LocalAnalysis.EvenBN.UnitaryFiveTwo.GomiU42OddExcField
public import CFSG.LocalAnalysis.EvenBN.UnitaryFiveTwo.GomiU42OddExcInner

public section

namespace CFSG.LocalAnalysis.EvenBN.UnitaryFiveTwo

open Subgroup CFSG.Blueprint CFSG.Blueprint.Chevalley CFSG.LieType.Chevalley
  CFSG.Assembly.LowTwoRank CFSG.LocalAnalysis.ComponentInitial.FourGroupChevalley

theorem gomi_E6_aut_false
    {p f : ℕ} (hp : p.Prime) (hp2 : p ≠ 2) (hf : 1 ≤ f) {K : Type} [Field K] [Finite K]
    (hK : Nat.card K = p ^ f) (β : MulAut (adjointGroup Tag.E6 K)) (hβ1 : β ≠ 1) (hβ2 : β ^ 2 = 1)
    (hβd : Nat.card ↥(β.toMonoidHom.eqLocus (MonoidHom.id (adjointGroup Tag.E6 K))) ∣ 51840)
    (L : Subgroup ↥(β.toMonoidHom.eqLocus (MonoidHom.id (adjointGroup Tag.E6 K))))
    (hL : CFSG.IsComponent L) (hLd : Nat.card L ∣ 51840) : False := by
  classical
  have hodd : Odd (Nat.card K) := by rw [hK]; exact (hp.odd_of_ne_two hp2).pow
  obtain ⟨-, -, hexist⟩ := ordinary_E_exact_automorphism_normal_form Tag.E6 (Or.inl rfl) K
  obtain ⟨g, a', σ, ε, hexpr⟩ := hexist β
  obtain ⟨-, -, -, -, hsq, hfacts⟩ :=
    ordinary_E_field_graph_quotient_and_involutions Tag.E6 (Or.inl rfl) K
  have hσ2 : σ ^ 2 = 1 := hsq β g a' σ ε hexpr hβ2
  have hε : (ε : ℕ) = 0 ∨ (ε : ℕ) = 1 := by
    have h := ε.2
    change (ε : ℕ) < 2 at h
    omega
  have hQ : exactQ Tag.E6 K ε = (diagramMap TwistTag.E6 K : ModGL Tag.E6 K) ^ (ε : ℕ) := rfl
  have hQ0 : (ε : ℕ) = 0 → exactQ Tag.E6 K ε = 1 := fun h0 => by
    rw [hQ, h0, pow_zero]
    rfl
  have hQ1 : (ε : ℕ) = 1 → exactQ Tag.E6 K ε = (diagramMap TwistTag.E6 K : ModGL Tag.E6 K) :=
    fun h0 => by rw [hQ, h0, pow_one]
  by_cases hσ : σ = 1
  · subst hσ
    have h1 : ∀ h : adjointGroup Tag.E6 K, Units.map (entrywiseHom (1 : K ≃+* K).toRingHom)
        (h : ModGL Tag.E6 K) = h := fun h => Units.ext (entrywise_id _)
    rcases hε with h0 | h0
    · refine gomi_innerDiag_false (Or.inr (Or.inl rfl)) hodd (g := g) (a := a') (fun h => ?_)
        hβ2 hβ1 hβd
      rw [hexpr h, hQ0 h0, h1 h, inv_one, mul_one, mul_one]
    · refine gomi_E6_graph_false hp hp2 hK (g := g) (a := a') (fun h => ?_) hβ2 L hL hLd
      have h2 := hexpr h
      rw [hQ1 h0, h1 h] at h2
      exact h2
  · obtain ⟨hfe, hσc, -⟩ := hfacts p f hp hf hK σ hσ2 hσ
    obtain ⟨e₀, rfl⟩ : ∃ e₀, f = 2 * e₀ := ⟨f / 2, (Nat.two_mul_div_two_of_even hfe).symm⟩
    have he₀ : 1 ≤ e₀ := by omega
    have hF' : Nat.card K = (p ^ e₀) ^ 2 := by rw [hK, ← pow_mul, mul_comm]
    have hσe : ∀ c, σ c = c ^ (p ^ e₀) := fun c => by
      rw [hσc, Nat.mul_div_cancel_left e₀ two_pos]
    rcases hε with h0 | h0
    · refine gomi_quadField_false (Or.inr (Or.inl rfl)) hp hp2 he₀ hF' σ hσe (g := g) (a := a')
        (fun h => ?_) hβ2 hβd
      rw [hexpr h, hQ0 h0, inv_one, mul_one, mul_one]
    · refine gomi_E6_graphField_false hp hp2 he₀ hF' σ hσe (g := g) (a := a')
        (fun h => ?_) hβ2 hβd
      have h2 := hexpr h
      rw [hQ1 h0] at h2
      exact h2

variable {X : Type} [Group X] [Finite X] {J D E : Subgroup X} {a : X}

theorem GomiU42Data.false_of_oddLie_E6
    (h : GomiU42Data X J D E a) {p f : ℕ} (hp : p.Prime) (hp2 : p ≠ 2)
    (hD : ChevalleyExceptionalModel ↥D .E6 p f) : False := by
  obtain ⟨⟨-, hf, -⟩, K, _, _, hK, ⟨e⟩⟩ := hD
  let ψ : ↥D ≃* adjointGroup Tag.E6 K :=
    e.trans ((QuotientGroup.quotientMulEquivOfEq (center_adjointGroup_eq_bot_field Tag.E6 K)).trans
      QuotientGroup.quotientBot)
  obtain ⟨α, hα2, hα1, hdvd, L, hL, hLcard⟩ := h.exists_involution_aut_component
  obtain ⟨L', hL', hL'card⟩ := gomi_exists_component_congr ψ α L hL
  refine gomi_E6_aut_false hp hp2 hf hK (MulAut.congr ψ α)
    (fun h1 => hα1 ((MulAut.congr ψ).injective (h1.trans (map_one _).symm)))
    (by rw [← map_pow, hα2, map_one]) (by rw [gomi_card_eqLocus_congr ψ α]; exact hdvd) L' hL' ?_
  rw [hL'card, hLcard]
  norm_num

end CFSG.LocalAnalysis.EvenBN.UnitaryFiveTwo
