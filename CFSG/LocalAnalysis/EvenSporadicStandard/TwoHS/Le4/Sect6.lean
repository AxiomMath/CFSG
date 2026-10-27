module

public import CFSG.LocalAnalysis.EvenSporadicStandard.TwoHS.Le4.Assembly
public import CFSG.LocalAnalysis.EvenSporadicStandard.TwoHS.Le4.Thompson
public import CFSG.LocalAnalysis.EvenSporadicStandard.TwoHS.Defs

public section

namespace CFSG.EvenSporadicStandard.TwoHS

open Subgroup CFSG.Blueprint CFSG.Blueprint.NativeSporadic

@[expose] def SolomonTwoHSNotFour : Prop :=
  ∀ (G : Type) [Group G] [Finite G] (L : Subgroup G), CFSG.EvenSporadicStandard.StdHyp G L →
    Nat.card (center L) = 2 → IsSporadic (L ⧸ center L) .HS →
      ∀ S : Sylow 2 (centralizer (L : Set G)), Nat.card S ≠ 4

@[expose] def SolomonSection6Fusion : Prop :=
  ∀ (G : Type) [Group G] [Finite G] (L : Subgroup G), CFSG.EvenSporadicStandard.StdHyp G L →
    Nat.card (center L) = 2 → IsSporadic (L ⧸ center L) .HS →
      ∀ S : Sylow 2 (centralizer (L : Set G)), Nat.card S = 4 →
        ∃ f : centralizer (L : Set G), f ∈ S ∧ orderOf f = 4 ∧
          ∃ T U : Subgroup G, IsPGroup 2 T ∧ ¬ 2 ∣ T.index ∧ (f : G) ∈ T ∧ U ≤ T ∧
            U.relIndex T = 2 ∧ (f : G) ∉ U ∧ (∀ g : G, g⁻¹ * (f : G) * g ∉ U) ∧
            ∀ g : G, g⁻¹ * (f : G) ^ 2 * g ∈ T → g⁻¹ * (f : G) ^ 2 * g ∈ U

theorem SolomonSection6Fusion.notFour (h6 : SolomonSection6Fusion) : SolomonTwoHSNotFour := by
  intro G _ _ L h hZ hq S hS4
  have := h.simple
  obtain ⟨f, -, hf4, T, U, hT, hTidx, hfT, hUT, hUidx, hfU, hconj, ht⟩ := h6 G L h hZ hq S hS4
  have hf4' : orderOf (f : G) = 4 := by rw [Subgroup.orderOf_coe]; exact hf4
  have hf44 : (f : G) ^ 4 = 1 := by rw [← hf4']; exact pow_orderOf_eq_one _
  refine false_of_thompson_pow h.nonabelian hT hTidx hUT hUidx hfT hfU ?_ hconj
  intro g k hg
  rcases Nat.even_or_odd k with ⟨m, hm⟩ | ⟨m, hm⟩
  · have h1 : (f : G) ^ (2 * k) = 1 := by
      rw [hm, show 2 * (m + m) = 4 * m by ring, pow_mul, hf44, one_pow]
    rw [h1, mul_one, inv_mul_cancel]
    exact U.one_mem
  · have h1 : (f : G) ^ (2 * k) = (f : G) ^ 2 := by
      rw [hm, show 2 * (2 * m + 1) = 4 * m + 2 by ring, pow_add, pow_mul, hf44, one_pow, one_mul]
    rw [h1] at hg ⊢
    exact ht g hg

theorem card_sylow_eq_two_of_dvd_four_of_ne_four {G : Type} [Group G] [Finite G] {L : Subgroup G}
    (h : CFSG.EvenSporadicStandard.StdHyp G L) (S : Sylow 2 (centralizer (L : Set G)))
    (h4 : Nat.card S ∣ 4) (hne : Nat.card S ≠ 4) : Nat.card S = 2 := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have heven : 2 ∣ Nat.card S := S.dvd_card_of_dvd_card (even_iff_two_dvd.mp h.standard.2.1)
  have hle : Nat.card S ≤ 4 := Nat.le_of_dvd (by norm_num) h4
  have hpos : 0 < Nat.card S := Nat.card_pos
  interval_cases hc : Nat.card S <;> simp_all

theorem solomonTwoHSCentralizer_of_notFour
    (h : SolomonTwoHSNotFour) : SolomonTwoHSCentralizer := fun G _ _ L hL hZ hq S =>
  card_sylow_eq_two_of_dvd_four_of_ne_four hL S (hL.card_sylow_dvd_four_twoHS hZ hq S)
    (h G L hL hZ hq S)

end CFSG.EvenSporadicStandard.TwoHS
