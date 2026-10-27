module

public import CFSG.LocalAnalysis.EvenSporadicStandard.Induction.Junction.Fs79.ThmU.Step4
public import CFSG.LocalAnalysis.EvenSporadicStandard.Induction.Junction.Fs79.ThmU.Dihedral

public section

namespace CFSG.EvenSporadicStandard.Induction.ThmU

open Subgroup CFSG.EvenSporadicStandard.Solomon78 CFSG.EvenSporadicStandard.Induction
  CFSG.ComponentClassification.AschbacherToolkit
open scoped commutatorElement

variable {G : Type} [Group G]

theorem maximalF_universal [Finite G] (hLB : LayerBalanceAt G) (hglaub : GlaubermanSimplePerfect)
    (hstar : StarHyp G) {A : Subgroup G} (hA : MaximalF A)
    (hrank : 2 ≤ CFSG.Open.pRank 2 A) : UniversalF A := by
  by_contra hnu
  rw [UniversalF] at hnu
  push_neg at hnu
  obtain ⟨b₀, hb₀⟩ := hnu
  obtain ⟨t₀, ht₀⟩ := hA.1
  obtain ⟨t, a, ht, ha, hta⟩ := exists_commuting_good_bad ht₀ hb₀
  obtain ⟨K, hS, hKmax, ⟨e⟩⟩ := exists_swapConfig hLB hglaub hA ht ha hta
  have hKrank : 2 ≤ CFSG.Open.pRank 2 K := by
    rw [← pRank_eq_of_mulEquiv e]
    exact hrank
  have hKnu : ¬ UniversalF K := not_universalF_of_swapConfig hstar hS hKmax hKrank
  have haGood : GoodInv K a := ⟨hS.y_ord, hS.isCompIn⟩
  have haK : a ∉ K := by
    intro haKmem
    exact hKnu (universalF_of_good_mem_center hLB hglaub hKmax haGood haKmem
      (fun k hk => (Subgroup.mem_centralizer_singleton_iff.1 (hS.isCompIn.1 hk)).symm))
  have haKt : a ∉ cj t K := by
    intro haKt
    apply haK
    have hmem : t * a * t ∈ K := (mem_cj_of_mul_self hS.x_mul_self).1 haKt
    have htat : t * a * t = a := by
      calc t * a * t = (a * t) * t := by rw [hta]
        _ = a := by rw [mul_assoc, hS.x_mul_self, mul_one]
    rwa [htat] at hmem
  obtain ⟨w₁, w₂, hw₁, hw₂, ho₁, ho₂, hc12, hne, P, haP, hw₁P, hw₂P, hcard, hcomm, hsq,
    hPK, h3⟩ := exists_swap_rank_three hS hKrank haKt
  have hw₁w₂_mem : w₁ * w₂ ∈ cj t K := (cj t K).mul_mem hw₁ hw₂
  have hw₁w₂P : w₁ * w₂ ∈ P := P.mul_mem hw₁P hw₂P
  have hw₁sq : w₁ * w₁ = 1 := mul_self_eq_one_of_orderOf ho₁
  have hw₂sq : w₂ * w₂ = 1 := mul_self_eq_one_of_orderOf ho₂
  have hw₁w₂_ne : w₁ * w₂ ≠ 1 := by
    intro h
    apply hne
    calc w₁ = w₁ * 1 := (mul_one w₁).symm
      _ = w₁ * (w₂ * w₂) := by rw [hw₂sq]
      _ = (w₁ * w₂) * w₂ := by group
      _ = w₂ := by rw [h, one_mul]
  have hw₁w₂_sq : (w₁ * w₂) * (w₁ * w₂) = 1 := by
    calc (w₁ * w₂) * (w₁ * w₂) = w₁ * (w₂ * (w₁ * w₂)) := by group
      _ = w₁ * ((w₂ * w₁) * w₂) := by group
      _ = w₁ * ((w₁ * w₂) * w₂) := by rw [hc12]
      _ = (w₁ * w₁) * (w₂ * w₂) := by group
      _ = 1 := by rw [hw₁sq, hw₂sq, mul_one]
  have ho₁₂ : orderOf (w₁ * w₂) = 2 :=
    orderOf_eq_prime (by simpa [pow_two] using hw₁w₂_sq) hw₁w₂_ne
  have hKle₁ : K ≤ centralizer ({w₁} : Set G) := by
    intro k hk
    rw [Subgroup.mem_centralizer_singleton_iff]
    exact hS.diagComm k hk w₁ hw₁
  have hKle₂ : K ≤ centralizer ({w₂} : Set G) := by
    intro k hk
    rw [Subgroup.mem_centralizer_singleton_iff]
    exact hS.diagComm k hk w₂ hw₂
  have hKle₁₂ : K ≤ centralizer ({w₁ * w₂} : Set G) := by
    intro k hk
    rw [Subgroup.mem_centralizer_singleton_iff]
    exact hS.diagComm k hk (w₁ * w₂) hw₁w₂_mem
  have bad_of_not_good : ∀ w : G, orderOf w = 2 → K ≤ centralizer ({w} : Set G) →
      ¬ GoodInv K w → BadInv K w := by
    intro w hw hle hng
    by_contra hnb
    exact hng (goodInv_of_not_badInv hw hle hnb)
  by_cases hgood : GoodInv K w₁ ∧ GoodInv K w₂ ∧ GoodInv K (w₁ * w₂)
  · exact hKnu (universalF_of_fourGroup hLB hglaub hKmax hgood.1 hgood.2.1 hgood.2.2 hc12 h3)
  · have hcases : ¬ GoodInv K w₁ ∨ ¬ GoodInv K w₂ ∨ ¬ GoodInv K (w₁ * w₂) := by
      by_contra hc
      push_neg at hc
      exact hgood hc
    rcases hcases with h₁ | h₂ | h₃
    · exact step_four hLB hglaub hstar hKmax hKrank haGood
        (bad_of_not_good w₁ ho₁ hKle₁ h₁) (hcomm a haP w₁ hw₁P) haP hw₁P hcard hcomm hsq hPK
    · exact step_four hLB hglaub hstar hKmax hKrank haGood
        (bad_of_not_good w₂ ho₂ hKle₂ h₂) (hcomm a haP w₂ hw₂P) haP hw₂P hcard hcomm hsq hPK
    · exact step_four hLB hglaub hstar hKmax hKrank haGood
        (bad_of_not_good (w₁ * w₂) ho₁₂ hKle₁₂ h₃) (hcomm a haP (w₁ * w₂) hw₁w₂P)
        haP hw₁w₂P hcard hcomm hsq hPK

end CFSG.EvenSporadicStandard.Induction.ThmU
