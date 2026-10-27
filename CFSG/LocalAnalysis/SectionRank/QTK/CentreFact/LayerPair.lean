module

public import CFSG.LocalAnalysis.SectionRank.QTK.CentreFact.LayerDefs
public import CFSG.LocalAnalysis.SectionRank.QTK.CentreFact.LayerPairReal
public import CFSG.LocalAnalysis.SectionRank.QTK.CentreFact.LayerPairU3
import CFSG.LieType.Steinberg.CentralExt.GriessUnitaryOdd
public import CFSG.Blueprint.MultiplierDefs
public import CFSG.LocalAnalysis.ComponentInitial.LinearUnitaryField

public section

namespace CFSG.SectionRank.QTK.CentreFact.LayerPair

open Subgroup CFSG.SectionRank.QTK CFSG.SectionRank.QTK.CoverB CFSG.RankThree.PerfectCover
  CFSG.Assembly.LowTwoRank CFSG.Blueprint.Multiplier

private theorem card_generic_exceptional' (t : StatedLieTag) (n p f : ℕ) :
    Nat.card (generic t n p f × exceptional t n p f) =
      ((genericOrders t n p f).1 * (genericOrders t n p f).2) *
        ((exceptionalOrders t n p f).1 * (exceptionalOrders t n p f).2) := by
  simp only [generic, exceptional, Nat.card_prod,
    Nat.card_congr (Multiplicative.toAdd : Multiplicative (ZMod _) ≃ _), Nat.card_zmod]

theorem card_hopfMultiplier_psu_three
    {S : Type} [Group S] {p f : ℕ}
    (h : StatedClassicalModel S .PSU 3 p f) :
    Nat.card (hopfMultiplier S) = Nat.gcd 3 (p ^ f + 1) := by
  obtain ⟨-, ⟨e⟩⟩ := CFSG.LieType.Steinberg.CentralExt.GriessClassical.psu_odd_row h (by decide)
  rw [← Nat.card_congr (hopfMultiplierEquivGriess S).toEquiv, Nat.card_congr e.toEquiv,
    card_generic_exceptional',
    CFSG.LieType.Steinberg.CentralExt.GriessClassical.exceptionalOrders_PSU_odd (by decide)]
  have h1 : genericOrders .PSU 3 p f = (Nat.gcd 3 (p ^ f + 1), 1) := by simp [genericOrders]
  rw [h1]
  simp

theorem card_center_dvd_gcd_psu_three
    {L : Type} [Group L] (hL : CFSG.IsQuasisimple L) {p f : ℕ}
    (h : StatedClassicalModel (L ⧸ center L) .PSU 3 p f) :
    Nat.card (center L) ∣ Nat.gcd 3 (p ^ f + 1) := by
  have : Group.IsPerfect L := hL.1
  rw [← card_hopfMultiplier_psu_three h]
  exact card_center_dvd_card_hopfMultiplier_quotient

theorem false_of_components_psu_three_two_pow
    {H : Type} [Group H] [Finite H]
    (he : CFSG.Open.evenRank H ≤ 2) {L₁ L₂ : Subgroup H}
    (hc : ∀ a ∈ L₁, ∀ b ∈ L₂, Commute a b) (φ : ↥L₁ ≃* ↥L₂) (hq : CFSG.IsQuasisimple ↥L₁)
    {f : ℕ} (hm : StatedClassicalModel (↥L₁ ⧸ center ↥L₁) .PSU 3 2 f)
    (h3 : 3 ∣ Nat.card (center ↥L₁)) : False := by
  have hf2 : 2 ≤ f := by
    obtain ⟨⟨-, hf1, -, hne⟩, -⟩ := id hm
    by_contra hlt
    obtain rfl : f = 1 := by omega
    exact hne (by simp)
  have hZ : Nat.card (center ↥L₁) ∣ 3 :=
    (card_center_dvd_gcd_psu_three hq hm).trans (Nat.gcd_dvd_left _ _)
  by_cases hf3 : f = 3
  · subst hf3
    have : Group.IsPerfect ↥L₁ := hq.1
    refine false_of_components_psu_three_eight_of_multiplier he hc φ hq hm ?_ h3
    rw [card_hopfMultiplier_psu_three hm]
    exact Nat.gcd_dvd_left _ _
  · refine false_of_components_psu_three_even he hc φ hf2 hf3 hm fun r hr _ hrZ => ?_
    exact (Nat.prime_dvd_prime_iff_eq hr Nat.prime_three).1 (hrZ.trans hZ)

private theorem components_commute {H : Type} [Group H] [Finite H] {L₁ L₂ : Subgroup H}
    (h₁ : CFSG.IsComponent L₁) (h₂ : CFSG.IsComponent L₂) (hne : L₁ ≠ L₂) :
    ∀ a ∈ L₁, ∀ b ∈ L₂, Commute a b := fun a ha b hb =>
  commutatorElement_eq_one_iff_commute.1 (Subgroup.mem_bot.1
    (((CFSG.LocalCores.distinct_components_commute h₁ h₂).resolve_left hne) ▸
      Subgroup.commutator_mem_commutator ha hb))

end CFSG.SectionRank.QTK.CentreFact.LayerPair

namespace CFSG.SectionRank.QTK.CentreFact

open Subgroup CFSG.SectionRank.QTK.CoverB LayerPair

theorem layerPairFact_holds :
    LayerPairFact := by
  intro H _ _ he _ L₁ L₂ h₁ h₂ hne ⟨φ⟩ hS h3
  exfalso
  have hc := components_commute h₁ h₂ hne
  have hq : CFSG.IsQuasisimple ↥L₁ := h₁.1
  rcases hS with h6 | h7 | h22 | ⟨p, f, hp, hf, hcase⟩
  · obtain ⟨e⟩ : Nonempty _ := h6
    exact false_of_realLocalElement_three he hc φ h3
      (RealLocalElement.of_mulEquiv e (realLocalElement_alternating_six_seven (Or.inl rfl)))
  · obtain ⟨e⟩ : Nonempty _ := h7
    exact false_of_realLocalElement_three he hc φ h3
      (RealLocalElement.of_mulEquiv e (realLocalElement_alternating_six_seven (Or.inr rfl)))
  · obtain ⟨e⟩ : Nonempty _ := h22
    exact false_of_realLocalElement_three he hc φ h3
      (RealLocalElement.of_mulEquiv e (realLocalElement_mathieu (s := .M22) (Or.inr (Or.inl rfl))))
  · rcases hcase with ⟨hm, -⟩ | ⟨hm, -⟩
    · obtain ⟨-, K, _, _, -, ⟨e⟩⟩ := id hm
      exact false_of_realLocalElement_three he hc φ h3
        (RealLocalElement.of_mulEquiv e realLocalElement_psl_three)
    · by_cases hp2 : p = 2
      · subst hp2
        exact false_of_components_psu_three_two_pow he hc φ hq hm h3
      · obtain ⟨-, K, _, _, hK, ⟨e⟩⟩ := id hm
        have : Fact p.Prime := ⟨hp⟩
        have : CharP K p :=
          (CFSG.LocalAnalysis.ComponentInitial.UnitaryFieldData.charP
            (⟨hp, hf, by rw [hK, ← pow_mul, mul_comm]⟩ :
              CFSG.LocalAnalysis.ComponentInitial.UnitaryFieldData p f K))
        exact false_of_realLocalElement_three he hc φ h3
          (RealLocalElement.of_mulEquiv e (realLocalElement_psu_three_odd (f := f) hp2))

end CFSG.SectionRank.QTK.CentreFact
