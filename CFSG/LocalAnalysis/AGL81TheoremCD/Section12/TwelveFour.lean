module

public import CFSG.LocalAnalysis.AGL81TheoremCD.Section12.Defs
public import CFSG.LocalAnalysis.AGL81TheoremCD.Section12.TwelveFourStmt

public section

namespace CFSG.LocalAnalysis.AGL81TheoremCD.Section12

open CFSG.Open

variable {G : Type} [Group G] [Finite G] {M H : Subgroup G}

theorem three_dvd_card_inf_of_weakBlock {L : Subgroup G} (hL : L ∈ weakBlockSet M H)
    (h3 : 3 ∣ Nat.card (L ⊓ H : Subgroup G)) :
    3 ∣ Nat.card (H ⊓ M : Subgroup G) := by
  refine h3.trans (Subgroup.card_dvd_of_le ?_)
  exact le_inf inf_le_right (inf_le_left.trans hL.le)

theorem twelveFour_of_dprime
    (h1 : ∀ d : ℕ, d ∈ sigmaSet G M → ¬ d ∣ Nat.card (H ⊓ M : Subgroup G))
    (h3 : 3 ∣ Nat.card (H ⊓ M : Subgroup G)) :
    TwelveFour M H := by
  unfold TwelveFour
  intro d hd
  have hdvd : ¬ d ∣ Nat.card (H ⊓ M : Subgroup G) := h1 d hd
  have h3σ : 3 ∉ sigmaSet G M := fun hmem => h1 3 hmem h3
  have hne3 : d ≠ 3 := fun hd3 => h3σ (hd3 ▸ hd)
  have hprime : d.Prime := CFSG.RankThreeCoreUniqueness.Helpers.sigmaA_prime d hd.1
  have hodd : d ≠ 2 := CFSG.RankThreeCoreUniqueness.Helpers.sigmaA_odd d hd.1
  have h5 : 5 ≤ d := hprime.five_le_of_ne_two_of_ne_three hodd hne3
  exact ⟨hdvd, by omega, h3σ⟩

theorem twelveFour_of_weakBlock
    (h1 : ∀ d : ℕ, d ∈ sigmaSet G M → ¬ d ∣ Nat.card (H ⊓ M : Subgroup G))
    (hL : ∃ L : Subgroup G, L ∈ weakBlockSet M H ∧ 3 ∣ Nat.card (L ⊓ H : Subgroup G)) :
    TwelveFour M H := by
  obtain ⟨L, hL, h3⟩ := hL
  exact twelveFour_of_dprime h1 (three_dvd_card_inf_of_weakBlock hL h3)

end CFSG.LocalAnalysis.AGL81TheoremCD.Section12
