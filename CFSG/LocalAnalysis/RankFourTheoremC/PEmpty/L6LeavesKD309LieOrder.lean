module

public import CFSG.LocalAnalysis.RankFourTheoremC.PEmpty.L6LeavesKD309LieWr
public import CFSG.LocalAnalysis.RankFourTheoremC.PEmpty.L6LeavesKD309LieWrap

public section

namespace CFSG.LocalAnalysis.RankFourTheoremC.PEmpty

open CFSG.Open CFSG.RankThreeCoreUniqueness.Helpers Subgroup
open CFSG.LocalAnalysis.RankFourTheoremC.PEmpty.KD309
open CFSG.LocalAnalysis.RankFourTheoremC.PEmpty.KD309L

@[expose] def KD309OrderModel : Prop :=
  ∀ (Y : Type) [Group Y] [Finite Y] (P : Sylow 5 Y) (x z : Y), Plane63 5 Y P x z →
    ∀ L : Subgroup (Y ⧸ primeComplementCore (G := Y) 5), IsComponentOf L ⊤ →
      (∀ K : Subgroup (Y ⧸ primeComplementCore (G := Y) 5), IsComponentOf K ⊤ → K = L) →
      I291P65.Is29a ↥L → Nat.card (P : Subgroup Y) ≤ 5 ^ 6 →
      Nat.card (P : Subgroup Y) ≤ 5 ^ 5 ∨
        ∃ S : Subgroup Y, S ≤ (P : Subgroup Y) ∧ Nat.card (P : Subgroup Y) = 5 ^ 6 ∧
          Nat.card S = 5 ^ 5 ∧ (∀ s ∈ S, s ^ 5 = 1) ∧ (∃ a ∈ S, ∃ b ∈ S, a * b ≠ b * a) ∧
          x ∉ S

theorem kd309LieOrderW_of_model (hM : KD309OrderModel) : KD309LieOrderW := by
  intro Y _ _ P x z hpl L hL hLu h29 hψ
  obtain ⟨ψ, hψinj⟩ := hψ
  have hcard : Nat.card (P : Subgroup Y) ≤ 5 ^ 6 := by
    rw [← card_Wr]
    exact Nat.card_le_card_of_injective ψ hψinj
  rcases hM Y P x z hpl L hL hLu h29 hcard with h | ⟨S, hSP, hP6, hS5, hSexp, hSnab, hxS⟩
  · exact h
  · exfalso
    obtain ⟨hxP, -, hx5, -, -, -⟩ := I291P65.plane_facts hpl.prime hpl.plane
    have h5 := wr_exclusion ψ hψinj hP6 hSP hS5 hSexp hSnab hxP hxS hx5
    have h2 := hpl.rank_centralizer
    omega

end CFSG.LocalAnalysis.RankFourTheoremC.PEmpty
