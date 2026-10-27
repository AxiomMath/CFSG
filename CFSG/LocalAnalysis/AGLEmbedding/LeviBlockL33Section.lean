module

public import CFSG.LocalAnalysis.AGLEmbedding.LeviBlockL33Defs
import CFSG.LocalAnalysis.AGLEmbedding.LeviBlockSection
import CFSG.LocalAnalysis.AGLEmbedding.LeviBlockL33Orders
public import CFSG.LocalAnalysis.AGLEmbedding.LeviBlockDefs

public section

namespace CFSG.AGLEmbedding

open CFSG.Open

theorem noL33U35L37HeAt_of_levi {Y : Type} [Group Y] [Finite Y] {L P : Subgroup Y}
    (hPL : P ≤ L)
    (h : ∃ (K : Type) (_ : Group K) (_ : Finite K) (ρ : K →* ↥L) (𝒯 : Set ℕ),
      Function.Surjective ρ ∧ HasLeviBlocks ↥((P.subgroupOf L).comap ρ) 𝒯 ∧
        ∀ n ∈ 𝒯, ¬ IsL33U35L37HeOrder n) :
    NoL33U35L37HeAt P := by
  intro O W hOP hPO hO3 hWP hPWO _ U _ _ _ ψ hψ hU
  exfalso
  obtain ⟨K, _, _, ρ, 𝒯, hρ, hQ, h𝒯⟩ := h
  have h3U : 3 ∣ Nat.card U := LeviBlock.three_dvd_of_isL33U35L37HeOrder hU
  have hnc : ∃ a b : U, a * b ≠ b * a := by
    refine ThreeFives.exists_noncomm_of_simple inferInstance ?_
    rcases hU with h | h | h | h <;> rw [h] <;> norm_num
  have := card_mem_of_section hPL ρ hρ hQ hOP hPO hO3 hWP hPWO hnc h3U ψ hψ
  exact h𝒯 _ this hU

end CFSG.AGLEmbedding
