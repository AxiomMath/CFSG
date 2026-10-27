module

public import CFSG.LocalAnalysis.AGLEmbedding.LeviBlockDefs
import CFSG.LocalAnalysis.AGLEmbedding.LeviBlockGenFive

public section

namespace CFSG.AGLEmbedding

theorem fivesAt_of_levi {Y : Type} [Group Y] [Finite Y] {L P : Subgroup Y} (hPL : P ≤ L)
    {K : Type} [Group K] (ρ : K →* ↥L) (hρ : Function.Surjective ρ) {ι : Type} [Fintype ι]
    [DecidableEq ι] {G : ι → Type} [∀ j, Group (G j)] [∀ j, Finite (G j)]
    {S : ∀ j, Subgroup (G j)} (β : ↥((P.subgroupOf L).comap ρ) →* ∀ j, G j)
    (hker : IsPGroup 2 β.ker) (hpi : Subgroup.pi Set.univ S ≤ β.range)
    (hcomm : ⁅β.range, β.range⁆ ≤ Subgroup.pi Set.univ S)
    (hS : ∀ j, CFSG.Open.IsQuasisimple (S j) ∨ Group.IsSolvable (S j))
    (hcl : ∀ j, CFSG.Open.IsQuasisimple (S j) →
      Nat.card (↥(S j) ⧸ Subgroup.center ↥(S j)) = 60 → Nat.card (S j) = 60)
    (h2 : Nat.card {j // CFSG.Open.IsQuasisimple (S j) ∧
      Nat.card (↥(S j) ⧸ Subgroup.center ↥(S j)) = 60} ≤ 2) : FivesAt P := by
  intro O J _ hPO _ hsec hJ hJc
  have h3 := three_le_card_fiveBlocks_of_cover hPL ρ hρ β hker hpi hcomm hS hcl hPO hsec hJ hJc
  omega

end CFSG.AGLEmbedding
