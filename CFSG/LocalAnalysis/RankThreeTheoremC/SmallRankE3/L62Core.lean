module

public import CFSG.LocalAnalysis.RankThreeTheoremC.SmallRankE3.L62Fixed
public import CFSG.LocalAnalysis.RankThreeTheoremC.SmallRankE3.L62Single
public import CFSG.LocalAnalysis.RankThreeTheoremC.SmallRankE3.L62ToBar
public import CFSG.LocalAnalysis.RankThreeTheoremC.KFactProofs.Stroth.Bal3Reduce

public section

namespace CFSG.LocalAnalysis.RankThreeTheoremC.SmallRankE3

open CFSG.Open CFSG.RankThreeCoreUniqueness.Helpers Subgroup
open CFSG.LocalAnalysis.RankThreeTheoremC.KFactProofs
open CFSG.LocalAnalysis.RankThreeTheoremC.KFactProofs.K2 (Bar barMk)

@[expose] def KFactThreeComponentsQRank : Prop :=
  ∀ (X : Type) [Group X] [Finite X], CFSG.AGLEmbedding.CatalogSimpleSections X →
    ∀ (g : Bar X) (L : Subgroup (Bar X)), IsComponentOf L ⊤ → (∃ n : ℕ, g ^ 3 ^ n = 1) →
      g ∉ normalizer (L : Set (Bar X)) → CFSG.Open.pRank 3 (⊤ : Subgroup (Bar X)) ≤ 3 →
      ∃ q : ℕ, q.Prime ∧ 5 ≤ q ∧ 3 ≤ CFSG.Open.pRank q (⊤ : Subgroup X)

theorem l62_false_of_moved (hQ : KFactThreeComponentsQRank) {X : Type} [Group X] [Finite X]
    {S : Sylow 3 X} {x z : X} (h : L62Data X S x z) {S' : Sylow 3 (Bar X)} {x' z' : Bar X}
    (hB : L62Bar (Bar X) S' x' z') {L : Subgroup (Bar X)} (hL : IsComponentOf L ⊤)
    (hmoved : ¬ (S' : Subgroup (Bar X)) ≤ normalizer (L : Set (Bar X))) : False := by
  obtain ⟨g, hgS, hgL⟩ := SetLike.not_le_iff_exists.mp hmoved
  have hg3 : ∃ n : ℕ, g ^ 3 ^ n = 1 := by
    obtain ⟨n, hn⟩ := S'.isPGroup' (⟨g, hgS⟩ : (S' : Subgroup (Bar X)))
    exact ⟨n, congrArg Subtype.val hn⟩
  obtain ⟨q, hq, hq5, hrk⟩ := hQ X h.catalog g L hL hg3 hgL hB.rank_top
  have := h.qrank q hq hq5
  omega

theorem l62_core (hT : T29.GL83I291Three) (hNC : T29.NoncyclicCentreRank)
    (hQ : KFactThreeComponentsQRank) {X : Type} [Group X] [Finite X] {S : Sylow 3 X} {x z : X}
    (h : L62Data X S x z) :
    HasPrimeConstraint (G := X) 3 ∨
      (IsCyclic ↥(CFSG.pCore 3 (Bar X)) ∧ 9 ≤ Nat.card ↥(CFSG.pCore 3 (Bar X))) := by
  by_contra hcon
  push Not at hcon
  obtain ⟨hnc, hnotδ⟩ := hcon
  obtain ⟨S', x', z', hB⟩ := l62Data_toBar h
  obtain ⟨L, hL⟩ :=
    Stroth.Bal3.exists_isComponentOf_of_not_hasPrimeConstraint Nat.prime_three hnc
  by_cases hinv : ∀ K : Subgroup (Bar X), IsComponentOf K ⊤ →
      (S' : Subgroup (Bar X)) ≤ normalizer (K : Set (Bar X))
  · have huniq : ∀ K : Subgroup (Bar X), IsComponentOf K ⊤ → K = L := fun K hK => by
      by_contra hne
      exact l62_false_of_two_fixed hB hNC hK hL hne (hinv K hK) (hinv L hL)
    obtain ⟨hcyc, h9⟩ := single_component_delta hT (S := S') (x := x') hB.rank.ge
      hB.x_mem hB.x_ne hB.x_pow hB.cent hB.catalog hB.core hL huniq hB.no_normal_three
    exact absurd h9 (not_le.mpr (hnotδ hcyc))
  · push Not at hinv
    obtain ⟨K, hK, hmoved⟩ := hinv
    exact l62_false_of_moved hQ h hB hK hmoved

end CFSG.LocalAnalysis.RankThreeTheoremC.SmallRankE3
