module

public import CFSG.LocalAnalysis.RankThreeTheoremC.KFactProofs.Stroth.Bal3Three
public import CFSG.LocalAnalysis.RankThreeTheoremC.KFactProofs.Stroth.Bal3Five

public section

namespace CFSG.LocalAnalysis.RankThreeTheoremC.KFactProofs.Stroth.Bal3

open CFSG CFSG.Open CFSG.RankThreeCoreUniqueness.Helpers CFSG.AGLEmbedding Subgroup

@[expose] def Bal3ThreeSingleRed : Prop :=
  ∀ (X : Type) [Group X] [Finite X], CFSG.AGLEmbedding.CatalogSimpleSections X →
    ∀ (P : Sylow 3 X) (z : X) (D : Subgroup X), RedConfig 3 P z D → z ∈ CFSG.pCore 3 X →
      ∀ K : Subgroup X, IsComponentOf K ⊤ → (∀ L : Subgroup X, IsComponentOf L ⊤ → L = K) →
        False

theorem kFactLemma212_three_of_red (h3 : Bal3ThreeSingleRed) :
    ∀ (H : Type) [Group H] [Finite H], CFSG.AGLEmbedding.CatalogSimpleSections H →
      ∀ (P : Sylow 3 H) (z : H) (D : Subgroup H), Lemma212Config 3 P z D →
        HasPrimeConstraint (G := H) 3 ∨
          CFSG.pCore 3 (H ⧸ primeComplementCore (G := H) 3) = ⊥ := by
  intro H _ _ hcat P z D hconf
  by_contra hno
  push Not at hno
  obtain ⟨hcon, hQ⟩ := hno
  haveI : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  have hred := Lemma212Config.reduce (by norm_num : (3 : ℕ) ≠ 2) hconf
  obtain ⟨K, hK⟩ := exists_isComponentOf_of_not_hasPrimeConstraint Nat.prime_three hcon
  have hz := hred.mem_pCore hQ
  have huniq : ∀ L : Subgroup (H ⧸ primeComplementCore (G := H) 3), IsComponentOf L ⊤ → L = K := by
    intro L hL
    by_contra hne
    exact hred.false_of_two_components hz hL hK hne
  exact h3 (H ⧸ primeComplementCore (G := H) 3) (hcat.quotient _) _ _ _ hred hz K hK huniq

theorem kFactLemma212_of_inputs_red (hK : SchurMultiplierRankFact) (h3 : Bal3ThreeSingleRed) :
    KFactLemma212 := by
  intro p hp hp2 H _ _ hcat P z D hconf _
  by_cases hp3 : p = 3
  · subst hp3
    exact kFactLemma212_three_of_red h3 H hcat P z D hconf
  · have hp5 : 5 ≤ p := by
      have h2 := hp.two_le
      have h4 : p ≠ 4 := by rintro rfl; exact absurd hp (by decide)
      omega
    exact kFactLemma212_five_le hK p hp hp5 H hcat P z D hconf

end CFSG.LocalAnalysis.RankThreeTheoremC.KFactProofs.Stroth.Bal3
