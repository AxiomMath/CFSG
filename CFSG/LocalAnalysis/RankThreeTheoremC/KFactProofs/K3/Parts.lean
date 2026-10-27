module

public import CFSG.LocalAnalysis.RankThreeTheoremC.KFactProofs.K3.ThreePart
public import CFSG.LocalAnalysis.RankThreeTheoremC.KFactProofs.K2.Quotient
public import CFSG.RankThree.PerfectCover.HopfCover

public section

namespace CFSG.LocalAnalysis.RankThreeTheoremC.KFactProofs.K3

open CFSG.Open CFSG.RankThreeCoreUniqueness.Helpers Subgroup
open CFSG.LocalAnalysis.RankThreeTheoremC.KFactProofs.K2 (Bar barMk)

@[expose] def K3CatalogQ : Prop :=
  ∀ (S : Type) [Group S] [Finite S], IsSimpleGroup S → (∃ a b : S, a * b ≠ b * a) →
    CFSG.Open.IsCatalogGroup S → 3 ∣ Nat.card S → ¬ 9 ∣ Nat.card S →
      ∃ q : ℕ, q.Prime ∧ 5 ≤ q ∧ q ∣ Nat.card S ∧
        ¬ q ∣ Nat.card (CFSG.RankThree.PerfectCover.hopfMultiplier S)

@[expose] def K3LiftQ : Prop :=
  ∀ (X : Type) [Group X] [Finite X], CFSG.AGLEmbedding.CatalogSimpleSections X →
    ∀ S : Sylow 3 (Bar X), Nonempty ((S : Subgroup (Bar X)) ≃* W3) →
    ∀ L : Subgroup (Bar X), IsComponentOf L ⊤ →
      (∀ K : Subgroup (Bar X), IsComponentOf K ⊤ →
        ∃ g ∈ (S : Subgroup (Bar X)), K = L.map (MulAut.conj g).toMonoidHom) →
      ¬ (S : Subgroup (Bar X)) ≤ normalizer (L : Set (Bar X)) →
      ∀ q : ℕ, q.Prime → 5 ≤ q → q ∣ Nat.card (↥L ⧸ Subgroup.center ↥L) →
        ¬ q ∣ Nat.card (CFSG.RankThree.PerfectCover.hopfMultiplier (↥L ⧸ Subgroup.center ↥L)) →
          3 ≤ CFSG.Open.pRank q (⊤ : Subgroup X)

theorem k3LiftThree_of_parts (hQ : K3CatalogQ) (hL : K3LiftQ) : K3LiftThree := by
  intro X _ _ hcat S hSW L hLc hall hnot
  have hcatH : CFSG.AGLEmbedding.CatalogSimpleSections (Bar X) :=
    hcat.quotient (CFSG.RankThreeCoreUniqueness.Helpers.primeComplementCore (G := X) 3)
  have hH : primeComplementCore (G := Bar X) 3 = ⊥ :=
    CFSG.LocalAnalysis.RankThreeTheoremC.KFactProofs.K2.primeComplementCore_bar (G := X)
  have hq := hLc.2.2
  have hsimple : IsSimpleGroup (↥L ⧸ Subgroup.center ↥L) := hq.2
  have hnab : ∃ a b : ↥L ⧸ Subgroup.center ↥L, a * b ≠ b * a :=
    CFSG.ComponentClassification.Helpers.quasisimple_central_quotient_nonabelian ↥L hq
  have hcatL : CFSG.Open.IsCatalogGroup (↥L ⧸ Subgroup.center ↥L) :=
    hcatH L (Subgroup.center ↥L) inferInstance hsimple hnab
  have h3 := three_dvd_card_component_quotient hH hLc
  have h9 := not_nine_dvd_card_component_quotient hH S hSW hLc hnot
  obtain ⟨q, hqp, hq5, hqd, hqM⟩ := hQ _ hsimple hnab hcatL h3 h9
  exact ⟨q, hqp, hq5, hL X hcat S hSW L hLc hall hnot q hqp hq5 hqd hqM⟩

end CFSG.LocalAnalysis.RankThreeTheoremC.KFactProofs.K3
