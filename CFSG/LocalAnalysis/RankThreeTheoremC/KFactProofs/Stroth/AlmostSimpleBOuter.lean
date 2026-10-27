module

public import CFSG.LocalAnalysis.RankThreeTheoremC.KFactProofs.Stroth.AlmostSimpleBSmall

public section

namespace CFSG.LocalAnalysis.RankThreeTheoremC.KFactProofs.Stroth.AlmostSimple

open CFSG CFSG.Open Subgroup CFSG.LocalAnalysis.RankThreeTheoremC
open CFSG.AGLEmbeddingD2.McLaughlin.WeakBlockModuleData (IsChevTwo)
open CFSG.RankThree.PartOne.Census3 (IsoLie)

@[expose] def IsLThreeTwo (L : Type) [Group L] : Prop :=
  ∃ q : TauCeti.PrimePower, q.p = 2 ∧ (IsoLie L (.A 2 q) ∨ IsoLie L (.twistedA 2 q))

@[expose] def ChevTwoOuterPElementIsLThree : Prop :=
  ∀ (p : ℕ), p.Prime → p ≠ 2 → ∀ (X : Type) [Group X] [Finite X] (L : Subgroup X) [L.Normal],
    IsSimpleGroup L → (∃ a b : L, a * b ≠ b * a) → IsCatalogGroup L →
    (¬ ∃ n : ℕ, Nonempty (L ≃* alternatingGroup (Fin n))) →
    Subgroup.centralizer (L : Set X) = ⊥ →
    (∀ E : Subgroup X, IsElemAbelian p E → Nat.card E ≤ p ^ 2) →
    CFSG.Open.pRank p (⊤ : Subgroup L) = 2 → IsChevTwo L →
    ∀ d : X, d ∉ L → d ^ p = 1 → p = 3 ∧ IsLThreeTwo ↥L

@[expose] def ChevTwoInnerTwoPartCentralizedRest : Prop :=
  ∀ (p : ℕ), p.Prime → p ≠ 2 → ∀ (X : Type) [Group X] [Finite X] (L : Subgroup X) [L.Normal],
    IsSimpleGroup L → (∃ a b : L, a * b ≠ b * a) → IsCatalogGroup L →
    (¬ ∃ n : ℕ, Nonempty (L ≃* alternatingGroup (Fin n))) →
    Subgroup.centralizer (L : Set X) = ⊥ →
    (∀ E : Subgroup X, IsElemAbelian p E → Nat.card E ≤ p ^ 2) →
    CFSG.Open.pRank p (⊤ : Subgroup L) = 2 → IsChevTwo L →
    ∀ D : Subgroup X, IsElemAbelian p D → Nat.card D = p ^ 2 → D ≤ L → ¬ SignalizerCase p L D →
    ∀ d ∈ D, d ≠ 1 → ∀ S : Subgroup X,
      S ≤ relPPrimeCore p (L ⊓ Subgroup.centralizer ({d} : Set X)) → IsPGroup 2 S →
      D ≤ Subgroup.normalizer (S : Set X) → ⁅S, D⁆ = ⊥

@[expose] def ChevTwoDiagonalTwoPartCentralized : Prop :=
  ∀ (X : Type) [Group X] [Finite X] (L : Subgroup X) [L.Normal],
    IsSimpleGroup L → (∃ a b : L, a * b ≠ b * a) → IsCatalogGroup L →
    (¬ ∃ n : ℕ, Nonempty (L ≃* alternatingGroup (Fin n))) →
    Subgroup.centralizer (L : Set X) = ⊥ →
    (∀ E : Subgroup X, IsElemAbelian 3 E → Nat.card E ≤ 3 ^ 2) →
    CFSG.Open.pRank 3 (⊤ : Subgroup L) = 2 → IsChevTwo L → IsLThreeTwo ↥L →
    ∀ D : Subgroup X, IsElemAbelian 3 D → Nat.card D = 3 ^ 2 → ¬ D ≤ L → ¬ SignalizerCase 3 L D →
    ∀ d ∈ D, d ≠ 1 → ∀ S : Subgroup X,
      S ≤ relPPrimeCore 3 (L ⊓ Subgroup.centralizer ({d} : Set X)) → IsPGroup 2 S →
      D ≤ Subgroup.normalizer (S : Set X) → ⁅S, D⁆ = ⊥

theorem chevTwoPPrimeCoreTwoPartCentralizedRest_of_inner_outer
    (hout : ChevTwoOuterPElementIsLThree) (hin : ChevTwoInnerTwoPartCentralizedRest)
    (hdiag : ChevTwoDiagonalTwoPartCentralized) : ChevTwoPPrimeCoreTwoPartCentralizedRest := by
  intro p hp hp2 X _ _ L _ hs hnab hcat hnalt hCL hrank hrk hchev D hDel hDcard hcase
  by_cases hDL : D ≤ L
  · exact hin p hp hp2 X L hs hnab hcat hnalt hCL hrank hrk hchev D hDel hDcard hDL hcase
  · obtain ⟨d, hdD, hdL⟩ : ∃ d ∈ D, d ∉ L := by
      by_contra hcon
      push Not at hcon
      exact hDL fun x hx => hcon x hx
    obtain ⟨rfl, hL3⟩ := hout p hp hp2 X L hs hnab hcat hnalt hCL hrank hrk hchev d hdL
      (hDel.2 d hdD)
    exact hdiag X L hs hnab hcat hnalt hCL hrank hrk hchev hL3 D hDel hDcard hDL hcase

theorem almostSimplePartBRankTwo_of_inner_outer (hSig : SignalizerTwoGroupKFact)
    (hout : ChevTwoOuterPElementIsLThree) (hin : ChevTwoInnerTwoPartCentralizedRest)
    (hdiag : ChevTwoDiagonalTwoPartCentralized) : AlmostSimplePartBRankTwo :=
  almostSimplePartBRankTwo_of_centralized_rest hSig
    (chevTwoPPrimeCoreTwoPartCentralizedRest_of_inner_outer hout hin hdiag)

end CFSG.LocalAnalysis.RankThreeTheoremC.KFactProofs.Stroth.AlmostSimple
