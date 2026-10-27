module

public import CFSG.LocalAnalysis.RankThreeTheoremC.KFactProofs.Stroth.AlmostSimpleSplit
public import CFSG.LocalAnalysis.RankThreeTheoremC.KFactProofs.Stroth.AlmostSimpleBBase
public import CFSG.LocalAnalysis.RankThreeTheoremC.SignalizerNoncentral2_7KFact

public section

namespace CFSG.LocalAnalysis.RankThreeTheoremC.KFactProofs.Stroth.AlmostSimple

open CFSG CFSG.Open Subgroup CFSG.LocalAnalysis.RankThreeTheoremC
open CFSG.AGLEmbeddingD2.McLaughlin.WeakBlockModuleData (IsChevTwo)
open CFSG.RankThree.PartOne.Census3 (IsoLie)

@[expose] def SignalizerCase (p : ℕ) {X : Type} [Group X] (L D : Subgroup X) : Prop :=
  (IsRankTwoSEGroup p L ∧ D ≤ L) ∨
    (p = 3 ∧ IsoLie ↥L (.A 1 ⟨2, 3, by norm_num, by norm_num⟩)) ∨
    (p = 5 ∧ IsoLie ↥L (.suzuki 2))

@[expose] def ChevTwoPPrimeCoreTwoPartCentralizedRest : Prop :=
  ∀ (p : ℕ), p.Prime → p ≠ 2 → ∀ (X : Type) [Group X] [Finite X] (L : Subgroup X) [L.Normal],
    IsSimpleGroup L → (∃ a b : L, a * b ≠ b * a) → IsCatalogGroup L →
    (¬ ∃ n : ℕ, Nonempty (L ≃* alternatingGroup (Fin n))) →
    Subgroup.centralizer (L : Set X) = ⊥ →
    (∀ E : Subgroup X, IsElemAbelian p E → Nat.card E ≤ p ^ 2) →
    CFSG.Open.pRank p (⊤ : Subgroup L) = 2 → IsChevTwo L →
    ∀ D : Subgroup X, IsElemAbelian p D → Nat.card D = p ^ 2 → ¬ SignalizerCase p L D →
    ∀ d ∈ D, d ≠ 1 → ∀ S : Subgroup X,
      S ≤ relPPrimeCore p (L ⊓ Subgroup.centralizer ({d} : Set X)) → IsPGroup 2 S →
      D ≤ Subgroup.normalizer (S : Set X) → ⁅S, D⁆ = ⊥

theorem le_centralizer_of_signalizerCase (hSig : SignalizerTwoGroupKFact) {p : ℕ}
    (hp : p.Prime) (hp2 : p ≠ 2) {X : Type} [Group X] [Finite X] {L D : Subgroup X} [L.Normal]
    (hs : IsSimpleGroup L) (hnab : ∃ a b : L, a * b ≠ b * a) (hcat : IsCatalogGroup L)
    (hC : Subgroup.centralizer (L : Set X) = ⊥) (hDel : IsElemAbelian p D)
    (hDcard : Nat.card D = p ^ 2) (hcase : SignalizerCase p L D) {T : Subgroup X}
    (hT2 : IsPGroup 2 T) (hDT : D ≤ normalizer (T : Set X)) : T ≤ centralizer (D : Set X) := by
  have hDC : D ⊓ Subgroup.centralizer (L : Set X) = ⊥ := by rw [hC, inf_bot_eq]
  have h := hSig X L inferInstance hs hnab hcat p hp hp2 D hDel hDcard hDC hcase T hT2 hDT
  rw [hC] at h
  exact Subgroup.le_centralizer_iff.1
    (Subgroup.commutator_eq_bot_iff_le_centralizer.1 (le_bot_iff.1 h))

theorem almostSimplePartBRankTwo_of_centralized_rest (hSig : SignalizerTwoGroupKFact)
    (h : ChevTwoPPrimeCoreTwoPartCentralizedRest) : AlmostSimplePartBRankTwo := by
  intro p hp hp2 X _ _ L _ hs hnab hcat hnalt hC hE hrk hchev D hF _ hjoin
  refine not_dvd_card_invariantTwoJoin_of_centralizes hF (fun T hTL hT2 hDT => ?_) hjoin
  by_cases hcase : SignalizerCase p L D
  · exact le_centralizer_of_signalizerCase hSig hp hp2 hs hnab hcat hC hF.elem hF.card hcase hT2 hDT
  · exact le_centralizer_of_invariantTwo hF
      (fun a ha ha1 S hS hS2 hDS =>
        h p hp hp2 X L hs hnab hcat hnalt hC hE hrk hchev D hF.elem hF.card hcase a ha ha1 S hS hS2
          hDS)
      hTL hT2 hDT

end CFSG.LocalAnalysis.RankThreeTheoremC.KFactProofs.Stroth.AlmostSimple
