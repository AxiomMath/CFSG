module

public import CFSG.LocalAnalysis.RankThreeTheoremC.RelPair2_Facts
public import CFSG.LocalAnalysis.RankThreeTheoremC.RelPair2_Endgame

public section

namespace CFSG.LocalAnalysis.RankThreeTheoremC

open CFSG.Open CFSG.RankThreeCoreUniqueness.Helpers Subgroup

variable {G : Type} [Group G] [Finite G]

@[expose] def GL83RelPair2Thompson (G : Type) [Group G] [Finite G] : Prop :=
  ∀ p ∈ rankThreeSigmaA G, ∀ (P : Sylow p G) (M D R T H V : Subgroup G),
    MaximalRelativePair p P M D R T → IsOptimalRelPair p M D R T H V →
      OptimalRelPairFacts p M D H V →
        p = 3 ∧ ∃ L : Subgroup (H ⧸ primeComplementCore (G := H) p), IsComponentOf L ⊤ ∧
          Nonempty (L ⧸ center L ≃* alternatingGroup (Fin 7))

@[expose] def GL83RelPair2A7 (G : Type) [Group G] [Finite G] : Prop :=
  ∀ p ∈ rankThreeSigmaA G, ∀ (P : Sylow p G) (M D R T H V : Subgroup G),
    MaximalRelativePair p P M D R T → IsOptimalRelPair p M D R T H V →
      OptimalRelPairFacts p M D H V → p = 3 →
        ∀ L : Subgroup (H ⧸ primeComplementCore (G := H) p), IsComponentOf L ⊤ →
          Nonempty (L ⧸ center L ≃* alternatingGroup (Fin 7)) →
            Nat.card V = 4 * Nat.card (pCoreOf 2 H) ∧ ∃ n ∈ H, n ∈ normalizer (D : Set G) ∧
              p ∣ Nat.card (V ⊔ V.map (MulAut.conj n).toMonoidHom : Subgroup G) ∧
              (∃ T' : Subgroup G, rankTwoMaximalInvariantTwoSubgroup D T' ∧ V < T') ∧
              ∃ S₁ : Subgroup G, ∀ g ∈ normalizer
                ((V.map (MulAut.conj n).toMonoidHom : Subgroup G) : Set G),
                (pCoreOf 2 H).map (MulAut.conj g).toMonoidHom = pCoreOf 2 H ∨
                  (pCoreOf 2 H).map (MulAut.conj g).toMonoidHom = S₁

theorem gl83RelativePairExclusion_of_relPair2 (hS : Setting G) (hD1 : TheoremD1 G)
    (hK : KFactLemma212) (hR : TransitivityReduction G) (h13 : GL83InvariantTwoSylow G)
    (hT : GL83RelPair2Thompson G) (hA7 : GL83RelPair2A7 G) : GL83RelativePairExclusion G := by
  refine gl83RelativePairExclusion_iff.mpr fun p hp P M D R T hd => ?_
  obtain ⟨H, V, hHV⟩ := hd.exists_optimal hS hD1 hp hR h13
  have hfacts := hHV.facts hS hD1 hK hp hR h13 hd
  obtain ⟨h3, L, hL, hLA⟩ := hT p hp P M D R T H V hd hHV hfacts
  obtain ⟨hV4, n, hnH, hnD, hjoin, hVT, horb⟩ := hA7 p hp P M D R T H V hd hHV hfacts h3 L hL hLA
  exact hHV.false_of_card_pCoreOf_lt hS hD1 hp hR h13 hd hV4
    (hHV.card_pCoreOf_lt_of_conj hS hD1 hp hR h13 hd hnH hnD hjoin hVT horb)

end CFSG.LocalAnalysis.RankThreeTheoremC
