module

public import CFSG.LocalAnalysis.RankThreeTheoremC.RelPair2A7_Main
public import CFSG.LocalAnalysis.RankThreeTheoremC.RelPair2A7B_Two
public import CFSG.LocalAnalysis.RankThreeTheoremC.RelPair2A7B_Elem
public import CFSG.LocalAnalysis.RankThreeTheoremC.RelPair2A7B_Rank

public section

namespace CFSG.LocalAnalysis.RankThreeTheoremC

open CFSG.Open CFSG.RankThreeCoreUniqueness.Helpers Subgroup

variable {G : Type} [Group G] [Finite G]

@[expose] def GL83RelPair2A7Module (G : Type) [Group G] [Finite G] : Prop :=
  ∀ p ∈ rankThreeSigmaA G, ∀ (P : Sylow p G) (M D R T H V : Subgroup G),
    MaximalRelativePair p P M D R T → IsOptimalRelPair p M D R T H V →
      OptimalRelPairFacts p M D H V → p = 3 →
        ∀ L : Subgroup (H ⧸ primeComplementCore (G := H) p), IsComponentOf L ⊤ →
          Nonempty (L ⧸ center L ≃* alternatingGroup (Fin 7)) →
            Nat.card V = 4 * Nat.card (pCoreOf 2 H) →
              (∃ n ∈ H, n ∈ normalizer (D : Set G) ∧
                p ∣ Nat.card (V ⊔ V.map (MulAut.conj n).toMonoidHom : Subgroup G)) →
                ∃ J₁ U : Subgroup G, A7ModuleData D H V J₁ U

theorem gl83RelPair2A7B_of_module (hS : Setting G) (hD1 : TheoremD1 G)
    (hR : TransitivityReduction G) (h13 : GL83InvariantTwoSylow G)
    (hM : GL83RelPair2A7Module G) : GL83RelPair2A7B G := by
  intro p hp P M D R T H V hd hopt hfacts hp3 L hL hLA hcard
  obtain ⟨e⟩ := hLA
  obtain ⟨-, n, hnH, hnD, hjoin⟩ := hopt.a7_structure hd hfacts hp3 hL e
  obtain ⟨J₁, U, hdata⟩ := hM p hp P M D R T H V hd hopt hfacts hp3 L hL ⟨e⟩ hcard
    ⟨n, hnH, hnD, hjoin⟩
  have hnotmax := not_invariantTwoMaximalWithin_of_module hS hD1 hp hR h13 hd hfacts hp3 hdata
    hcard
  obtain ⟨-, _, -, -, -, -, -, -, hglob⟩ := hd.ext.transitivity_data hS hD1 hp
    hd.not_le_normalizer hR h13
  obtain ⟨T'', hVT'', hT''max⟩ := exists_invariantTwoMaximalWithin_containing D M V hfacts.le_M
    hfacts.maximal.2.1 hfacts.maximal.2.2.1
  have hlt : V < T'' := lt_of_le_of_ne hVT'' fun h => hnotmax (h ▸ hT''max)
  have hel : IsElemAbelian 2 (pCoreOf 2 H) := by
    subst hp3
    exact hopt.isElemAbelian_pCoreOf hfacts hdata hcard hT''max.1 hT''max.2.1 hT''max.2.2.1 hlt
  have hVn : V ≤ normalizer (pCoreOf 2 H : Set G) :=
    hfacts.maximal.1.trans hfacts.normalizer_pCore.ge
  obtain ⟨S₁, hS₁⟩ := a7_orbit_pCore_le_two hdata hfacts.pCore_le hel hcard hVn
  exact ⟨⟨T'', (hglob T'' hT''max).1, hlt⟩, S₁, hS₁⟩

theorem gl83RelativePairExclusion_of_relPair2A7Module (hS : Setting G) (hD1 : TheoremD1 G)
    (hK : KFactLemma212) (hR : TransitivityReduction G) (h13 : GL83InvariantTwoSylow G)
    (hT : GL83RelPair2Thompson G) (hM : GL83RelPair2A7Module G) : GL83RelativePairExclusion G :=
  gl83RelativePairExclusion_of_relPair2A7 hS hD1 hK hR h13 hT
    (gl83RelPair2A7B_of_module hS hD1 hR h13 hM)

end CFSG.LocalAnalysis.RankThreeTheoremC
