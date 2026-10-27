module

public import CFSG.GroupTheory.SylowIntersectionControl.GomiChevLeviPackageModels
public import CFSG.LocalAnalysis.AGLEmbeddingD2.Tits.MsideParabolicEscape.MinParReeF4
import CFSG.GroupTheory.SylowIntersectionControl.GomiChevLeviVacuousTwoPar
import CFSG.Blueprint.LieModelAPI
public import CFSG.LocalAnalysis.AGLEmbeddingD2.Tits.MsideParabolicEscape.MinParTwoMap

public section

namespace CFSG.GroupTheory

open CFSG.Open CFSG.AGLEmbeddingD2.Tits.MsideParabolicEscape.MinPar

theorem gomiAtomsOnlyTop_of_oneNode {X : Type} [Group X] [Finite X] {T : Subgroup X}
    (hT : CFSG.QuasithinUnique.IsSylowTwoOf T ⊤) (h : OneNode X T) : GomiAtomsOnlyTop X :=
  fun _ _ hU hBQ hQ => absurd ((h.of_sylow hT
    (CFSG.QuasithinUnique.Setup.X6.isSylowTwoOf_iff_isSylowOf.2 hU)).coatom.lt_iff.1 hBQ) hQ.ne

section Suzuki


theorem gomiChevLeviPackageModel_twistedB2 (n : ℕ) : GomiChevLeviPackageModel .twistedB2 n :=
  gomiChevLeviPackageModel_of_gomiAtomsOnlyTop fun X _ _ f h => by
    obtain ⟨-, -, a, -, K, hKfield, hKfin, hf, hcard, ⟨e⟩⟩ :=
      CFSG.Blueprint.LieModel.suzukiModel h
    have hK : Nat.card K = 2 ^ (2 * a + 1) := by rw [hcard, hf]
    refine gomiAtomsOnlyTop_of_oneNode ?_ (OneNode.map e.symm (suzuki_oneNode hK))
    exact CFSG.AGLEmbeddingD2.Tits.MsideParabolicEscape.ChevGen.isSylowTwoOf_top_map_equiv
      e.symm (suzukiU_isSylowTwoOf hK)

end Suzuki

section Ree


theorem gomiChevLeviPackageModel_twistedF4 (n : ℕ) : GomiChevLeviPackageModel .twistedF4 n :=
  gomiChevLeviPackageModel_of_gomiAtomsOnlyTop fun X _ _ f h => by
    obtain ⟨-, hree⟩ := CFSG.Blueprint.LieModel.reeTitsModel h (by decide)
    obtain ⟨a, K, hKfield, hKfin, hKcp, ha, hfa, hcard, ⟨e⟩⟩ :=
      CFSG.QuasithinUnique.Setup.X6.exists_mulEquiv_largeRee_model (X := X) hree
    have hK : Nat.card K = 2 ^ (2 * a + 1) := by rw [hcard, hfa]
    exact gomiAtomsOnlyTop_of_twoPar (TwoPar.map e.symm (twoPar_reeF4 (K := K) (a := a) ha hK))

end Ree

end CFSG.GroupTheory
