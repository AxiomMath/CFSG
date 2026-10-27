module

public import CFSG.GroupTheory.SylowIntersectionControl.GomiChevAtomGenerationTwoPar
public import CFSG.LocalAnalysis.AGLEmbeddingD2.Tits.MsideParabolicEscape.MinParTits
import CFSG.LieType.BorelTits.AllModels
import CFSG.Quasithin.Background.C22PfG
public import CFSG.LocalAnalysis.AGLEmbeddingD2.Tits.MsideParabolicEscape.MinParTwoAssembly
public import CFSG.LocalAnalysis.AGLEmbeddingD2.Tits.MsideParabolicEscape.MinParTwoMap

public section

namespace CFSG.GroupTheory

theorem holds_two_of_lieModel_tits
    {K : Type} [Group K] [Finite K] {n f : ℕ} (hK : CFSG.Blueprint.LieModel K .Tits n 2 f) :
    CFSG.LieType.BorelTits.Holds K 2 :=
  CFSG.Quasithin.C22Pf.holds_of_holdsTits (CFSG.LieType.BorelTits.holdsTits_of_lieModel_tits hK)
    (CFSG.Quasithin.C22Pf.titsSylowSelfNormalizing_holds K n f hK)

theorem gomiAtomGenerationTop_of_lieModel_tits
    {K : Type} [Group K] [Finite K] {n f : ℕ} (hK : CFSG.Blueprint.LieModel K .Tits n 2 f) :
    GomiAtomGenerationTop K := by
  have hR : CFSG.Blueprint.ReeTitsModel K .Tits 2 f := by
    rcases hK with ⟨hcl, -⟩ | ⟨-, hce, -⟩ | ⟨-, -, hree⟩ | ⟨-, hsz, -⟩
    · exact absurd hcl (by decide)
    · exact absurd hce (by decide)
    · exact hree
    · exact absurd hsz (by decide)
  obtain ⟨e⟩ := CFSG.Sporadic.Schreier.Tits.titsModelEquiv K 2 f hR
  obtain ⟨P₁, P₂, h⟩ :=
    CFSG.AGLEmbeddingD2.Tits.MsideParabolicEscape.MinPar.twoParLat_tits.toTwoPar.exists_of_equiv
      e.symm (CFSG.QuasithinUnique.isSylowTwoOf_top_of_sylow (default : Sylow 2 K))
  exact gomiAtomGenerationTop_of_twoPar h

end CFSG.GroupTheory
