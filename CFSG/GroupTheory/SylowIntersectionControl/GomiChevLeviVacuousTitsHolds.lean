module

public import CFSG.GroupTheory.SylowIntersectionControl.GomiChevLeviVacuous
public import CFSG.LocalAnalysis.AGLEmbeddingD2.Tits.MsideParabolicEscape.MinParTits
import CFSG.GroupTheory.SylowIntersectionControl.GomiChevLeviVacuousTwoPar
public import CFSG.LocalAnalysis.AGLEmbeddingD2.Tits.MsideParabolicEscape.MinParTwoAssembly
public import CFSG.LocalAnalysis.AGLEmbeddingD2.Tits.MsideParabolicEscape.MinParTwoMap

public section

namespace CFSG.GroupTheory

theorem gomiAtomsOnlyTop_of_lieModel_tits
    {K : Type} [Group K] [Finite K] {n f : ℕ} (hK : CFSG.Blueprint.LieModel K .Tits n 2 f) :
    GomiAtomsOnlyTop K := by
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
  exact gomiAtomsOnlyTop_of_twoPar h

end CFSG.GroupTheory
