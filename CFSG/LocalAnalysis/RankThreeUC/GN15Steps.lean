module

public import CFSG.CGT.PushingUpLit.Transport
public import CFSG.Fischer.Classification.Recognition.PSU6
public import CFSG.LocalAnalysis.AGLEmbeddingD2.McLaughlin.WeakBlockModuleData.GlaubermanNiles
public import CFSG.LocalAnalysis.ComponentClassification.ClassicalModelStatedBridge
public import CFSG.LocalAnalysis.RankTwoShapes.UnitaryFour.Bridge

public section

namespace CFSG.LocalAnalysis.RankThreeUC.S15.GN15

open CFSG.AGLEmbeddingD2.McLaughlin.WeakBlockModuleData CFSG.Quasithin CFSG.QuasithinUnique
  CFSG.Open

variable {X : Type} [Group X]

@[expose] noncomputable def gnHPre (T : Subgroup X) : Subgroup X :=
  (Subgroup.centralizer (rankThreeLayer (⊤ : Subgroup (X ⧸ gnC T)) : Set (X ⧸ gnC T))).comap
    (QuotientGroup.mk' (gnC T))

@[expose] noncomputable def gnDStar (T : Subgroup X) : Subgroup (X ⧸ gnC T) :=
  ⨆ L ∈ {L : Subgroup (X ⧸ gnC T) | IsComponentOf L ⊤ ∧ ⁅L, gnImg T (thompsonJ T)⁆ ≠ ⊥}, L

@[expose] noncomputable def gnDPre (T : Subgroup X) : Subgroup X :=
  (gnDStar T).comap (QuotientGroup.mk' (gnC T))

@[expose] noncomputable def gnQPre (T : Subgroup X) : Subgroup X :=
  (Subgroup.centralizer (gnDStar T : Set (X ⧸ gnC T))).comap (QuotientGroup.mk' (gnC T))

end CFSG.LocalAnalysis.RankThreeUC.S15.GN15

end
