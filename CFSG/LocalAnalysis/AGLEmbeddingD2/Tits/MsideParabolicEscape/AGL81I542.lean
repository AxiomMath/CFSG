module

public import CFSG.LocalAnalysis.AGLEmbeddingD2.Tits.MsideParabolicEscape.RankTwoPermute
public import CFSG.LocalAnalysis.AGLEmbeddingD2.McLaughlin.WeakBlockModuleData.GlaubermanNiles

public section

namespace CFSG.AGLEmbeddingD2.Tits.MsideParabolicEscape

open CFSG.Open CFSG.Quasithin CFSG.QuasithinUnique
open CFSG.AGLEmbeddingD2.McLaughlin.WeakBlockModuleData

@[expose] def autIn {Y : Type} [Group Y] (L : Subgroup Y) : Subgroup (MulAut ↥L) :=
  L.normalizerMonoidHom.range

@[expose] def AutInOK {Y : Type} [Group Y] (L : Subgroup Y) : Prop :=
  (innSub ↥L).relIndex (autIn L) ≤ 2 ∧
    (Nonempty (↥L ≃* alternatingGroup (Fin 6)) → (innSub ↥L).relIndex (autIn L) = 2 →
      Nonempty (↥(autIn L) ≃* Equiv.Perm (Fin 6))) ∧
    (StatedClassicalModel ↥L .PSL 3 2 1 → (innSub ↥L).relIndex (autIn L) = 1)

@[expose] def AGL81I542 : Prop :=
  ∀ (X : Type) [Group X] [Finite X] (T : Subgroup X), GNSetting X T →
    ∀ L : Subgroup (X ⧸ gnC T), IsComponentOf L ⊤ →
      ⁅L, gnImg T (thompsonJ T)⁆ = L → IsRankTwoLayerType ↥L → AutInOK L

end CFSG.AGLEmbeddingD2.Tits.MsideParabolicEscape
