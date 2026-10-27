module

public import CFSG.LocalAnalysis.AGLEmbeddingD2.McLaughlin.A7Six.Final
public import CFSG.LocalAnalysis.AGLEmbeddingD2.McLaughlin.A7Six.Natural
public import CFSG.LocalAnalysis.AGLEmbeddingD2.McLaughlin.FiveThreeAlt.A7SixModule

public section

namespace CFSG.AGLEmbeddingD2.McLaughlin.A7Six

open CFSG.Open CFSG.Quasithin CFSG.QuasithinUnique
  CFSG.AGLEmbeddingD2.McLaughlin.WeakBlockModuleData CFSG.AGLEmbeddingD2.GN


theorem false_of_alt7_six_pd (pd : PermData) {X : Type} [Group X] [Finite X] {T : Subgroup X}
    (hX : GNSetting X T) {C₁ C₂ : Subgroup X} (hP : IsC118Pair T C₁ C₂)
    {L : Subgroup (X ⧸ gnC T)} (hY : GNYComponent T C₁ C₂ L)
    (hTN : gnImg T T ≤ Subgroup.normalizer (L : Set (X ⧸ gnC T)))
    (eL : ↥L ≃* alternatingGroup (Fin 7))
    (h6 : (⁅gnV T, L.comap (QuotientGroup.mk' (gnC T))⁆ ⊓
        Subgroup.centralizer (L.comap (QuotientGroup.mk' (gnC T)) : Set X)).relIndex
      ⁅gnV T, L.comap (QuotientGroup.mk' (gnC T))⁆ = 2 ^ 6) : False := by
  obtain ⟨-, h1Z, -, -, h2B, h2c, -⟩ := id hP
  have hJ := commutator_eq_of_gnYComponent hX h1Z h2B h2c hY
  exact false_of_alt7_six_of_nat pd hX hP hY hTN eL fun θ hθ hθL =>
    FiveThreeAlt.natural_of_relIndex_six hX hY.1 hJ eL h6 θ hθ hθL

theorem false_of_alt7_natural_pd (pd : PermData) {X : Type} [Group X] [Finite X]
    {T : Subgroup X} (hX : GNSetting X T) {C₁ C₂ : Subgroup X} (hP : IsC118Pair T C₁ C₂)
    {L : Subgroup (X ⧸ gnC T)} (hY : GNYComponent T C₁ C₂ L)
    (eL : ↥L ≃* alternatingGroup (Fin 7))
    (hTN : gnImg T T ≤ Subgroup.normalizer (L : Set (X ⧸ gnC T)))
    (hn : FiveThreeAlt.A7NaturalCase T L) : False :=
  false_of_alt7_six_pd pd hX hP hY hTN eL (relIndex_six_of_natural hX hP hY eL hn)

theorem gnAltSevenThreeRank_of_permData (pd : PermData) :
    GNAltSevenThreeRank :=
  FiveThreeAlt.gnAltSevenThreeRank_of_natural
    (CFSG.HardMathSupport.Cooperstein.Coordinator.EightFive.gf2EightFive_of_b42L42Core
      CFSG.HardMathSupport.Cooperstein.Coordinator.EightFive.b42L42Core_holds)
    fun _ _ _ _ hX _ _ _ hP _ hY eL hTL hn =>
      (false_of_alt7_natural_pd pd hX hP hY eL hTL hn).elim

end CFSG.AGLEmbeddingD2.McLaughlin.A7Six
