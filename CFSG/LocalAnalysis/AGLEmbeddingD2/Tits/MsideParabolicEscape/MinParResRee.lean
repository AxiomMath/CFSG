module

public import CFSG.LocalAnalysis.AGLEmbeddingD2.Tits.MsideParabolicEscape.MinParReeF4
public import CFSG.LocalAnalysis.AGLEmbeddingD2.Tits.MsideParabolicEscape.MinParResSz
public import CFSG.RankThree.PartOne.K133X.F4

public section

namespace CFSG.AGLEmbeddingD2.Tits.MsideParabolicEscape.MinPar

open CFSG.QuasithinUnique CFSG.AGLEmbeddingD2.McLaughlin.WeakBlockModuleData CFSG.Open
  CFSG.LieType.Chevalley CFSG.LieType.Ree CFSG.Blueprint

set_option linter.unusedSectionVars false

section ReeF4

variable {Y : Type} [Group Y] [Finite Y] {L R P : Subgroup Y}

theorem kFact_of_reeF4
    (hR : R ≤ Subgroup.normalizer (L : Set Y)) (hR2 : IsPGroup 2 R)
    (hS : IsSylowTwoOf (R ⊓ L) L) (hP : IsMinOverBorel L (R ⊓ L) P) (m : ℕ)
    (hv : (TauCeti.LieTypeIndex.reeF4 m).Valid)
    (e : (↥L ⧸ Subgroup.center ↥L) ≃* (TauCeti.CFSGIndex.lie ⟨TauCeti.LieTypeIndex.reeF4 m, hv⟩).Group) :
    KFactConcl L R P := by
  obtain ⟨-, hmodel⟩ := CFSG.RankThree.PartOne.K133X.reeTitsModel_twistedF4_of_isoLie
    (X := ↥L ⧸ Subgroup.center ↥L) (m := m) ⟨hv, ⟨e⟩⟩
  obtain ⟨a, K, hKF, hKFin, hcp, ha, hfa, hK, ⟨e'⟩⟩ :=
    CFSG.QuasithinUnique.Setup.X6.exists_mulEquiv_largeRee_model hmodel
  have hK' : Nat.card K = 2 ^ (2 * a + 1) := by rw [hK, hfa]
  exact kFact_of_twoPar_cat hR hR2 hS hP e' ⟨_, _, _, twoPar_reeF4 ha hK'⟩

end ReeF4

end CFSG.AGLEmbeddingD2.Tits.MsideParabolicEscape.MinPar
