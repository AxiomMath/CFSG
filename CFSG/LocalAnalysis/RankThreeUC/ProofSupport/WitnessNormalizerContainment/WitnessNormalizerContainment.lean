module


public import CFSG.LocalAnalysis.RankThreeUC.Basic

public section

namespace CFSG.LocalAnalysis.RankThreeUC.ProofSupport.WitnessNormalizerContainment

open CFSG.Open CFSG.LocalAnalysis.RankThreeUC

theorem normalizer_le_of_isWitness {G : Type} [Group G] [Finite G] {p : ℕ} {P : Sylow p G}
    {M : Subgroup G} (hw : IsWitness p P M) {X : Subgroup G} (hX : X ≤ (P : Subgroup G))
    (h2 : 1 < CFSG.Open.pRank p X) : Subgroup.normalizer (X : Set G) ≤ M := by
  have normalizer_le_gamma_two {G : Type} [Group G] [Finite G] (p : ℕ) (P : Subgroup G)
      {X : Subgroup G} (hX : X ≤ P) (h2 : 1 < CFSG.Open.pRank p X) :
      Subgroup.normalizer (X : Set G) ≤ rankThreeGamma 2 p P :=
    le_sSup ⟨X, hX, h2, rfl⟩
  exact (normalizer_le_gamma_two p (P : Subgroup G) hX h2).trans hw.u0

end CFSG.LocalAnalysis.RankThreeUC.ProofSupport.WitnessNormalizerContainment
