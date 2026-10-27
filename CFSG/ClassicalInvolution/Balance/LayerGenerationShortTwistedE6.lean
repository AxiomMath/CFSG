module

public import CFSG.ClassicalInvolution.Balance.LayerGenerationShortTwistedAssembly
public import CFSG.ClassicalInvolution.ModelFacts.ClassicalIsFundamentalTwistedE6Sign

public section

namespace CFSG.ClassicalInvolution.Balance.Bootstrap

open CFSG.Blueprint.Chevalley CFSG.LieType.Chevalley CFSG.LieType.AlgebraicGroups
  CFSG.LocalAnalysis.ComponentInitial.FourGroupChevalley CFSG.Open CFSG.ClassicalInvolution
  CFSG.ClassicalInvolution.Generic CFSG.LieType.CurtisTits

section SignGroup

@[expose] noncomputable def twistedE6SignGroup (n p e : ℕ) [Fact p.Prime] :
    Subgroup (modelUniv .twistedE6 n p e Fact.out).K :=
  (ModelFacts.e6SignDiagonalGroup (AlgebraicClosure (GaloisField p (2 * e)))).comap
    (show (modelUniv .twistedE6 n p e Fact.out).K →* ModGL TwistTag.E6.tag
        (AlgebraicClosure (GaloisField p (2 * e))) from
      CFSG.ClassicalInvolution.ModelFacts.twistedE6Phi p e
        (AlgebraicClosure (GaloisField p (2 * e))))

end SignGroup

section Statements

variable (p : ℕ) [Fact p.Prime] (n e : ℕ)

@[expose] def TwistedE6PairFrame : Prop :=
  PairFrame (twistedE6SignGroup n p e)
    (fundamentalSubgroups .twistedE6 (modelUniv .twistedE6 n p e Fact.out).D)

variable {p n e}

theorem twistedE6ToralLayers (hadm : StatedLieAdmissible .twistedE6 n p e) (h5 : 5 ≤ p ^ e)
    (hp2 : p ≠ 2) :
    ∀ i : Fin (modelUniv .twistedE6 n p e Fact.out).D.rank, ∀ s₁ ∈ twistedE6SignGroup n p e,
      ∀ s₂ ∈ twistedE6SignGroup n p e, s₁ ≠ 1 → s₂ ≠ 1 → s₁ * s₂ ≠ 1 →
        ∃ s ∈ ({s₁, s₂, s₁ * s₂} : Set (modelUniv .twistedE6 n p e Fact.out).K),
          rankOne (modelUniv .twistedE6 n p e Fact.out).D.rootGroup i ≤
            ⨆ (Q : Subgroup (modelUniv .twistedE6 n p e Fact.out).K)
              (_ : IsComponentOf Q (Subgroup.centralizer
                ({s} : Set (modelUniv .twistedE6 n p e Fact.out).K))), Q := by
  intro i s₁ hs₁ s₂ hs₂ _ _ _
  exact ModelFacts.twistedE6_toralLayers p e hp2 hadm.2.1 h5 i hs₁ hs₂

theorem layerGenerationPairAt_twistedE6 (hadm : StatedLieAdmissible .twistedE6 n p e)
    (hp2 : p ≠ 2) (h5 : 5 ≤ p ^ e) (hframe : TwistedE6PairFrame p n e) :
    LayerGenerationPairAt .twistedE6 n p e Fact.out :=
  layerGenerationPairAt_of_toralLayers trivial hadm hp2 h5 (twistedE6SignGroup n p e)
    (twistedE6ToralLayers hadm h5 hp2) hframe

end Statements

end CFSG.ClassicalInvolution.Balance.Bootstrap
