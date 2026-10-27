module

public import CFSG.ClassicalInvolution.Asc77.AscR31Recog

public section

namespace CFSG.ClassicalInvolution.Asc77

namespace R31

set_option linter.unusedSectionVars false

open CFSG.Open CFSG.ClassicalInvolution CFSG.ClassicalInvolution.Generic
  CFSG.ClassicalInvolution.Disconnected CFSG.Assembly.LowTwoRank
open CFSG.Timmesfeld (edgeD)
open CFSG.ClassicalInvolution.Phan (UnitaryBlockStandardPair)

variable (p f : ℕ) [Fact p.Prime]


@[expose] def PhanD4Recognition : Prop :=
  p ≠ 2 → 5 ≤ p ^ f → ∀ (G : Type) [Group G] [Finite G] [IsSimpleGroup G] (Ω : Set (Subgroup G)),
    ConjInvariant Ω → ∀ U : Fin 4 → Subgroup G, (∀ k, U k ∈ Ω) →
      (∀ J ∈ Ω, ∃ g : G, J = conjSub g (U 0)) →
      (∀ i j : Fin 4, i ≠ j → ¬ edgeD 4 i j → ¬ edgeD 4 j i → Commutes (U i) (U j)) →
      (∀ i j : Fin 4, edgeD 4 i j →
        ∃ W, UnitaryBlockStandardPair (GaloisField p (2 * f)) p f W (U i) (U j)) →
      ⨆ k, U k = ⊤ →
        ∃ D : LieSystemData p f G Ω, D.card = 1 ∧ ∃ i, D.tag i = .POmegaPlus ∧ D.rank i = 4

@[expose] def C22_phanChainNeg : Prop :=
  p ^ f % 4 = 3 → ∀ (G : Type) [Group G] [Finite G] [IsSimpleGroup G] (Ω : Set (Subgroup G))
    (K K' K₃ : Subgroup G) (z u₁ u₂ u₃ : G), Hyp22Setting p f Ω K K' K₃ z u₁ u₂ u₃ →
      (∀ W ∈ WSet Ω, MuIsoWylD4 Ω W) →
        (LayerOrthType p f Ω (u₁ * u₂) 6 (piSign p f) ∧
          (⨆ M ∈ twinSet Ω K, M) ⊔ rLayer Ω (u₁ * u₂) = ⊤) →
          ∃ U : Fin 4 → Subgroup G, (∀ k, U k ∈ Ω) ∧
            (∀ i j : Fin 4, i ≠ j → ¬ edgeD 4 i j → ¬ edgeD 4 j i → Commutes (U i) (U j)) ∧
            (∀ i j : Fin 4, edgeD 4 i j →
              ∃ W, UnitaryBlockStandardPair (GaloisField p (2 * f)) p f W (U i) (U j)) ∧
            ⨆ k, U k = ⊤

variable {p f} in
theorem c22_recogNeg_of_phan (hP : PhanD4Recognition p f) (hC : C22_phanChainNeg p f) :
    C22_recogNeg p f := by
  intro hq G _ _ _ Ω K K' K₃ z u₁ u₂ u₃ hs hW hLayer
  obtain ⟨U, hUΩ, hcomm, hpair, hgen⟩ := hC hq G Ω K K' K₃ z u₁ u₂ u₃ hs hW hLayer
  have hcls : ∀ J ∈ Ω, ∃ g : G, J = conjSub g (U 0) := by
    intro J hJ
    obtain ⟨g, hg⟩ := (hs.stand.of_mem (hUΩ 0)).trans J hJ
    exact ⟨g, hg.symm⟩
  exact hP hs.stand.odd hs.stand.five G Ω hs.stand.hyp.conjInvariant U hUΩ hcls hcomm hpair hgen

end R31

end CFSG.ClassicalInvolution.Asc77
