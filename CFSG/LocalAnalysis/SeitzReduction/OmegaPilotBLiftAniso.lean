module

public import CFSG.LocalAnalysis.SeitzReduction.OmegaPilotNeighbourStandardAniso

public section

namespace CFSG.SeitzReduction.OmegaPilot

open Subgroup CFSG.Open
open CFSG.ComponentClassification.CatalogueBOrthogonalSemilinear (matrixProjectiveDerived)
open CFSG.ComponentClassification.CatalogueBOrthogonalPointData (coordinateQuadMinus)
open CFSG.SeitzReduction.F4Pilot (HasBLift oddCoreLift)

variable {G : Type} [Group G] [Finite G] {L : Subgroup G}

section Aniso

variable (hset : SeitzSetting G L) {n f : ℕ} {K : Type} [Field K] (hKc : Nat.card K = 2 ^ f)
  (hn : 4 ≤ n) {b c : K} (hirr : ∀ s : K, s ^ 2 + b * s + c ≠ 0)
  (e : L ≃* matrixProjectiveDerived (coordinateQuadMinus n K (one_le_of_four_le hn) b c))
  {t : G} (htC : t ∈ centralizer (L : Set G)) (ht : orderOf t = 2) {X : Subgroup G}
  (htX : t ∈ centralizer (X : Set G)) {D : Subgroup G}

include hset hKc hirr htC ht

theorem bLift_inputs_anisoTorus_of_seitzSetting [Finite K] [CharP K 2]
    (hX : X = ((anisoTorus (K := K) (by omega) b c).map e.symm.toMonoidHom).map L.subtype)
    (hDe : D = ((anisoPerp (K := K) (by omega) b c).map e.symm.toMonoidHom).map L.subtype) :
    centralizer ({t} : Set G) ≤ normalizer (L : Set G) ∧
      D = inSubgroup layer (L ⊓ centralizer (X : Set G)) ∧ CFSG.IsQuasisimple D ∧
      ∀ x ∈ centralizer (X : Set G) ⊓ centralizer ({t} : Set G) ⊓ centralizer (D : Set G),
        Odd (orderOf x) → x ∈ X :=
  bLift_inputs_anisoTorus hset.standardSetting.standard htC ht
    (inf_centralizer_eq_zpowers_minus hset hn hKc hirr e htC ht) hn hirr e hX hDe

end Aniso

end CFSG.SeitzReduction.OmegaPilot
