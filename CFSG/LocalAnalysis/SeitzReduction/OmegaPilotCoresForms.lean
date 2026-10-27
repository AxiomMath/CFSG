module

public import CFSG.LocalAnalysis.SeitzReduction.OmegaPilotCores
public import CFSG.LocalAnalysis.SeitzReduction.OmegaPilotNeighbourStandardAniso

public section

namespace CFSG.SeitzReduction.OmegaPilot

open Subgroup QuadraticMap
open CFSG.Quasithin (perfectCore)
open CFSG.ComponentClassification.CatalogueBOrthogonalSemilinear (matrixProjectiveDerived)
open CFSG.ComponentClassification.CatalogueBOrthogonalPointData
  (plusIndexEquiv minusIndexEquiv coordinateQuadPlus coordinateQuadMinus)
open CFSG.SeitzReduction.SymplecticPilot (planeTorusParam)
open CFSG.SeitzReduction.F4Pilot (centralizerPerfectCore centralizerPerfectCore_anti)
open CFSG.SeitzReduction.UnitaryPilot (modelToG modelToG_mono)

section Frames

variable (K : Type*) [Field K] (n : ℕ)

@[expose] noncomputable def plusFrameLeft (k : Fin n) : Fin (2 * n) := plusIndexEquiv n (.inl k)

@[expose] noncomputable def plusFrameRight (k : Fin n) : Fin (2 * n) := plusIndexEquiv n (.inr k)

theorem isHypFrame_plus :
    IsHypFrame (coordinateQuadPlus n K) (plusFrameLeft n) (plusFrameRight n) where
  hyp k := isHypCoord_coordinateQuadPlus k
  left_injective _ _ h := Sum.inl_injective ((plusIndexEquiv n).injective h)
  right_injective _ _ h := Sum.inr_injective ((plusIndexEquiv n).injective h)
  left_ne_right _ _ h := Sum.inl_ne_inr ((plusIndexEquiv n).injective h)

variable {n} (hn : 1 ≤ n)

@[expose] noncomputable def minusFrameLeft (k : Fin (n - 1)) : Fin (2 * n) :=
  minusIndexEquiv n hn (.inl k)

@[expose] noncomputable def minusFrameRight (k : Fin (n - 1)) : Fin (2 * n) :=
  minusIndexEquiv n hn (.inr (.inl k))

theorem isHypFrame_minus (b c : K) :
    IsHypFrame (coordinateQuadMinus n K hn b c) (minusFrameLeft hn) (minusFrameRight hn) where
  hyp k := isHypCoord_coordinateQuadMinus hn b c k
  left_injective _ _ h := Sum.inl_injective ((minusIndexEquiv n hn).injective h)
  right_injective _ _ h :=
    Sum.inl_injective (Sum.inr_injective ((minusIndexEquiv n hn).injective h))
  left_ne_right _ _ h := Sum.inl_ne_inr ((minusIndexEquiv n hn).injective h)

end Frames

section Tori

variable (K : Type) [Field K] {n : ℕ}

@[expose] noncomputable def plusFrameTorus (P : Subgroup (Fin n → Kˣ)) :
    Subgroup (matrixProjectiveDerived (coordinateQuadPlus n K)) :=
  frameTorusOf (coordinateQuadPlus n K) (plusFrameLeft n) (plusFrameRight n) P

@[expose] noncomputable def plusPlaneTorus (I : Finset (Fin n)) :
    Subgroup (matrixProjectiveDerived (coordinateQuadPlus n K)) :=
  plusFrameTorus K (planeTorusParam K I)

@[expose] noncomputable def plusLevelTorus (J : Finset (Fin n)) :
    Subgroup (matrixProjectiveDerived (coordinateQuadPlus n K)) :=
  plusFrameTorus K (levelParam J)

variable {K}

theorem plusFrameTorus_rootParam (k : Fin n) : plusFrameTorus K (rootParam k) = pairTorus k :=
  frameTorusOf_rootParam k

variable (hn : 1 ≤ n) (b c : K)

@[expose] noncomputable def minusFrameTorus (P : Subgroup (Fin (n - 1) → Kˣ)) :
    Subgroup (matrixProjectiveDerived (coordinateQuadMinus n K hn b c)) :=
  frameTorusOf (coordinateQuadMinus n K hn b c) (minusFrameLeft hn) (minusFrameRight hn) P

@[expose] noncomputable def minusPlaneTorus (I : Finset (Fin (n - 1))) :
    Subgroup (matrixProjectiveDerived (coordinateQuadMinus n K hn b c)) :=
  minusFrameTorus hn b c (planeTorusParam K I)

@[expose] noncomputable def minusLevelTorus (J : Finset (Fin (n - 1))) :
    Subgroup (matrixProjectiveDerived (coordinateQuadMinus n K hn b c)) :=
  minusFrameTorus hn b c (levelParam J)

@[expose] noncomputable def minusAnisoPlaneTorus [CharP K 2] (I : Finset (Fin (n - 1))) :
    Subgroup (matrixProjectiveDerived (coordinateQuadMinus n K hn b c)) :=
  minusPlaneTorus hn b c I ⊔ anisoTorus hn b c

variable {hn b c}

theorem minusFrameTorus_rootParam (k : Fin (n - 1)) :
    minusFrameTorus hn b c (rootParam k) = minusPairTorus hn b c k :=
  frameTorusOf_rootParam k

theorem minusPairTorus_le_minusPlaneTorus {k : Fin (n - 1)} {I : Finset (Fin (n - 1))}
    (hk : k ∉ I) : minusPairTorus hn b c k ≤ minusPlaneTorus hn b c I := by
  rw [← minusFrameTorus_rootParam]
  exact frameTorusOf_mono (rootParam_le_planeTorusParam hk)

theorem minusPairTorus_le_minusLevelTorus {k : Fin (n - 1)} {J : Finset (Fin (n - 1))}
    (hk : k ∉ J) : minusPairTorus hn b c k ≤ minusLevelTorus hn b c J := by
  rw [← minusFrameTorus_rootParam]
  exact frameTorusOf_mono (rootParam_le_levelParam hk)

end Tori

section PlusCores

variable {G : Type*} [Group G] {L : Subgroup G} {K : Type} [Field K] {n : ℕ}
  (e : L ≃* matrixProjectiveDerived (coordinateQuadPlus n K))

@[expose] noncomputable def plusPieceCore (I : Finset (Fin n)) : Subgroup G :=
  centralizerPerfectCore (modelToG e (plusPlaneTorus K I))

@[expose] noncomputable def plusLevelCore (J : Finset (Fin n)) : Subgroup G :=
  centralizerPerfectCore (modelToG e (plusLevelTorus K J))

@[expose] noncomputable def plusNeighbourCore (k : Fin n) : Subgroup G :=
  centralizerPerfectCore (modelToG e (pairTorus (K := K) k))

variable [Finite G]

end PlusCores

section MinusCores

variable {G : Type*} [Group G] {L : Subgroup G} {K : Type} [Field K] {n : ℕ} {hn : 1 ≤ n}
  {b c : K} (e : L ≃* matrixProjectiveDerived (coordinateQuadMinus n K hn b c))

@[expose] noncomputable def minusPieceCore (I : Finset (Fin (n - 1))) : Subgroup G :=
  centralizerPerfectCore (modelToG e (minusPlaneTorus hn b c I))

@[expose] noncomputable def minusLevelCore (J : Finset (Fin (n - 1))) : Subgroup G :=
  centralizerPerfectCore (modelToG e (minusLevelTorus hn b c J))

@[expose] noncomputable def minusNeighbourCore (k : Fin (n - 1)) : Subgroup G :=
  centralizerPerfectCore (modelToG e (minusPairTorus hn b c k))

@[expose] noncomputable def anisoNeighbourCore [CharP K 2] : Subgroup G :=
  centralizerPerfectCore (modelToG e (anisoTorus hn b c))

theorem minusPieceCore_le_minusNeighbourCore {k : Fin (n - 1)} {I : Finset (Fin (n - 1))}
    (hk : k ∉ I) : minusPieceCore e I ≤ minusNeighbourCore e k :=
  centralizerPerfectCore_anti (modelToG_mono e (minusPairTorus_le_minusPlaneTorus hk))

theorem minusLevelCore_le_minusNeighbourCore {k : Fin (n - 1)} {J : Finset (Fin (n - 1))}
    (hk : k ∉ J) : minusLevelCore e J ≤ minusNeighbourCore e k :=
  centralizerPerfectCore_anti (modelToG_mono e (minusPairTorus_le_minusLevelTorus hk))

theorem modelToG_le_minusNeighbourCore {k : Fin (n - 1)}
    {A : Subgroup (matrixProjectiveDerived (coordinateQuadMinus n K hn b c))}
    (hA : A ≤ centralizer (minusPairTorus hn b c k : Set _)) (hperf : ⁅A, A⁆ = A) :
    modelToG e A ≤ minusNeighbourCore e k :=
  UnitaryPilot.modelToG_le_centralizerPerfectCore e hA hperf

theorem mem_normalizer_minusPieceCore {t : G} (ht : t ∈ centralizer (L : Set G))
    (I : Finset (Fin (n - 1))) : t ∈ normalizer (minusPieceCore e I : Set G) :=
  UnitaryPilot.mem_normalizer_centralizerPerfectCore_modelToG_of_mem_centralizer e ht _

theorem mem_normalizer_minusNeighbourCore {t : G} (ht : t ∈ centralizer (L : Set G))
    (k : Fin (n - 1)) : t ∈ normalizer (minusNeighbourCore e k : Set G) :=
  UnitaryPilot.mem_normalizer_centralizerPerfectCore_modelToG_of_mem_centralizer e ht _

variable [Finite G]

end MinusCores

section LeviFactors

variable {G : Type*} [Group G] {L : Subgroup G} {K : Type} [Field K] [Finite K] [CharP K 2]
  {n : ℕ}

theorem modelToG_minusPairPerp_le_minusNeighbourCore {hn : 1 ≤ n} {b c : K}
    (e : L ≃* matrixProjectiveDerived (coordinateQuadMinus n K hn b c)) (hq : 4 ≤ Nat.card K)
    (hn5 : 5 ≤ n) (hirr : ∀ s : K, s ^ 2 + b * s + c ≠ 0) (k : Fin (n - 1)) :
    modelToG e (minusPairPerp hn b c k) ≤ minusNeighbourCore e k :=
  modelToG_le_minusNeighbourCore e
    ((isHypCoord_coordinateQuadMinus hn b c k).pairPerpOf_le_centralizer hq)
    (Subgroup.isPerfect_iff.1 (isQuasisimple_minusPairPerp hn5 hirr k).1)

end LeviFactors

end CFSG.SeitzReduction.OmegaPilot
