module

public import CFSG.LocalAnalysis.SeitzReduction.OmegaPilotCoresForms

public section

namespace CFSG.SeitzReduction.OmegaPilot

open Subgroup
open CFSG.RankThree.Classical2 (orthDerived)
open CFSG.ComponentClassification.CatalogueBOrthogonalSemilinear (matrixProjectiveDerived)
open CFSG.ComponentClassification.CatalogueBOrthogonalPointData
  (minusIndexEquiv coordinateQuadMinus)
open CFSG.SeitzReduction.F4Pilot (centralizerPerfectCore)
open CFSG.SeitzReduction.UnitaryPilot (modelToG modelToG_mono)

section Fix

variable {K : Type*} [Field K] {ι : Type*} [DecidableEq ι] {m : ℕ}

theorem frameLin_single_of_forall_ne {a b : Fin m → ι} (t : Fin m → Kˣ) {u : ι}
    (hua : ∀ k, u ≠ a k) (hub : ∀ k, u ≠ b k) :
    frameLin a b t (Pi.single u 1) = Pi.single u 1 := by
  funext i
  rw [frameLin_apply]
  by_cases hiu : i = u
  · subst hiu
    rw [frameEntry_of_forall_ne t hua hub, Units.val_one, one_mul]
  · rw [Pi.single_eq_of_ne hiu, mul_zero]

end Fix

section Minus

variable {K : Type} [Field K] {n : ℕ} (hn : 1 ≤ n) (b c : K)

include hn in
theorem anisoCoordLeft_ne_minusFrameLeft (k : Fin (n - 1)) :
    anisoCoordLeft hn ≠ minusFrameLeft hn k := fun h => by
  have := (minusIndexEquiv n hn).injective h
  simp at this

include hn in
theorem anisoCoordLeft_ne_minusFrameRight (k : Fin (n - 1)) :
    anisoCoordLeft hn ≠ minusFrameRight hn k := fun h => by
  have := (minusIndexEquiv n hn).injective h
  simp at this

include hn in
theorem anisoCoordRight_ne_minusFrameLeft (k : Fin (n - 1)) :
    anisoCoordRight hn ≠ minusFrameLeft hn k := fun h => by
  have := (minusIndexEquiv n hn).injective h
  simp at this

include hn in
theorem anisoCoordRight_ne_minusFrameRight (k : Fin (n - 1)) :
    anisoCoordRight hn ≠ minusFrameRight hn k := fun h => by
  have := (minusIndexEquiv n hn).injective h
  simp at this

theorem minusFrameTorus_le_anisoPerp (P : Subgroup (Fin (n - 1) → Kˣ)) :
    minusFrameTorus hn b c P ≤ anisoPerp hn b c := by
  refine map_mono fun x hx => ?_
  obtain ⟨t, -, ht⟩ := hx
  refine ⟨?_, ?_⟩
  · have hx' : (x : (Fin (2 * n) → K) ≃ₗ[K] (Fin (2 * n) → K)) =
        frameLin (minusFrameLeft hn) (minusFrameRight hn) t := ht.symm
    change (x : (Fin (2 * n) → K) ≃ₗ[K] (Fin (2 * n) → K)) (Pi.single (anisoCoordLeft hn) 1) = _
    rw [hx']
    exact frameLin_single_of_forall_ne t (anisoCoordLeft_ne_minusFrameLeft hn)
      (anisoCoordLeft_ne_minusFrameRight hn)
  · have hx' : (x : (Fin (2 * n) → K) ≃ₗ[K] (Fin (2 * n) → K)) =
        frameLin (minusFrameLeft hn) (minusFrameRight hn) t := ht.symm
    change (x : (Fin (2 * n) → K) ≃ₗ[K] (Fin (2 * n) → K)) (Pi.single (anisoCoordRight hn) 1) = _
    rw [hx']
    exact frameLin_single_of_forall_ne t (anisoCoordRight_ne_minusFrameLeft hn)
      (anisoCoordRight_ne_minusFrameRight hn)

variable [Finite K] [CharP K 2] {hn b c}

theorem minusFrameTorus_le_centralizer_anisoTorus (hirr : ∀ s : K, s ^ 2 + b * s + c ≠ 0)
    (P : Subgroup (Fin (n - 1) → Kˣ)) :
    minusFrameTorus hn b c P ≤ centralizer (anisoTorus hn b c :
      Set (matrixProjectiveDerived (coordinateQuadMinus n K hn b c))) :=
  (minusFrameTorus_le_anisoPerp hn b c P).trans
    (le_centralizer_iff.1 (anisoTorus_le_centralizer_anisoPerp hn hirr))

variable {G : Type*} [Group G] {L : Subgroup G}
  (e : L ≃* matrixProjectiveDerived (coordinateQuadMinus n K hn b c))

theorem mem_normalizer_anisoNeighbourCore_of_mem (hirr : ∀ s : K, s ^ 2 + b * s + c ≠ 0)
    {P : Subgroup (Fin (n - 1) → Kˣ)} {x : matrixProjectiveDerived (coordinateQuadMinus n K hn b c)}
    (hx : x ∈ minusFrameTorus hn b c P ∨ x ∈ anisoTorus hn b c) :
    ((e.symm x : L) : G) ∈ normalizer (anisoNeighbourCore e : Set G) := by
  refine UnitaryPilot.symm_mem_normalizer_centralizerPerfectCore_modelToG e
    (centralizer_le_normalizer _ ?_)
  rcases hx with hx | hx
  · exact minusFrameTorus_le_centralizer_anisoTorus hirr P hx
  · exact anisoTorus_le_centralizer_self hn hirr hx

end Minus

end CFSG.SeitzReduction.OmegaPilot
