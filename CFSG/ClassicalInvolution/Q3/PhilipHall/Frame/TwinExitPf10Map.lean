module

public import CFSG.ClassicalInvolution.Q3.PhilipHall.Frame.LiftTransfer
public import CFSG.ClassicalInvolution.Q3.PhilipHall.Frame.FStarBasic

public section

set_option linter.unusedSectionVars false

namespace CFSG.ClassicalInvolution.Q3.PhilipHall.Frame.TwinExitPf10

open CFSG CFSG.Open CFSG.ClassicalInvolution CFSG.ClassicalInvolution.Generic
open CFSG.ClassicalInvolution.Asc77 CFSG.ClassicalInvolution.Balance CFSG.ClassicalInvolution.Disconnected.AschTight
open CFSG.ClassicalInvolution.Q3 CFSG.ClassicalInvolution.Uniform CFSG.ClassicalInvolution.Uniform.U4 CFSG.ClassicalInvolution.Q3.Q3T6X CFSG.ClassicalInvolution.Q3.TL4
open CFSG.ClassicalInvolution.Q3.PhilipHall.Frame


section Map

variable {X X' : Type} [Group X] [Group X']

theorem isUniqueInvolution_map (σ : X ≃* X') {K : Subgroup X} {z : X} (h : IsUniqueInvolution K z) :
    IsUniqueInvolution (K.map σ.toMonoidHom) (σ z) where
  mem := ⟨z, h.mem, rfl⟩
  ne_one := fun h1 => h.ne_one (σ.injective (by simpa using h1))
  sq := by rw [← map_mul, h.sq, map_one]
  unique := by
    rintro _ ⟨y, hy, rfl⟩ hy2
    have : y * y = 1 := σ.injective (by simpa [map_mul] using hy2)
    rcases h.unique y hy this with h1 | h1
    · left; simp [h1]
    · right; simp [h1]

omit [Group X'] in
theorem oddCoreIn_map_equiv [Finite X] {X' : Type} [Group X'] (σ : X ≃* X') (A : Subgroup X) :
    (oddCoreIn A).map σ.toMonoidHom = oddCoreIn (A.map σ.toMonoidHom) := by
  let e : ↥A ≃* ↥(A.map σ.toMonoidHom) := A.equivMapOfInjective σ.toMonoidHom σ.injective
  have hO : (componentClassificationOddCore ↥A).map e.toMonoidHom =
      componentClassificationOddCore ↥(A.map σ.toMonoidHom) :=
    CFSG.ComponentClassification.OddCore.equiv_invariant e
  have hcomp : σ.toMonoidHom.comp A.subtype = (A.map σ.toMonoidHom).subtype.comp e.toMonoidHom := by
    ext x
    rfl
  unfold oddCoreIn
  rw [Subgroup.map_map, hcomp, ← Subgroup.map_map, hO]

end Map


section Lift

variable {X X' : Type} [Group X] [Group X'] [Finite X]

theorem satU_map (σ : X ≃* X') (L : Subgroup X) (u : X) :
    satU (.sl2 3 1) (L.map σ.toMonoidHom) (σ u) = (satU (.sl2 3 1) L u).map σ.toMonoidHom := by
  rw [satU_of_isSolvableType solvableType_three, satU_of_isSolvableType solvableType_three,
    Subgroup.map_sup, ← map_centralizer_singleton_mulEquiv₃ σ u, oddCoreIn_map_equiv]

theorem isLiftOf_map (σ : X ≃* X') {J L : Subgroup X} {u : X} (h : IsLiftOf J L u) :
    IsLiftOf (J.map σ.toMonoidHom) (L.map σ.toMonoidHom) (σ u) :=
  ⟨isUniqueInvolution_map σ h.inv, Subgroup.map_mono h.le, h.member.map_mulEquiv σ⟩

theorem liftFam_map {Φ : Set (Subgroup X)} (σ : X ≃* X)
    (hσ : ∀ K ∈ Φ, K.map σ.toMonoidHom ∈ Φ) {M : Subgroup X} (hM : M ∈ liftFam Φ) :
    M.map σ.toMonoidHom ∈ liftFam Φ := by
  obtain ⟨J, hJ, L, u, hL, rfl⟩ := hM
  refine ⟨J.map σ.toMonoidHom, hσ J hJ, L.map σ.toMonoidHom, σ u, isLiftOf_map σ hL, ?_⟩
  rw [satU_map]

theorem map_omegaGen_liftFam {Φ : Set (Subgroup X)} (σ : X ≃* X)
    (hσ : ∀ K ∈ Φ, K.map σ.toMonoidHom ∈ Φ) :
    (omegaGen (liftFam Φ)).map σ.toMonoidHom = omegaGen (liftFam Φ) := by
  have hle : (omegaGen (liftFam Φ)).map σ.toMonoidHom ≤ omegaGen (liftFam Φ) := by
    unfold omegaGen
    rw [Subgroup.map_iSup]
    refine iSup_le fun M => ?_
    rw [Subgroup.map_iSup]
    refine iSup_le fun hM => ?_
    exact le_omegaGen (liftFam_map σ hσ hM)
  exact Subgroup.eq_of_le_of_card_ge hle (le_of_eq
    (Subgroup.card_map_of_injective (show Function.Injective σ.toMonoidHom from σ.injective)).symm)

end Lift

end CFSG.ClassicalInvolution.Q3.PhilipHall.Frame.TwinExitPf10
