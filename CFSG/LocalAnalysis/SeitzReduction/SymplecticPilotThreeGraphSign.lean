module

public import CFSG.LocalAnalysis.SeitzReduction.SymplecticPilotThreeGraphOmega
public import CFSG.LocalAnalysis.SeitzReduction.OmegaPilotEightEndSign

public section

namespace CFSG.SeitzReduction.SymplecticPilot

open Subgroup
open CFSG.ComponentClassification.UnbalancedCatalog
  CFSG.ComponentClassification.UnbalancedCatalog.OmegaRadical
open CFSG.ComponentClassification.CatalogueBOrthogonalPointData
open CFSG.ComponentClassification.CatalogueBOrthogonalSemilinear

theorem omegaPlusSignInput_four : OmegaPlusSignInput 4 := by
  intro F _ _ _
  obtain ⟨hX, hX'⟩ := OmegaPilot.symmetryAut_lastPlaneVec_smul_plusCX (F := F)
  set g₀ := symmetryAut (coordinateQuadPlus 4 F) (OmegaPilot.lastPlaneVec 3) with hg₀
  have hg₀im : g₀ ∈ matrixProjectiveImage (coordinateQuadPlus 4 F) := ⟨_, rfl⟩
  have hg₀F := (OmegaPilot.mem_image_iff_smul_pointFamily le_rfl g₀).1 hg₀im
  obtain ⟨E, hE2, hEInn, hEg⟩ := OmegaPilot.exists_index_two_of_swap hg₀F hX hX'
  have : E.Normal := Subgroup.normal_of_index_eq_two hE2
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hQ : Nat.card (MulAut (matrixProjectiveDerived (coordinateQuadPlus 4 F)) ⧸ E) = 2 := hE2
  have hZ : Nat.card (Multiplicative (ZMod 2)) = 2 := by
    rw [Nat.card_eq_fintype_card, Fintype.card_multiplicative, ZMod.card]
  set φ := mulEquivOfPrimeCardEq hQ hZ
  refine ⟨OmegaPilot.lastPlaneVec 3, OmegaPilot.coordinateQuadPlus_lastPlaneVec,
    φ.toMonoidHom.comp (QuotientGroup.mk' E), fun x => ?_, fun h => ?_⟩
  · have h0 : QuotientGroup.mk' E (MulAut.conj x) = 1 :=
      (QuotientGroup.eq_one_iff _).2 (hEInn x)
    rw [MonoidHom.comp_apply, h0, map_one]
  · apply hEg
    have h1 : QuotientGroup.mk' E g₀ = 1 := by
      apply φ.injective
      rw [map_one]
      exact h
    exact (QuotientGroup.eq_one_iff _).1 h1

end CFSG.SeitzReduction.SymplecticPilot
