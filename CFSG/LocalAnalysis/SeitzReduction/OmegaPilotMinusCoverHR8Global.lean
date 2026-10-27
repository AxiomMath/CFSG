module

public import CFSG.LocalAnalysis.SeitzReduction.OmegaPilotHR8Kind
public import CFSG.ClassicalInvolution.SmallCases.UpgradeCoverClassical
public import CFSG.LocalAnalysis.SeitzReduction.OmegaPilotHR8Field
public import CFSG.LocalAnalysis.SeitzReduction.TwistedE6PilotFieldNormalizeBasic
public import CFSG.LocalAnalysis.SeitzReduction.TwistedE6PilotFieldYModel

public section

namespace CFSG.SeitzReduction.OmegaPilot

open Subgroup CFSG.Blueprint CFSG.Assembly.LowTwoRank
open CFSG.Quasithin (perfectCore)
open CFSG.ComponentClassification.CatalogueBOrthogonalSemilinear (matrixProjectiveDerived)
open CFSG.ComponentClassification.CatalogueBOrthogonalPointData (coordinateQuadMinus)
open CFSG.RankThree.PartOne.KCOrthogonalSubfield (fieldAutT)
open CFSG.SeitzReduction.TwistedE6Pilot (coordinateQuadMinus_fieldMap_of_fixed)
open CFSG.SeitzReduction.UnitaryPilot (modelToG)

variable {G : Type} [Group G] [Finite G] {L : Subgroup G}

omit [Finite G] in
theorem exists_fieldAlt_of_rowAt_tag {t : G} {m f : ℕ} {tag : StatedLieTag} {X D : Subgroup G}
    (h8 : OmegaHR8FieldAt t m f tag X D) (hrow : OmegaRowAt t X D .field)
    (hDq : CFSG.Open.IsQuasisimple ((D.subgroupOf (centralizer (X : Set G))).map
      (QuotientGroup.mk' (oddCore (centralizer (X : Set G)))))) :
    ∃ htX : t ∈ centralizer (X : Set G),
      ∃ Kc : Subgroup (centralizer (X : Set G) ⧸ oddCore (centralizer (X : Set G))),
        IsComponent Kc ∧
        OmegaNeighbourAlternativeField
          (QuotientGroup.mk' (oddCore (centralizer (X : Set G))) ⟨t, htX⟩)
          ((D.subgroupOf (centralizer (X : Set G))).map
            (QuotientGroup.mk' (oddCore (centralizer (X : Set G))))) Kc m f tag ∧
        Kc.map (MulAut.conj
          (QuotientGroup.mk' (oddCore (centralizer (X : Set G))) ⟨t, htX⟩)).toMonoidHom = Kc := by
  obtain ⟨htX, -, hall, -⟩ := h8
  obtain ⟨htX', Kc, hKc, hDK, hr⟩ := hrow
  have hKt := hr.1 rfl
  refine ⟨htX, Kc, hKc, hall Kc hKc ?_, hKt⟩
  have hDle : (D.subgroupOf (centralizer (X : Set G))).map
      (QuotientGroup.mk' (oddCore (centralizer (X : Set G)))) ≤ Kc := by
    have h1 := hDK
    rw [hKt, sup_idem] at h1
    exact h1
  have hperf : ⁅(D.subgroupOf (centralizer (X : Set G))).map
      (QuotientGroup.mk' (oddCore (centralizer (X : Set G)))),
      (D.subgroupOf (centralizer (X : Set G))).map
        (QuotientGroup.mk' (oddCore (centralizer (X : Set G))))⁆ =
      (D.subgroupOf (centralizer (X : Set G))).map
        (QuotientGroup.mk' (oddCore (centralizer (X : Set G)))) :=
    SymplecticPilot.commutator_eq_self_of_isQuasisimple hDq
  intro hbot
  apply ne_bot_of_isQuasisimple hDq
  rw [← hperf, eq_bot_iff, ← hbot]
  exact Subgroup.commutator_mono le_rfl hDle

end CFSG.SeitzReduction.OmegaPilot
