module

public import CFSG.ClassicalInvolution.Q3.Q3E8Attach
public import CFSG.ClassicalInvolution.Q3.Q3E8R1

public section

namespace CFSG.ClassicalInvolution.Q3.Q3W

open CFSG.Open hiding StatedLieTag StatedLieAdmissible
open CFSG.ClassicalInvolution CFSG.ClassicalInvolution.Generic CFSG.ClassicalInvolution.RouteD
  CFSG.ClassicalInvolution.RouteD.Gaps CFSG.Assembly.LowTwoRank CFSG.LieType.Universal
  CFSG.LieType CFSG.LieType.RootSystem CFSG.LieType.CurtisTits CFSG.Timmesfeld
open CFSG.ClassicalInvolution.WeakCT (LinearBlockStandardPair)
open scoped MatrixGroups commutatorElement

set_option linter.unusedSectionVars false


theorem partnerExists3E8_proved (h3 : OddThreeFreeInput) (hLG : E8LayerGeom3)
    (hT : E8PartnerToral3) (hX : E8ClassExcluded3) : PartnerExists3E8Input := by
  intro G _ _ _ hnab K z hR hshape
  obtain ⟨c⟩ := nonempty_etctx3_E7 h3 hR hshape
  obtain ⟨ι, hι, D, -⟩ := id hshape
  have hsingle : ∀ L ∈ conjClass3 K, ∃ g : G, L = conjSub g K := by
    rintro L ⟨g, rfl⟩
    exact ⟨g, rfl⟩
  exact exists_partnerAt_E8_proved (Gaps.fundNoncentral 3) c hsingle D hLG
    (hT G hnab K z hR hshape c)
    (fun β hβ t htβ hKβ ht g p₀ hg => hX G hnab K z hR hshape c β hβ t htβ hKβ ht g p₀ hg)

theorem piece3E8_proved (h3 : OddThreeFreeInput) (hLG : E8LayerGeom3) (hT : E8PartnerToral3)
    (hX : E8ClassExcluded3) : Piece3E8 :=
  piece3E8_of_exists h3 (partnerExists3E8_proved h3 hLG hT hX)

theorem piece3E8_of_facts (h3 : OddThreeFreeInput) (hSP : E7SignPerp3) (hT : E8PartnerToral3)
    (hB8 : TypeE8.E7FrameRelations 3 1) (hB9 : TypeE8.E7FrameInvolutions 3 1)
    (hB7 : TypeE8.E7PerpA2StarFree 3 1) (hLayer : TypeE8.E7LayerEquiv 3 1)
    (hConn : TypeE8.Fund12Connected 3 1) (hRow : E8D8Row3)
    (hD8 : TypeE8.D8NoThreeAdjPairs 3 .POmegaPlus 8 1) (hP1x : E8P1x3)
    (hR2 : E8R2Excluded3) : Piece3E8 :=
  piece3E8_proved h3 (e8LayerGeom3_of_signPerp hSP) hT
    (e8ClassExcluded3_of_packages hB8 hB9 hB7 hLayer hConn hRow hD8 hP1x e8R1Excluded3 hR2)

end CFSG.ClassicalInvolution.Q3.Q3W
