module

public import CFSG.LocalAnalysis.RankThreeTheoremC.NGK3PlaneBasic
public import CFSG.LocalAnalysis.RankThreeTheoremC.NGK3PlaneNormal
public import CFSG.LocalAnalysis.RankThreeTheoremC.NGK3PlaneInner
public import CFSG.LocalAnalysis.RankThreeTheoremC.NGK3PlaneOut

public section

namespace CFSG.LocalAnalysis.RankThreeTheoremC

open CFSG.Open CFSG.RankThreeCoreUniqueness.Helpers Subgroup

variable {X : Type} [Group X] [Finite X] {P D : Subgroup X} {z : X}

theorem PlaneData.facts (h : PlaneData P D z) : PlaneFacts P D z := by
  have hcomm := h.comm_mem
  have hcen := h.center_le
  have hω := h.omega_cent
  have hz := h.z_mem hω
  have hinv := h.inv_plane hz
  have hinner := h.exists_inner hcomm hcen
  have hcyc := h.cent_cyclic
  exact ⟨hcomm, hcen, hω, hcyc, hz, hinv, h.inf_plane hω hcyc hz hinv hinner hcomm, hinner,
    h.eq_of_comm, h.not_normal hinner hcomm⟩

end CFSG.LocalAnalysis.RankThreeTheoremC
