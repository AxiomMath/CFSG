module

public import CFSG.CGT.PushingUpLit.SolKNA.R4.TwinEdgeFam
public import CFSG.CGT.PushingUpLit.SolKNA.R4.TwinEdgeLift
public import CFSG.CGT.PushingUpLit.SolKNA.R4.TwinEdgeSec

public section

namespace CFSG.CGT.PushingUpLit.SolKNA.R4

open CFSG CFSG.Open CFSG.ClassicalInvolution CFSG.ClassicalInvolution.Generic
open CFSG.ClassicalInvolution.Asc77 CFSG.ClassicalInvolution.Disconnected.AschTight
open CFSG.ClassicalInvolution.Q3 CFSG.ClassicalInvolution.Q3.TA3
open CFSG.ClassicalInvolution.Q3.PhilipHall.Frame
open CFSG.ClassicalInvolution.Q3.PhilipHall.Frame.Thm4Twin

section Cit3

theorem thm4TwinEdgelessModelR_of_classUnique {r n : ℕ} (hr : 4 ≤ r) (h4 : NoQ16E4)
    (hA : CIT3Below n) (hT : Thm1RTwinBelowR r n) (hB : TightBelowR r n)
    (h6 : ∀ m, TightLargeEdgeSR r m) (hList : SmallListR) (hO : NoDatumOtherR r)
    (hL2 : EdgelessClassUniqueR r SmallL2) (hL3 : EdgelessClassUniqueR r SmallL3Ne3)
    (hU3 : EdgelessClassUniqueR r SmallU3Ne3) : Thm4TwinEdgelessModelR r n := by
  intro G _ _ hG J L L₀ hc W hJW hWs hWg htw hedge
  have hJΔ : J ∈ CoreAssembly.conjClass J ∪ CoreAssembly.conjClass L :=
    Or.inl (CoreAssembly.mem_conjClass_self J)
  have hLΔ : L ∈ CoreAssembly.conjClass J ∪ CoreAssembly.conjClass L :=
    Or.inr (CoreAssembly.mem_conjClass_self L)
  obtain ⟨Y, _, _, ι, R, S, t, hι, hT₀, hd, hcl, -, -, hnO, -, hcard⟩ :=
    hc.exists_embSec hr hJΔ hJW hWs hWg htw hedge
  have hLs := hc.exists_edgeless_section hr h4 hT hB hG hLΔ
  haveI := hc.normal
  have hTs := isSimpleGroup_socle hc.isComp.1 hc.centralizerEq
  have hTab := exists_ne_comm_socle hc.isComp.1 hc.centralizerEq
  have hTC := centralizer_socle_eq_bot hc.isComp.1 hc.centralizerEq
  have h4gen := twoSubgroupsFourGenerated_socle hr hA hB h6 (socleOf L₀) hTs hTab hTC
    (lt_of_le_of_lt hcard hG) ι hι hT₀ hd hcl hnO
  have hfam := edgelessFamily_of_embedded hr hList hO (socleOf L₀) hTs hTab hTC h4gen ι hι hT₀
    hd hcl
  have hJs : ∃ W : Subgroup G, EdgelessSection J W := ⟨W, hJW, hWs, hWg, htw, hedge⟩
  obtain ⟨a, ha⟩ : ∃ a : G ⧸ Subgroup.center G,
      J.map (QuotientGroup.mk' (Subgroup.center G)) =
        conjSub a (L.map (QuotientGroup.mk' (Subgroup.center G))) := by
    rcases hfam with hP | hP | hP
    · exact hL2 hr G J L L₀ hc hP hJs hLs
    · exact hL3 hr G J L L₀ hc hP hJs hLs
    · exact hU3 hr G J L L₀ hc hP hJs hLs
  obtain ⟨g, rfl⟩ := QuotientGroup.mk'_surjective (Subgroup.center G) a
  have hJM : J.map (QuotientGroup.mk' (Subgroup.center G)) =
      (conjSub g L).map (QuotientGroup.mk' (Subgroup.center G)) := by
    rw [ha, TwistQ.conjSub_map]
  obtain ⟨x, hxJ, y, hyJ, h4d⟩ := hc.exists_commutator_four_dvd hr hJΔ
  have hJe := eq_of_map_center_eq hc.min.hyp.hyp hJΔ (Or.inr ⟨g, rfl⟩) hJM hxJ hyJ h4d
  exact hc.min.notConj ⟨g⁻¹, by rw [hJe, conjSub_inv_conjSub]⟩

end Cit3

end CFSG.CGT.PushingUpLit.SolKNA.R4
