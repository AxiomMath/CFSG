module

public import CFSG.LocalAnalysis.RankThreeTheoremC.GL83P3U3RemarkE
public import CFSG.LocalAnalysis.RankThreeTheoremC.GL83P3U3RemarkTorus
public import CFSG.LocalAnalysis.RankThreeTheoremC.GL83P3U3Proof
import CFSG.LocalAnalysis.RankThreeTheoremC.GL83Generic4_1P3U3Proved

public section

namespace CFSG.LocalAnalysis.RankThreeTheoremC

open CFSG.Open CFSG.RankThreeCoreUniqueness.Helpers CFSG.ABGLocalTools Subgroup
open CFSG.LocalAnalysis.RankThreeTheoremC.GL83P3U3RemarkAux
open CFSG.LocalAnalysis.RankThreeTheoremC.Generic49U3
  (u3T u3S TypeTStruct TypeSDecomp typeBorelMax_u3)

variable {G : Type} [Group G] [Finite G]

theorem gl83P3U3_remark_of_kfacts (hS : Setting G) (hD1 : TheoremD1 G) (hU0 : FullCoreLocal G)
    (hInn : KFactInnerAction) (hWC : KFactWeakClosure) (hHeis3 : KFactWeakClosureHeisThree) :
    GL83GenericPrimeThreeU3RemarkCond G := by
  intro p hp P M hM hfail hIH x hgen hp3 J hJC hCJ hperf hlt hmin hnot Q _ ψ hψ hker hQ h34
  subst hp3
  haveI : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  have hc : PointConfig3 (fun p K _ => IsU3Pred p K) G 3 P M x J :=
    ⟨hp, hM, hfail, hIH, hgen, rfl, hJC, hCJ, hperf, hlt, hmin, hnot,
      ⟨Q, inferInstance, ψ, hψ, hker, hQ⟩⟩
  obtain ⟨hPx, hTcard, hTexp, hTnc, ⟨Z, hZc, hxZ, hZcomm, hTZ, hPZ⟩, hwc⟩ := h34
  have hS' : u3S P x = (P : Subgroup G) := inf_eq_left.mpr hPx
  have hT : u3T P x J = (P : Subgroup G) ⊓ J := by rw [u3T, hS']
  have hx1 : x ≠ 1 := hgen.2.1.2.1
  have hxJ : x ∉ J := by
    intro hxJ
    have hxT : x ∈ ((P : Subgroup G) ⊓ J) ⊓ Z := ⟨⟨hgen.1, hxJ⟩, hxZ⟩
    rw [hTZ, Subgroup.mem_bot] at hxT
    exact hx1 hxT
  have hTstr : TypeTStruct 3 P x J := by
    rw [TypeTStruct, hT]
    exact ⟨hTcard, hTexp, hTnc, hxJ⟩
  have hZP : Z ≤ (P : Subgroup G) := by
    rw [hPZ]
    exact le_sup_right
  have hSdec : TypeSDecomp 3 P x J := by
    rw [TypeSDecomp, hT, hS']
    exact ⟨Z, hZc, hxZ, hZP, fun z hz t ht => (hZcomm t ht z hz).symm, hTZ, hPZ.symm⟩
  have key := u3_normal_core_proof_gen3 hS hD1 hU0 hInn hWC hHeis3 hc ⟨hPx, hwc⟩ hTstr hSdec
    (fun K _ _ hK _ S hS => u3AutData_proved K hK S hS)
    typeTorusIrred_u3_three typeTorusFpf_u3_three typeTorusOnCenter_u3_three typeBorelMax_u3
  rw [hT] at key
  exact key

end CFSG.LocalAnalysis.RankThreeTheoremC
