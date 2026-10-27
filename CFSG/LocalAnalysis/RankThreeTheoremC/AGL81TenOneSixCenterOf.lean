module

public import CFSG.LocalAnalysis.RankThreeTheoremC.AGL81TenThreeThreeCasesProof
import CFSG.GH74.GLS.AssemblyComponents
public import CFSG.LocalAnalysis.RankThreeTheoremC.AGL81TenThreeThreeCfg
public import CFSG.Monster.B.TwoA.Census.PermClasses

public section

namespace CFSG.LocalAnalysis.RankThreeTheoremC

open CFSG.Open CFSG.AGLEmbedding CFSG.AGLEmbeddingD2 CFSG.LocalAnalysis.RankThreeTheoremC.Hyp111
open CFSG.Quasithin CFSG.RankThreeCoreUniqueness.Helpers
open Subgroup

variable {G : Type} [Group G] [Finite G]

namespace TenOneSixCenter

theorem conj_mem_of_mk_mem_centralizer {M S : Subgroup G} (hSM : S ≤ M) (hQS : pCoreOf 2 M ≤ S)
    (w : ↥M) (hw : QuotientGroup.mk' (CFSG.pCore 2 ↥M) w ∈ centralizer (barM M S : Set _))
    {s : G} (hs : s ∈ S) : (w : G) * s * (w : G)⁻¹ ∈ S := by
  have hsb : QuotientGroup.mk' (CFSG.pCore 2 ↥M) (⟨s, hSM hs⟩ : ↥M) ∈ barM M S :=
    ⟨⟨s, hSM hs⟩, mem_subgroupOf.mpr hs, rfl⟩
  have hc := mem_centralizer_iff.mp hw _ hsb
  have h1 : QuotientGroup.mk' (CFSG.pCore 2 ↥M)
      (w * ⟨s, hSM hs⟩ * w⁻¹ * (⟨s, hSM hs⟩ : ↥M)⁻¹) = 1 := by
    rw [map_mul, map_mul, map_mul, map_inv, map_inv, ← hc]
    group
  have h3 := hQS (coe_mem_pCoreOf_two_of_mk_eq_one _ h1)
  have heq : (w : G) * s * (w : G)⁻¹ =
      ((w * ⟨s, hSM hs⟩ * w⁻¹ * (⟨s, hSM hs⟩ : ↥M)⁻¹ : ↥M) : G) * s := by
    simp [mul_assoc]
  rw [heq]
  exact S.mul_mem h3 hs

theorem mem_normalizer_of_mk_mem_centralizer {M S : Subgroup G} (hSM : S ≤ M)
    (hQS : pCoreOf 2 M ≤ S) (w : ↥M)
    (hw : QuotientGroup.mk' (CFSG.pCore 2 ↥M) w ∈ centralizer (barM M S : Set _)) :
    (w : G) ∈ normalizer (S : Set G) := by
  have hw' : QuotientGroup.mk' (CFSG.pCore 2 ↥M) w⁻¹ ∈ centralizer (barM M S : Set _) := by
    rw [map_inv]
    exact inv_mem hw
  rw [mem_normalizer_iff]
  intro s
  refine ⟨fun hs => conj_mem_of_mk_mem_centralizer hSM hQS w hw hs, fun hs => ?_⟩
  have := conj_mem_of_mk_mem_centralizer hSM hQS w⁻¹ hw' hs
  simpa [mul_assoc] using this

end TenOneSixCenter

theorem agl81TenOneSixCenterCfg_of (h84 : Asc81bEightFour) (hNX : NoXBlockFor G)
    (h98 : AGL81NineEightFour G) : AGL81TenOneSixCenterCfg G := by
  intro hS p P M H Q K hd L hL h4 z hz
  have hT := hd.toTwoLocalPhaseThree' hS h98
  have hK : Open.IsKGroup ↥M := (hT.toTwoLocalPair.isKGroup_of_isKProper hS.kProper).1
  have hA : Asc81bHyp M (pCoreOf 2 H) := hT.asc81bHyp
  have hNH : normalizer (pCoreOf 2 H : Set G) = H := hT.toTwoLocalPair.normalizer_twoCore_H
  have hO := hT.oddCore_le_centralizer hK h84 hNX
  have hLsn : (barM M L).IsSubnormal := hL.component.2.1.mathlib Subgroup.IsSubnormal.top
  have hZsn : ((center ↥(barM M L)).map (barM M L).subtype).IsSubnormal :=
    Subgroup.IsSubnormal.trans' (Subgroup.Normal.isSubnormal inferInstance) hLsn
  have hZ3 : Nat.card ((center ↥(barM M L)).map (barM M L).subtype) = 3 := by
    rw [card_map_of_injective (barM M L).subtype_injective]
    exact h4.2.1
  have hZO : (center ↥(barM M L)).map (barM M L).subtype ≤
      CFSG.pPrimeCore 2 (↥M ⧸ CFSG.pCore 2 ↥M) :=
    CFSG.GH74.GLS.le_pPrimeCore_of_subnormal 2 hZsn (by rw [hZ3]; norm_num)
  have hzc := hO (hZO ⟨z, hz, rfl⟩)
  obtain ⟨w, hwL, hwz⟩ := z.2
  refine ⟨w, mem_subgroupOf.mpr ⟨?_, mem_subgroupOf.mp hwL⟩, hwz⟩
  rw [← hNH]
  exact TenOneSixCenter.mem_normalizer_of_mk_mem_centralizer hA.twoRadical.1 hA.twoCore_le w
    (hwz ▸ hzc)

end CFSG.LocalAnalysis.RankThreeTheoremC
