module

public import CFSG.LocalAnalysis.ComponentClassification.GS79bSec5.FieldStandardSourceInputs
public import CFSG.LocalAnalysis.ComponentClassification.GrSLitL34Sec5SStdSplit
import CFSG.LocalAnalysis.ComponentClassification.GS79bSec5.FieldStandardCoverExclusion

public section

open Subgroup

namespace CFSG.ComponentClassification.GrSLit.L34Sec5S

open CFSG.LocalAnalysis.ComponentInitial CFSG.LocalAnalysis.EvenBN.LinearThree
open CFSG.OddStandard.Seitz77 (Datum)
open CFSG.ComponentClassification.GS79bSec5
open CFSG.ComponentClassification.UnbalancedLayer

theorem l34FieldStandardExclusion_holds :
    L34FieldStandardExclusion := by
  intro G _ _ hG b J hb hJb _ hnL hst hO
  obtain ⟨n, hn, -, hL⟩ := hnL
  have hbase := hG
  obtain ⟨hsimple, hna, hK, -, -, -, -, -⟩ := hG
  have hq : IsQuasisimple J := hst.1
  have hO' : pPrimeCore 2 ↥J ≤ center ↥J := by
    intro y hy
    obtain ⟨w, hw, hwy⟩ := hO ⟨y, hy, rfl⟩
    rwa [← Subtype.ext hwy]
  have heq := GrS5.fusionZStar_eq_center_of_le hq.1.commutator_eq_top hO'
  have hmodel : CFSG.Blueprint.LieModel (J ⧸ center J) .PSL 3 2 n :=
    hL.of_mulEquiv (QuotientGroup.quotientMulEquivOfEq heq)
  obtain ⟨hZ, hcyc, F, _, _, _, hF, e, φ, hφsurj, hφproj⟩ :=
    exists_ordinary_cover_of_l34_field hbase J
      (CFSG.StandardSubgroupAPI.isStandardSubgroup_iff_assembly.mp hst) n hn hmodel
  have hF16 : 16 ≤ Nat.card F := by
    rw [hF]
    calc 16 = 2 ^ 4 := by norm_num
      _ ≤ 2 ^ n := Nat.pow_le_pow_right (by norm_num) hn
  have hbC : b ∈ centralizer (J : Set G) := by
    rw [mem_centralizer_iff]
    intro j hj
    exact mem_centralizer_singleton_iff.mp (hJb hj)
  exact false_of_standard_of_cover hK hna hF16 hF J
    (CFSG.StandardSubgroupAPI.isStandardSubgroup_iff_standardComponentIsStandard.mp hst) hZ e φ
    hφsurj hφproj hcyc b hb hbC

end CFSG.ComponentClassification.GrSLit.L34Sec5S
