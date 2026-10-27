module

public import CFSG.LocalAnalysis.OddStandard.SmallF3.Omega.Sec8SESyl
public import CFSG.LocalAnalysis.OddStandard.SmallF3.Omega.Sec79BA

public section

namespace CFSG.OddStandard.SmallF3.Omega

open Subgroup CFSG.Blueprint

theorem asc82FinkCE_of (hSyl : Asc82FinkSylow) : Asc82FinkCE := by
  intro G _ _ t L S z g B E hE
  let C : Subgroup G := centralizer (E : Set G)
  let X : Subgroup G := normalizer (E : Set G)
  change C = E ⊔ oddCoreIn X ∧ oddCoreIn X ≤ C
  have hY : IsSylow2Of E C := sec8s_E_sylow hSyl hE
  have hEC : E ≤ C := by
    haveI : IsMulCommutative E := hE.elem.1.1
    intro e he
    exact Subgroup.mem_centralizer_iff.mpr fun a ha => setLike_mul_comm ha he
  have hBurn : E ⊔ oddCoreIn C = C :=
    sup_oddCoreIn_of_central_sylow hY
      (fun k hk z hz => Subgroup.mem_centralizer_iff.mp hk z hz)
  have hOC : oddCoreIn C ≤ oddCoreIn X :=
    oddCoreIn_le_of_normal (Subgroup.centralizer_le_normalizer (E : Set G))
      (Subgroup.normal_subgroupOf_centralizer_normalizer (E : Set G))
  have hP2 : IsPGroup 2 E := IsPGroup.of_card hE.elem.2
  have hEX : E ≤ X := Subgroup.le_normalizer
  have hEn : (E.subgroupOf X).Normal := by
    change (E.subgroupOf (Subgroup.normalizer (E : Set G))).Normal
    infer_instance
  have hOn : ((oddCoreIn X).subgroupOf X).Normal := (oddCoreIn_normal X).2
  have hOodd : Odd (Nat.card (oddCoreIn X)) := odd_card_oddCoreIn X
  have hcomm := commute_of_normal_two_odd hEX (oddCoreIn_normal X).1 hEn hOn hP2 hOodd
  have hOCX : oddCoreIn X ≤ C := by
    intro o ho
    exact Subgroup.mem_centralizer_iff.mpr fun e he => hcomm e he o ho
  refine ⟨?_, hOCX⟩
  apply le_antisymm
  · rw [← hBurn]
    exact sup_le le_sup_left (hOC.trans le_sup_right)
  · exact sup_le hEC hOCX

end CFSG.OddStandard.SmallF3.Omega
