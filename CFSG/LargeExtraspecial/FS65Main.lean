module

public import CFSG.LargeExtraspecial.S14SMJDefs
public import CFSG.LargeExtraspecial.FS65SixThree
public import CFSG.LargeExtraspecial.FS65Exist

public section

attribute [-instance] instAddCommGroupOfIsSimpleAddGroupOfIsNilpotent
  instCommGroupOfIsSimpleGroupOfIsNilpotent

namespace CFSG.LargeExtraspecial

open Subgroup CFSG.Open

namespace Setting

variable {G : Type} [Group G] [Finite G] (S : Setting G)

theorem z_mem_center_of_isolated (hO : timmesfeldOddCore G = ⊥)
    (hiso : ∀ g : G, g * S.z * g⁻¹ ∈ S.M → g * S.z * g⁻¹ = S.z) : S.z ∈ center G := by
  obtain ⟨N, hNn, hNodd, hN⟩ := S10.exists_odd_normal_of_isolated S.z S.z_ne_one S.z_mul_z
    fun g hg => hiso g (S.mem_M_iff.mpr hg)
  have hNle : N ≤ timmesfeldOddCore G :=
    le_sSup (show N ∈ {N : Subgroup G | N.Normal ∧ Odd (Nat.card N)} from ⟨hNn, hNodd⟩)
  rw [hO, le_bot_iff] at hNle
  rw [mem_center_iff]
  intro g
  have h := hN g
  rw [hNle, mem_bot, mul_inv_eq_one] at h
  calc g * S.z = g * S.z * g⁻¹ * g := by group
    _ = S.z * g := by rw [h]

omit [Finite G] in
theorem aschbacherHyp_of_mem_center (hz : S.z ∈ center G) : S.AschbacherHyp := by
  intro e _ _
  have hzc : ∀ c : G, c * S.z = S.z * c := fun c => mem_center_iff.mp hz c
  refine S.zInOTwo_of_le (P := zpowers S.z) (zpowers_le.mpr
      (mem_centralizer_singleton_iff.mpr (hzc e).symm)) ?_
    (IsPGroup.of_card (n := 1) (by rw [Nat.card_zpowers, S.orderOf_z, pow_one]))
    (mem_zpowers _)
  intro c _ p hp
  obtain ⟨m, rfl⟩ := mem_zpowers_iff.mp hp
  have hcm : c * S.z ^ m = S.z ^ m * c := (Commute.zpow_right (hzc c) m).eq
  exact mem_zpowers_iff.mpr ⟨m, by rw [hcm, mul_inv_cancel_right]⟩

theorem aschbacherHyp_of_not_isolated (h63 : S14.SmithSixThreeGenInput) (hn : 3 ≤ S.width)
    (hW : ∀ g : G, g * S.z * g⁻¹ ∈ S.QG → g * S.z * g⁻¹ = S.z)
    (hiso : ∃ g : G, g * S.z * g⁻¹ ∈ S.M ∧ g * S.z * g⁻¹ ≠ S.z) : S.AschbacherHyp :=
  S.aschbacherHyp_of_smith hW (h63 G S hn hW) (S.exists_four_le_card_inf_Qa_gen hn hW hiso)

theorem aschbacherHyp_of_oddCore (h63 : S14.SmithSixThreeGenInput) (hn : 3 ≤ S.width)
    (hO : timmesfeldOddCore G = ⊥)
    (hW : ∀ g : G, g * S.z * g⁻¹ ∈ S.QG → g * S.z * g⁻¹ = S.z) : S.AschbacherHyp := by
  by_cases hiso : ∃ g : G, g * S.z * g⁻¹ ∈ S.M ∧ g * S.z * g⁻¹ ≠ S.z
  · exact S.aschbacherHyp_of_not_isolated h63 hn hW hiso
  · push Not at hiso
    exact S.aschbacherHyp_of_mem_center (S.z_mem_center_of_isolated hO hiso)

end Setting

namespace S14

theorem fSmithSixFiveOddInput_of_smithSixThreeGen (h63 : SmithSixThreeGenInput) :
    FSmithSixFiveOddInput :=
  fun _ _ _ T hn hO hW => T.aschbacherHyp_of_oddCore h63 hn hO hW

end S14

end CFSG.LargeExtraspecial
