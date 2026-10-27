module

public import CFSG.Assembly.RankThreeEvenDefs
public import CFSG.ClassicalInvolution.Asc77.AscT7AHyp51
public import CFSG.ClassicalInvolution.AschTight.S19COrd
public import CFSG.ClassicalInvolution.SmallCases.Hat2A7FactsInputs
public import CFSG.Fischer.Classification.Recognition.PSU6
public import CFSG.LocalAnalysis.RankTwoShapes.UnitaryFour.Bridge

public section

namespace CFSG.ClassicalInvolution.A7Q.Vertex

open CFSG.Open CFSG.ClassicalInvolution CFSG.ClassicalInvolution.Generic
  CFSG.ClassicalInvolution.Asc77 CFSG.ClassicalInvolution.Disconnected
  CFSG.ClassicalInvolution.Disconnected.AschTight CFSG.ClassicalInvolution.Hat2A7
open CFSG.ClassicalInvolution.Balance (OddQuot oddQuotMk modOdd oddCoreIn)
open CFSG.ClassicalInvolution.Balance.Bootstrap (trivialOnQuot)

variable {G : Type} [Group G] [Finite G]

theorem not_mem_modOdd_zpowers {c w : G} (hc2 : c * c = 1) (hc1 : c ≠ 1) (hw2 : w * w = 1)
    (hw1 : w ≠ 1) (hwc : w ≠ c) (hwC : w ∈ Subgroup.centralizer ({c} : Set G)) :
    oddQuotMk c ⟨w, hwC⟩ ∉ modOdd c (Subgroup.zpowers c) := by
  rintro ⟨k, hk, hkw⟩
  have hcw : c * w = w * c := (Subgroup.mem_centralizer_singleton_iff.mp hwC).symm
  have hci : c⁻¹ = c := inv_eq_of_mul_eq_one_right hc2
  have hk01 : (k : G) = 1 ∨ (k : G) = c :=
    T7A.eq_one_or_eq_of_mem_zpowers (orderOf_eq_prime (by rw [pow_two]; exact hc2) hc1)
      (Subgroup.mem_subgroupOf.mp hk)
  have hq : oddQuotMk c (k⁻¹ * ⟨w, hwC⟩) = 1 := by rw [map_mul, map_inv, hkw, inv_mul_cancel]
  rcases hk01 with h | h
  · have hk1 : k = 1 := Subtype.ext h
    rw [hk1, inv_one, one_mul] at hq
    exact hw1 (congrArg Subtype.val
      (Balance.eq_one_of_oddQuotMk_eq_one (Subtype.ext hw2) hq))
  · have hsq : (k⁻¹ * ⟨w, hwC⟩) * (k⁻¹ * ⟨w, hwC⟩) = 1 := by
      apply Subtype.ext
      show (k : G)⁻¹ * w * ((k : G)⁻¹ * w) = 1
      rw [h, hci]
      calc c * w * (c * w) = c * (w * c) * w := by group
        _ = c * (c * w) * w := by rw [hcw]
        _ = (c * c) * (w * w) := by group
        _ = 1 := by rw [hc2, hw2, one_mul]
    have h2 : (k : G)⁻¹ * w = 1 :=
      congrArg Subtype.val (Balance.eq_one_of_oddQuotMk_eq_one hsq hq)
    rw [h, hci] at h2
    exact hwc ((eq_inv_of_mul_eq_one_right h2).trans hci)

end CFSG.ClassicalInvolution.A7Q.Vertex
