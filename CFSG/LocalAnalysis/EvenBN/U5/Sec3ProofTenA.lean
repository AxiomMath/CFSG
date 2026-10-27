module

public import CFSG.LocalAnalysis.EvenBN.U5.CaseBSharedPartsB

public noncomputable section

namespace CFSG.LocalAnalysis.EvenBN.U5

open Subgroup CFSG.Open CFSG.ClassicalGroups.UnitaryFlag CFSG.LocalAnalysis.ComponentInitial
open CFSG.Blueprint
open CFSG.ABGLocalTools (IsSylowOf)
open CFSG.LocalAnalysis.EvenBN.Common.NormalizerQuotient
open scoped MatrixGroups

namespace Data

variable {G : Type} [Group G] [Finite G] {f : ℕ} {K : Type} [Field K]
  {h : UnitaryFieldData 2 f K} {d : Data G h}

theorem sec3101A1_of_hyp (hp : d.CaseHyp) (k : d.Know93) (h2 : d.Sec3_10_two)
    (S : Subgroup G) (hS : IsSylowOf 2 S d.L₂) (hP : d.P ≤ S) (hO : d.Sec3101Orders S) :
    d.Sec3101A1 S := by
  obtain ⟨hZ, -, hD, hF, -⟩ := k.s9_2 S hS hP
  have hd := hp.hyp
  have hGMS := hp.gms
  have hVS : d.V ≤ S := by
    rw [← hZ]
    exact (show CFSG.centerIn S ≤ S from inf_le_left)
  have hDS : d.D ≤ S := by
    rw [hD]
    exact inf_le_left
  have hFS : d.F ≤ S := by
    rw [← hF]
    exact (show CFSG.centerIn d.D ≤ d.D from inf_le_left).trans hDS
  have hVC3 : d.V ≤ centralizer (d.I₃ : Set G) :=
    hd.V_le_CB₄I₃.trans (show d.CB₄I₃ ≤ centralizer (d.I₃ : Set G) from inf_le_right)
  have hEq1 : d.V = S ⊓ centralizer (d.I₃ : Set G) :=
    Subgroup.eq_of_le_of_card_ge (le_inf hVS hVC3) (le_of_eq (by rw [hO.c₃, hd.card_V]))
  have hEq2 : S ⊓ centralizer (d.I₄ : Set G) = d.F ⊓ centralizer (d.I₄ : Set G) :=
    (Subgroup.eq_of_le_of_card_ge (inf_le_inf_right (centralizer (d.I₄ : Set G)) hFS)
      (le_of_eq (by rw [hO.c₄, hd.card_F_I₄ hGMS]))).symm
  unfold Sec3101A1
  refine ⟨hEq1, ?_, ?_⟩
  · rw [hd.W_eq hGMS, hEq2]
  · rw [hEq2]
    exact hd.V_inf_F_I₄

end Data

namespace CaseBParts

theorem sec3101A1 : Sec3101A1Statement :=
  fun _ _ _ _ _ _ _ _ hp k h2 S hS hP hO => Data.sec3101A1_of_hyp hp k h2 S hS hP hO

end CaseBParts

end CFSG.LocalAnalysis.EvenBN.U5
