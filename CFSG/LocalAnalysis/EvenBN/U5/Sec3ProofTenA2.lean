module

public import CFSG.LocalAnalysis.EvenBN.U5.CaseBSharedPartsB
public import CFSG.LocalAnalysis.EvenBN.U5.Sec3TenN1

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

theorem sec3101A2_of_facts (hp : d.CaseHyp) (k : d.Know93) (S : Subgroup G)
    (hS : IsSylowOf 2 S d.L₂) (hP : d.P ≤ S) (hO : d.Sec3101Orders S) (h1 : d.Sec3101A1 S)
    (RA : Nat.card (d.F ⊓ centralizer (d.I₆ : Set G) : Subgroup G) = (2 ^ f) ^ 2)
    (RB : Nat.card (d.F ⊓ centralizer ((d.I₃ ⊓ d.I₆ : Subgroup G) : Set G) : Subgroup G) =
      (2 ^ f) ^ 4)
    (RC : d.W ⊓ centralizer (d.I₆ : Set G) = ⊥)
    (RD : (d.F ⊓ centralizer (d.I₄ : Set G)) ⊓
        (d.F ⊓ centralizer ((d.I₃ ⊓ d.I₆ : Subgroup G) : Set G)) = ⊥) :
    d.Sec3101A2 S := by
  obtain ⟨-, -, hD, hF, -⟩ := k.s9_2 S hS hP
  have hd := hp.hyp
  have hGMS := hp.gms
  unfold Sec3101A1 at h1
  obtain ⟨-, hWeq, -⟩ := h1
  have hDS : d.D ≤ S := by
    rw [hD]
    exact inf_le_left
  have hFD : d.F ≤ d.D := by
    rw [← hF]
    exact (show CFSG.centerIn d.D ≤ d.D from inf_le_left)
  have hFS : d.F ≤ S := hFD.trans hDS
  have hWF : d.W ≤ d.F := hd.W_le_F hGMS
  have hcomm : ∀ x ∈ d.F, ∀ y ∈ d.F, x * y = y * x := by
    intro x hx y hy
    have hy' : y ∈ CFSG.centerIn d.D := by
      rw [hF]
      exact hy
    have hyc : y ∈ centralizer (d.D : Set G) :=
      (show CFSG.centerIn d.D ≤ centralizer (d.D : Set G) from inf_le_right) hy'
    exact mem_centralizer_iff.1 hyc x (hFD hx)
  have hC6eq : d.F ⊓ centralizer (d.I₆ : Set G) = S ⊓ centralizer (d.I₆ : Set G) :=
    Subgroup.eq_of_le_of_card_ge (inf_le_inf_right _ hFS)
      (le_of_eq (by rw [hO.c₆, RA]))
  have hC6 : S ⊓ centralizer (d.I₆ : Set G) ≤ d.F := by
    rw [← hC6eq]
    exact inf_le_left
  have hC36eq : d.F ⊓ centralizer ((d.I₃ ⊓ d.I₆ : Subgroup G) : Set G) =
      S ⊓ centralizer ((d.I₃ ⊓ d.I₆ : Subgroup G) : Set G) :=
    Subgroup.eq_of_le_of_card_ge (inf_le_inf_right _ hFS)
      (le_of_eq (by rw [hO.c₃₆, RB]))
  have hC36 : S ⊓ centralizer ((d.I₃ ⊓ d.I₆ : Subgroup G) : Set G) ≤ d.F := by
    rw [← hC36eq]
    exact inf_le_left
  have hC4eq : d.F ⊓ centralizer (d.I₄ : Set G) = S ⊓ centralizer (d.I₄ : Set G) :=
    Subgroup.eq_of_le_of_card_ge (inf_le_inf_right _ hFS)
      (le_of_eq (by rw [hO.c₄, hd.card_F_I₄ hGMS]))
  have hC4W : S ⊓ centralizer (d.I₄ : Set G) ≤ d.W := by
    rw [hWeq]
    exact le_sup_right
  have hC4 : S ⊓ centralizer (d.I₄ : Set G) ≤ d.F := hC4W.trans hWF
  have hWC6 : d.W ⊓ (S ⊓ centralizer (d.I₆ : Set G)) = ⊥ :=
    le_antisymm ((inf_le_inf_left _ inf_le_right).trans RC.le) bot_le
  have hsupW6 : d.W ⊔ (S ⊓ centralizer (d.I₆ : Set G)) ≤ d.F := sup_le hWF hC6
  have hcard6 : Nat.card (d.W ⊔ (S ⊓ centralizer (d.I₆ : Set G)) : Subgroup G) = (2 ^ f) ^ 8 := by
    have h0 := (CFSG.GroupTheory.card_sup_mul_card_inf_of_commute d.W
      (S ⊓ centralizer (d.I₆ : Set G))
      (fun x hx y hy => hcomm x (hWF hx) y (hC6 hy))).1
    rw [hWC6, card_bot, hd.card_W hGMS, hO.c₆, mul_one] at h0
    rw [h0]
    ring
  have hFeq1 : d.F = d.W ⊔ (S ⊓ centralizer (d.I₆ : Set G)) :=
    (Subgroup.eq_of_le_of_card_ge hsupW6 (le_of_eq (by rw [hd.card_F hGMS, hcard6]))).symm
  have hC4C36 : (S ⊓ centralizer (d.I₄ : Set G)) ⊓
      (S ⊓ centralizer ((d.I₃ ⊓ d.I₆ : Subgroup G) : Set G)) = ⊥ := by
    rw [← hC4eq, ← hC36eq]
    exact RD
  have hsupC4 : (S ⊓ centralizer (d.I₄ : Set G)) ⊔
      (S ⊓ centralizer ((d.I₃ ⊓ d.I₆ : Subgroup G) : Set G)) ≤ d.F :=
    sup_le hC4 hC36
  have hcard4 : Nat.card ((S ⊓ centralizer (d.I₄ : Set G)) ⊔
      (S ⊓ centralizer ((d.I₃ ⊓ d.I₆ : Subgroup G) : Set G)) : Subgroup G) = (2 ^ f) ^ 8 := by
    have h0 := (CFSG.GroupTheory.card_sup_mul_card_inf_of_commute
      (S ⊓ centralizer (d.I₄ : Set G))
      (S ⊓ centralizer ((d.I₃ ⊓ d.I₆ : Subgroup G) : Set G))
      (fun x hx y hy => hcomm x (hC4 hx) y (hC36 hy))).1
    rw [hC4C36, card_bot, hO.c₄, hO.c₃₆, mul_one] at h0
    rw [h0]
    ring
  have hFeq2 : d.F = (S ⊓ centralizer (d.I₄ : Set G)) ⊔
      (S ⊓ centralizer ((d.I₃ ⊓ d.I₆ : Subgroup G) : Set G)) :=
    (Subgroup.eq_of_le_of_card_ge hsupC4 (le_of_eq (by rw [hd.card_F hGMS, hcard4]))).symm
  unfold Sec3101A2
  exact ⟨⟨hFeq1, hWC6⟩, ⟨hFeq2, hC4C36⟩⟩

theorem sec3101A2_of_hyp (hp : d.CaseHyp) (k : d.Know93) (h2 : d.Sec3_10_two)
    (S : Subgroup G) (hS : IsSylowOf 2 S d.L₂) (hP : d.P ≤ S) (hO : d.Sec3101Orders S)
    (h1 : d.Sec3101A1 S) : d.Sec3101A2 S := by
  exact sec3101A2_of_facts hp k S hS hP hO h1 (sec3101_RA hp) (sec3101_RB hp) (sec3101_RC hp) (sec3101_RD hp)

end Data

namespace CaseBParts

theorem sec3101A2 : Sec3101A2Statement :=
  fun _ _ _ _ _ _ _ _ hp k h2 S hS hP hO h1 => Data.sec3101A2_of_hyp hp k h2 S hS hP hO h1

end CaseBParts

end CFSG.LocalAnalysis.EvenBN.U5
