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

theorem sec3101B_mem_sup_of_le_normalizer {α : Type*} [Group α] {E Y : Subgroup α}
    (hY : Y ≤ Subgroup.normalizer (E : Set α)) {x : α} (hx : x ∈ E ⊔ Y) :
    ∃ e ∈ E, ∃ y ∈ Y, x = e * y := by
  have hT : ∃ T : Subgroup α, ∀ z : α, z ∈ T ↔ ∃ e ∈ E, ∃ y ∈ Y, z = e * y := by
    refine ⟨{ carrier := {z | ∃ e ∈ E, ∃ y ∈ Y, z = e * y}, mul_mem' := ?_, one_mem' := ?_, inv_mem' := ?_ }, fun z => Iff.rfl⟩
    · rintro _ _ ⟨e₁, he₁, y₁, hy₁, rfl⟩ ⟨e₂, he₂, y₂, hy₂, rfl⟩
      have hc : y₁ * e₂ * y₁⁻¹ ∈ E := (Subgroup.mem_normalizer_iff.1 (hY hy₁) e₂).1 he₂
      exact ⟨e₁ * (y₁ * e₂ * y₁⁻¹), E.mul_mem he₁ hc, y₁ * y₂, Y.mul_mem hy₁ hy₂, by group⟩
    · exact ⟨1, E.one_mem, 1, Y.one_mem, by group⟩
    · rintro _ ⟨e, he, y, hy, rfl⟩
      have hc : y⁻¹ * e⁻¹ * y⁻¹⁻¹ ∈ E :=
        (Subgroup.mem_normalizer_iff.1 (hY (Y.inv_mem hy)) e⁻¹).1 (E.inv_mem he)
      exact ⟨y⁻¹ * e⁻¹ * y⁻¹⁻¹, hc, y⁻¹, Y.inv_mem hy, by group⟩
  obtain ⟨T, hTmem⟩ := hT
  have hle : E ⊔ Y ≤ T := by
    apply sup_le
    · intro e he
      exact (hTmem e).2 ⟨e, he, 1, Y.one_mem, by group⟩
    · intro y hy
      exact (hTmem y).2 ⟨1, E.one_mem, y, hy, by group⟩
  exact (hTmem x).1 (hle hx)

theorem sec3101B_factor_D {α : Type*} [Group α] {S E D Y : Subgroup α}
    (hSeq : S = E ⊔ Y) (hDS : D ≤ S) (hYD : Y ≤ D) (hYN : Y ≤ Subgroup.normalizer (E : Set α))
    (hEY : E ⊓ Y = ⊥) :
    D = (E ⊓ D) ⊔ Y ∧ (E ⊓ D) ⊓ Y = ⊥ := by
  refine ⟨le_antisymm ?_ (sup_le inf_le_right hYD), ?_⟩
  · intro x hx
    have hxS : x ∈ E ⊔ Y := (le_of_eq hSeq) (hDS hx)
    obtain ⟨e, he, y, hy, rfl⟩ := sec3101B_mem_sup_of_le_normalizer hYN hxS
    have hed : e ∈ D := by simpa using D.mul_mem hx (D.inv_mem (hYD hy))
    exact mul_mem (Subgroup.mem_sup_left (Subgroup.mem_inf.2 ⟨he, hed⟩)) (Subgroup.mem_sup_right hy)
  · have h1 : (E ⊓ D) ⊓ Y ≤ E ⊓ Y := inf_le_inf inf_le_left le_rfl
    rw [hEY] at h1
    exact eq_bot_iff.2 h1

theorem sec3101B_sup_eq {α : Type*} [Group α] {F W E D Y : Subgroup α}
    (hED : E ⊓ D = W ⊔ Y) (hWF : W ≤ F) : F ⊔ (E ⊓ D) = F ⊔ Y := by
  rw [hED, ← sup_assoc, sup_eq_left.2 hWF]

theorem sec3101B_factor_S_D {α : Type*} [Group α] {S E D Y : Subgroup α}
    (hSED : S = E ⊔ D) (hDS : D ≤ S) (hYS : Y ≤ S) (hEfac : E = (E ⊓ D) ⊔ Y) :
    S = D ⊔ Y := by
  have hsub : (E ⊓ D) ⊔ Y ≤ D ⊔ Y := sup_le (inf_le_right.trans le_sup_left) le_sup_right
  have hEle : E ≤ D ⊔ Y := le_trans (le_of_eq hEfac) hsub
  have hSle : S ≤ D ⊔ Y := le_trans (le_of_eq hSED) (sup_le hEle le_sup_left)
  exact le_antisymm hSle (sup_le hDS hYS)

theorem sec3101B_inf_bot_of_inf_bot {α : Type*} [Group α] {S D C : Subgroup α}
    (hDC : D ⊓ C = ⊥) : D ⊓ (S ⊓ C) = ⊥ := by
  have h1 : D ⊓ (S ⊓ C) ≤ D ⊓ C := inf_le_inf le_rfl inf_le_right
  rw [hDC] at h1
  exact eq_bot_iff.2 h1

theorem sec3101B_of_hyp (hp : d.CaseHyp) (k : d.Know93) (h2 : d.Sec3_10_two)
    (S : Subgroup G) (hS : IsSylowOf 2 S d.L₂) (hP : d.P ≤ S) (hO : d.Sec3101Orders S)
    (ha : d.Sec3101A S) (he : d.Sec3101E S) : d.Sec3101B S := by
  have h91 := k.s9_1 S hS hP
  have h39a := k.s9a S hS hP
  have h39e := k.s9e
  have hSED : S = d.E ⊔ d.D := h91.1
  have hEchar : (d.E.subgroupOf S).Characteristic := h91.2.1
  have hDS : d.D ≤ S := by rw [hSED]; exact le_sup_right
  have hES : d.E ≤ S := by rw [hSED]; exact le_sup_left
  have hEN : (d.E.subgroupOf S).Normal := by
    haveI := hEchar
    infer_instance
  have hSN : S ≤ Subgroup.normalizer (d.E : Set G) :=
    (normal_subgroupOf_iff_le_normalizer hES).1 hEN
  have hE1 : d.E = (d.E ⊓ d.D) ⊔ (S ⊓ centralizer (d.I₁ : Set G)) := he.1.1
  have hE2 : d.E ⊓ d.D = d.W ⊔ (S ⊓ centralizer (d.I₅ : Set G)) := he.2.2
  have hF : d.F = d.W ⊔ (S ⊓ centralizer (d.I₆ : Set G)) := ha.2.1.1
  have hWF : d.W ≤ d.F := by rw [hF]; exact le_sup_left
  have hYD : S ⊓ centralizer (d.I₂ : Set G) ≤ d.D := by
    exact (le_of_eq h39a.cD₂.symm).trans inf_le_left
  have hYN : S ⊓ centralizer (d.I₂ : Set G) ≤ Subgroup.normalizer (d.E : Set G) :=
    inf_le_left.trans hSN
  have hA := sec3101B_factor_D (S := S) (E := d.E) (D := d.D)
    (Y := S ⊓ centralizer (d.I₂ : Set G)) h39a.S_eq₂ hDS hYD hYN h39a.E_inf₂
  have hC := sec3101B_sup_eq (F := d.F) (W := d.W) (E := d.E) (D := d.D)
    (Y := S ⊓ centralizer (d.I₅ : Set G)) hE2 hWF
  have hE5 := sec3101B_factor_S_D (S := S) (E := d.E) (D := d.D)
    (Y := S ⊓ centralizer (d.I₁ : Set G)) hSED hDS inf_le_left hE1
  have hEI := sec3101B_inf_bot_of_inf_bot (S := S) (D := d.D)
    (C := centralizer (d.I₁ : Set G)) h39e.centralizer_I₁
  exact ⟨hA, h39a.D_eq, hC, ⟨h39a.S_eq₂, h39a.E_inf₂⟩, ⟨hE5, hEI⟩⟩

end Data

namespace CaseBParts

theorem sec3101B : Sec3101BStatement :=
  fun _ _ _ _ _ _ _ _ hp k h2 S hS hP hO ha he => Data.sec3101B_of_hyp hp k h2 S hS hP hO ha he

end CaseBParts

end CFSG.LocalAnalysis.EvenBN.U5
