module

public import CFSG.LocalAnalysis.EvenBN.U5.CaseBSharedPartsB

public noncomputable section

namespace CFSG.LocalAnalysis.EvenBN.U5

namespace S3e3

open Subgroup
open CFSG.LocalAnalysis.EvenBN.Common.NormalizerQuotient

variable {G : Type} [Group G] [Finite G]

theorem proj_mem_centralizer_of_mem_section {D X : Subgroup G} (hX : X ≤ normalizer (D : Set G))
    {y : G} (hyN : y ∈ normalizer (D : Set G)) (hy : ∀ x ∈ X, x⁻¹ * (y * x * y⁻¹) ∈ D) :
    proj D ⟨y, hyN⟩ ∈ centralizer ((bar D X : Subgroup (Bar D)) : Set (Bar D)) := by
  rw [mem_centralizer_iff]
  rintro _ ⟨x', hx', rfl⟩
  have hxX : (x' : G) ∈ X := hx'
  have hmem : (x' : G)⁻¹ * (y * (x' : G) * y⁻¹) ∈ normalizer (D : Set G) :=
    mul_mem (inv_mem x'.2) (mul_mem (mul_mem hyN x'.2) (inv_mem hyN))
  have hone : proj D (⟨(x' : G)⁻¹ * (y * (x' : G) * y⁻¹), hmem⟩ : normalizer (D : Set G)) = 1 :=
    proj_eq_one_iff.2 (hy _ hxX)
  have : (⟨(x' : G)⁻¹ * (y * (x' : G) * y⁻¹), hmem⟩ : normalizer (D : Set G)) =
      x'⁻¹ * (⟨y, hyN⟩ * x' * ⟨y, hyN⟩⁻¹) := rfl
  rw [this, map_mul, map_inv, map_mul, map_mul, map_inv] at hone
  have h3 : proj D ⟨y, hyN⟩ * proj D x' * (proj D ⟨y, hyN⟩)⁻¹ = proj D x' := by
    have := congrArg (fun z => proj D x' * z) hone
    simpa using this
  calc proj D x' * proj D ⟨y, hyN⟩ = (proj D ⟨y, hyN⟩ * proj D x' * (proj D ⟨y, hyN⟩)⁻¹) *
        proj D ⟨y, hyN⟩ := by rw [h3]
    _ = proj D ⟨y, hyN⟩ * proj D x' := by group

end S3e3

open Subgroup CFSG.Open CFSG.ClassicalGroups.UnitaryFlag CFSG.LocalAnalysis.ComponentInitial
open CFSG.Blueprint
open CFSG.ABGLocalTools (IsSylowOf)
open CFSG.LocalAnalysis.EvenBN.Common.NormalizerQuotient
open scoped MatrixGroups

namespace Data

variable {G : Type} [Group G] [Finite G] {f : ℕ} {K : Type} [Field K]
  {h : UnitaryFieldData 2 f K} {d : Data G h}

theorem sec39_odd (hp : d.CaseHyp) (k : d.Know92) (he : d.Sec39e)
    (hr : d.Sec39Reduced) (hl : d.Sec39Layer) :
    Odd (d.D.relIndex (centralizerSection (d.D ⊔ d.M₁) d.D)) := by
  have hMN := hr.M₁_le
  have hXN : d.D ⊔ d.M₁ ≤ normalizer (d.D : Set G) := sup_le le_normalizer hMN
  set Y := centralizerSection (d.D ⊔ d.M₁) d.D with hY
  have hDY : d.D ≤ Y := by
    intro y hy
    refine ⟨le_normalizer (mem_sup_left hy), le_normalizer hy, fun x hx => ?_⟩
    have hxN := hXN hx
    have h1 : x⁻¹ * y * x ∈ d.D := by
      have := (mem_normalizer_iff.1 (inv_mem hxN) y).1 hy
      simpa using this
    have : x⁻¹ * (y * x * y⁻¹) = (x⁻¹ * y * x) * y⁻¹ := by group
    rw [this]
    exact mul_mem h1 (inv_mem hy)
  have hYO : Y ≤ lift (OD d) := by
    intro y hy
    obtain ⟨-, hyN, hyx⟩ := hy
    have hc := S3e3.proj_mem_centralizer_of_mem_section (X := d.M₁) hMN hyN
      (fun x hx => hyx x (mem_sup_right hx))
    rw [hl.centralizer_eq] at hc
    exact mem_lift_of_proj_mem (x := ⟨y, hyN⟩) hc
  have hmul : d.D.relIndex Y * Y.relIndex (lift (OD d)) = d.D.relIndex (lift (OD d)) :=
    Subgroup.relIndex_mul_relIndex d.D Y (lift (OD d)) hDY hYO
  have hrel : d.D.relIndex (lift (OD d)) = Nat.card (OD d) := by
    have h1 := Subgroup.card_mul_index (d.D.subgroupOf (lift (OD d)))
    have h2 : Nat.card (d.D.subgroupOf (lift (OD d))) = Nat.card d.D :=
      Nat.card_congr (Subgroup.subgroupOfEquivOfLe (le_lift _)).toEquiv
    rw [h2, card_lift, mul_comm (Nat.card (OD d))] at h1
    have hpos : 0 < Nat.card d.D := Nat.card_pos
    exact Nat.eq_of_mul_eq_mul_left hpos h1
  have hodd : Odd (Nat.card (OD d)) := GMSK.odd_card_standardComponentOddCore _
  rw [← hrel] at hodd
  rw [← hmul] at hodd
  exact (Nat.odd_mul.1 hodd).1

end Data

namespace CaseBParts

theorem sec39Odd : Sec39OddStatement :=
  fun _ _ _ _ _ _ _ _ hp k he hr hl => Data.sec39_odd hp k he hr hl

end CaseBParts

end CFSG.LocalAnalysis.EvenBN.U5
