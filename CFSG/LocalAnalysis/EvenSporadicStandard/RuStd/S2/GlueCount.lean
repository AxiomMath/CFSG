module

public import CFSG.LocalAnalysis.EvenSporadicStandard.RuStd.S2.GlueFive

public section

namespace CFSG.EvenSporadicStandard.RuStd.S2.Glue

open Subgroup

variable {G : Type} [Group G] [Finite G] {L : Subgroup G} {t : G}

theorem count_of (d : PartThreeData G L t) (h5 : RuFiveFacts L) :
    ∀ F : Subgroup (CenG d.r), F ≤ centralizer ({fCen d} : Set (CenG d.r)) → Nat.card F = 25 →
      Nat.card {x : CenG d.r // x ∈ F ∧ x ≠ 1 ∧
        9 ∣ Nat.card (centralizer ({x} : Set (CenG d.r)))} ≤ 4 := by
  intro F hF hF25
  set F' : Subgroup G := F.map (centralizer ({d.r} : Set G)).subtype with hF'
  have hF'card : Nat.card F' = 25 := by
    rw [hF', Subgroup.card_map_of_injective (Subgroup.subtype_injective _)]
    exact hF25
  have hF'C : F' ≤ centralizer ({d.f} : Set G) := by
    rintro _ ⟨x, hx, rfl⟩
    have := mem_centralizer_singleton_iff.1 (hF hx)
    exact mem_centralizer_singleton_iff.2 (congrArg Subtype.val this)
  have hF'p : IsPGroup 5 F' := IsPGroup.of_card (n := 2) (by rw [hF'card]; norm_num)
  obtain ⟨c, hcC, hc⟩ := exists_conj_F₁ d hF'C hF'p
  set fL : L := ⟨d.f, d.f_mem⟩ with hfL
  have hfL5 : orderOf fL = 5 := by rw [hfL, Subgroup.orderOf_mk]; exact d.f_ord
  have hF₁le : d.F₁.subgroupOf L ≤ centralizer ({fL} : Set L) := by
    intro y hy
    have h1 : (y : G) ∈ d.F₁ := Subgroup.mem_subgroupOf.1 hy
    have h2 := mem_centralizer_singleton_iff.1 (d.F₁_le_C h1)
    exact mem_centralizer_singleton_iff.2 (Subtype.ext h2)
  have hF₁card : Nat.card (d.F₁.subgroupOf L) = 25 := by
    rw [← d.F₁_card]
    exact Nat.card_congr (Subgroup.subgroupOfEquivOfLe d.F₁_le_L).toEquiv
  have hcount := h5.count fL hfL5 d.f_typeA (d.F₁.subgroupOf L) hF₁le hF₁card
  have key : ∀ x : {x : CenG d.r // x ∈ F ∧ x ≠ 1 ∧
      9 ∣ Nat.card (centralizer ({x} : Set (CenG d.r)))},
      ∃ hyL : c * ((x.1 : CenG d.r) : G) * c⁻¹ ∈ L, Nat.card (centralizer
        ({(⟨c * ((x.1 : CenG d.r) : G) * c⁻¹, hyL⟩ : L)} : Set L)) = 1000 := by
    intro x
    obtain ⟨hxF, hx1, hx9⟩ := x.2
    have hxG : ((x.1 : CenG d.r) : G) ∈ F' := ⟨x.1, hxF, rfl⟩
    have hx1' : ((x.1 : CenG d.r) : G) ≠ 1 := fun h => hx1 (Subtype.ext h)
    have hx9' : 9 ∣ Nat.card (centralizer ({((x.1 : CenG d.r) : G)} : Set G)) :=
      hx9.trans (card_cen_dvd d.r x.1)
    obtain ⟨hyL, -, h1000⟩ := conj_typeB d h5 hx1' (hc _ hxG) hx9'
    exact ⟨hyL, h1000⟩
  let Ξ : {x : CenG d.r // x ∈ F ∧ x ≠ 1 ∧ 9 ∣ Nat.card (centralizer ({x} : Set (CenG d.r)))} →
      {y : L // y ∈ d.F₁.subgroupOf L ∧ y ≠ 1 ∧ Nat.card (centralizer ({y} : Set L)) = 1000} :=
    fun x => ⟨⟨c * ((x.1 : CenG d.r) : G) * c⁻¹, (key x).1⟩,
      Subgroup.mem_subgroupOf.2 (hc _ ⟨x.1, x.2.1, rfl⟩),
      fun h => x.2.2.1 (Subtype.ext (by
        have h1 : c * ((x.1 : CenG d.r) : G) * c⁻¹ = 1 := congrArg Subtype.val h
        calc ((x.1 : CenG d.r) : G) = c⁻¹ * (c * ((x.1 : CenG d.r) : G) * c⁻¹) * c := by group
          _ = 1 := by rw [h1]; group)),
      (key x).2⟩
  have hinj : Function.Injective Ξ := by
    intro x x' h
    have h1 : c * ((x.1 : CenG d.r) : G) * c⁻¹ = c * ((x'.1 : CenG d.r) : G) * c⁻¹ :=
      congrArg (fun y => ((y.1 : L) : G)) h
    have h2 : ((x.1 : CenG d.r) : G) = ((x'.1 : CenG d.r) : G) :=
      mul_left_cancel (mul_right_cancel h1)
    exact Subtype.ext (Subtype.ext h2)
  exact (Nat.card_le_card_of_injective Ξ hinj).trans hcount

end CFSG.EvenSporadicStandard.RuStd.S2.Glue
