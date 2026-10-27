module

public import CFSG.Foundations.Basic
public import CFSG.CharacterTheory.Blocks.Defs
public import Mathlib.Data.Set.Card.Arithmetic
public import Mathlib.RingTheory.SimpleRing.Principal
public import Mathlib.RingTheory.WittVector.IsPoly
public import Mathlib.Tactic.Polynomial.Basic
public import Mathlib.Tactic.ReduceModChar

public section

open scoped BigOperators Classical

namespace CFSG.DihedralTIFusion

variable {G : Type*} [Group G]

theorem mem_iUnion_conj_image_iff {D : Set G} {x : G} :
    x ∈ ⋃ a : G, (fun y => a⁻¹ * y * a) '' D ↔ ∃ a : G, a * x * a⁻¹ ∈ D := by
  simp only [Set.mem_iUnion, Set.mem_image]
  constructor
  · rintro ⟨a, y, hy, rfl⟩
    exact ⟨a, by simpa [mul_assoc] using hy⟩
  · rintro ⟨a, ha⟩
    exact ⟨a, a * x * a⁻¹, ha, by group⟩

theorem ti_mem_of_conj_mem {D : Set G} {L : Subgroup G} (hTI : IsTISubset D L)
    {d g : G} (hd : d ∈ D) (hg : g * d * g⁻¹ ∈ D) : g ∈ L := by
  by_contra hgL
  have hinv : g⁻¹ ∉ L := fun h => hgL (by simpa using L.inv_mem h)
  have hmem : g * d * g⁻¹ ∈ D ∩ (fun x => g⁻¹⁻¹ * x * g⁻¹) '' D :=
    ⟨hg, d, hd, by simp⟩
  rw [hTI.2.2.2 g⁻¹ hinv] at hmem
  exact hmem

theorem ti_conj_mem_of_mem {D : Set G} {L : Subgroup G} (hTI : IsTISubset D L)
    {d g : G} (hd : d ∈ D) (hg : g ∈ L) : g * d * g⁻¹ ∈ D := by
  rw [← hTI.2.2.1] at hg
  exact (Subgroup.mem_set_normalizer_iff.mp hg d).mp hd

theorem ti_conj_mem_iff {D : Set G} {L : Subgroup G} (hTI : IsTISubset D L)
    {x a₀ : G} (ha₀ : a₀ * x * a₀⁻¹ ∈ D) (a : G) : a * x * a⁻¹ ∈ D ↔ a * a₀⁻¹ ∈ L := by
  have hconj : a * x * a⁻¹ = (a * a₀⁻¹) * (a₀ * x * a₀⁻¹) * (a * a₀⁻¹)⁻¹ := by group
  rw [hconj]
  exact ⟨fun ha => ti_mem_of_conj_mem hTI ha₀ ha, fun ha => ti_conj_mem_of_mem hTI ha₀ ha⟩

theorem ti_sum_conj_mem [Fintype G] {D : Set G} {L : Subgroup G}
    (hTI : IsTISubset D L) (x : G) :
    (∑ a : G, if a * x * a⁻¹ ∈ D then (1 : ℂ) else 0) =
      if x ∈ ⋃ a : G, (fun y => a⁻¹ * y * a) '' D then (Nat.card L : ℂ) else 0 := by
  split_ifs with hx
  · obtain ⟨a₀, ha₀⟩ := mem_iUnion_conj_image_iff.mp hx
    simp_rw [ti_conj_mem_iff hTI ha₀]
    rw [Fintype.sum_equiv (Equiv.mulRight a₀⁻¹) (fun a => if a * a₀⁻¹ ∈ L then (1 : ℂ) else 0)
      (fun b => if b ∈ L then (1 : ℂ) else 0) (fun a => rfl), Finset.sum_boole,
      Nat.card_eq_fintype_card, Fintype.card_subtype]
  · refine Finset.sum_eq_zero fun a _ => ite_eq_right fun ha => hx ?_
    exact mem_iUnion_conj_image_iff.mpr ⟨a, ha⟩

theorem finsum_mem_one_eq_natCard {α : Type*} [Finite α] (s : Set α) :
    ∑ᶠ x ∈ s, (1 : ℂ) = Nat.card s := by
  rw [Nat.card_coe_set_eq, ← finsum_one, Nat.cast_finsum_mem s.toFinite]
  simp

theorem ti_conjugacy_support_sum [Finite G] {D : Set G} {L : Subgroup G}
    (hTI : IsTISubset D L) (w : G → ℂ) (hw : BlocksIsClassFunction w) :
    ∑ᶠ x ∈ ⋃ a : G, (fun y => a⁻¹ * y * a) '' D, w x = L.index * ∑ᶠ d ∈ D, w d ∧
      Nat.card ↥(⋃ a : G, (fun y => a⁻¹ * y * a) '' D) = L.index * Nat.card D := by
  have : Fintype G := Fintype.ofFinite G
  have hsum : ∀ w : G → ℂ, BlocksIsClassFunction w →
      ∑ᶠ x ∈ ⋃ a : G, (fun y => a⁻¹ * y * a) '' D, w x = L.index * ∑ᶠ d ∈ D, w d := by
    intro w hw
    set S := ⋃ a : G, (fun y => a⁻¹ * y * a) '' D with hS
    rw [finsum_mem_def, finsum_mem_def, finsum_eq_sum_of_fintype, finsum_eq_sum_of_fintype]
    have hcount : (Nat.card L : ℂ) * ∑ x, S.indicator w x =
        (Nat.card G : ℂ) * ∑ y, D.indicator w y := by
      calc (Nat.card L : ℂ) * ∑ x, S.indicator w x
          = ∑ x, ∑ a : G, if a * x * a⁻¹ ∈ D then w x else 0 := by
            rw [Finset.mul_sum]
            refine Finset.sum_congr rfl fun x _ => ?_
            have h := ti_sum_conj_mem hTI x
            rw [← hS] at h
            have h' : (∑ a : G, if a * x * a⁻¹ ∈ D then w x else 0) =
                (∑ a : G, if a * x * a⁻¹ ∈ D then (1 : ℂ) else 0) * w x := by
              rw [Finset.sum_mul]
              exact Finset.sum_congr rfl fun a _ => by split_ifs <;> simp
            rw [h', h, Set.indicator_apply]
            split_ifs <;> simp
        _ = ∑ a : G, ∑ x, if a * x * a⁻¹ ∈ D then w x else 0 := Finset.sum_comm
        _ = ∑ _a : G, ∑ y, D.indicator w y := by
            refine Finset.sum_congr rfl fun a _ => ?_
            refine Fintype.sum_equiv (MulAut.conj a).toEquiv _ _ fun x => ?_
            simp only [MulEquiv.toEquiv_eq_coe, EquivLike.coe_coe, MulAut.conj_apply,
              Set.indicator_apply, hw x a]
        _ = (Nat.card G : ℂ) * ∑ y, D.indicator w y := by
            rw [Finset.sum_const, Finset.card_univ, nsmul_eq_mul, Nat.card_eq_fintype_card]
    have hL : (Nat.card L : ℂ) ≠ 0 := Nat.cast_ne_zero.mpr Nat.card_pos.ne'
    rw [← L.card_mul_index, Nat.cast_mul, mul_assoc] at hcount
    exact mul_left_cancel₀ hL hcount
  refine ⟨hsum w hw, ?_⟩
  have h1 := hsum (fun _ => 1) (fun _ _ => rfl)
  rw [finsum_mem_one_eq_natCard, finsum_mem_one_eq_natCard] at h1
  exact_mod_cast h1

end CFSG.DihedralTIFusion
