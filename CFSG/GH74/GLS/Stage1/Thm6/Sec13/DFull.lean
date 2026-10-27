module

public import CFSG.GH74.GLS.Stage1.Thm6.Sec13.DCount
public import CFSG.GH74.GLS.Stage1.Thm6.Sec13.Arith
public import CFSG.GH74.GLS.Stage1.Thm6.Sec13.Models5

public section

namespace CFSG.GH74.GLS.Stage1.Thm6.Sec13

open Subgroup
open scoped commutatorElement

variable {G : Type*} [Group G]

namespace D13

variable {x : G} {T V H : Subgroup G} {f : G} (d : D13 x T V H f)
include d

theorem x_mem_M : x ∈ Mm V H := ⟨d.hI.H_le d.hI.x_mem, le_normalizer d.hI.x_mem⟩

theorem cls_full [Finite G] {R : Subgroup G} (hR : SylowIn 2 R (Mm V H)) (hHR : H < R) :
    ∃ n : ℕ, 1 ≤ n ∧ Nat.card (Hzero H f) = 4 ^ n ∧ Nat.card R = 2 ^ (2 * n + 3) ∧
      ∀ q ∈ Hzero H f, q * x ∈ cls (Mm V H) x := by
  obtain ⟨n, hn1, hn⟩ := IsYGroup.card_pow4 d.iv4
  have hcard := card_cls_mul (Mm V H) d.x_mem_M
  obtain ⟨o, ho, hC⟩ := d.out.card_cent_M d.hI.E_le
  rw [hC] at hcard
  have hRM := relIndex_mul_card R (Mm V H)
  rw [inf_of_le_left hR.le] at hRM
  obtain ⟨e, he⟩ := hR.isPGroup.exists_card_eq
  rw [he] at hRM
  have hu : ¬ 2 ∣ R.relIndex (Mm V H) := hR.2.2
  have hH : Nat.card H = 2 * 4 ^ n := by
    rw [InH.card_H_of d.out d.iv1 d.iv2 d.iv3 d.hI, hn]
  have hr4 : 4 * 4 ^ n ≤ 2 ^ e := by
    obtain ⟨c, hc⟩ := Subgroup.card_dvd_of_le hHR.le
    have hlt := Subgroup.card_lt_of_lt hHR
    rw [hc, hH] at hlt
    have hc2 : 2 ≤ c := by
      by_contra hcon
      push Not at hcon
      interval_cases c <;> simp at hlt
    have hpos : 0 < 4 ^ n := by positivity
    rw [← he, hc, hH]
    nlinarith
  have ha : Nat.card (cls (Mm V H) x) ≤ 4 ^ n := by
    have := d.card_cls_le
    rwa [hn] at this
  have ha0 : 0 < Nat.card (cls (Mm V H) x) := by
    have : Nonempty (cls (Mm V H) x) := ⟨⟨x, x_mem_cls⟩⟩
    exact Nat.card_pos
  have hEq : Nat.card (cls (Mm V H) x) * (8 * o) = 2 ^ e * R.relIndex (Mm V H) := by
    rw [hcard, ← hRM]; ring
  have hX := key_arith n hn1 _ o _ e ho hEq hr4 ha d.card_cls_mod3 ha0
  have he' : e = 2 * n + 3 := by
    rw [hX] at hEq
    exact key_arith2 n e o _ ho hu hEq
  refine ⟨n, hn1, hn, by rw [he, he'], ?_⟩
  have hsub : cls (Mm V H) x ⊆ (fun q => q * x) '' (Hzero H f : Set G) := by
    intro y hy
    obtain ⟨q, hq, rfl⟩ := d.cls_sub hy
    exact ⟨q, hq, rfl⟩
  have hnc : ((fun q => q * x) '' (Hzero H f : Set G)).ncard = 4 ^ n := by
    rw [Set.ncard_image_of_injective _ (mul_left_injective x), ← hn]
    exact Nat.card_coe_set_eq _ ▸ rfl
  have hle : ((fun q => q * x) '' (Hzero H f : Set G)).ncard ≤ (cls (Mm V H) x).ncard := by
    rw [hnc, ← Nat.card_coe_set_eq, hX]
  have heq := Set.eq_of_subset_of_ncard_le hsub hle (Set.toFinite _)
  intro q hq
  rw [heq]
  exact ⟨q, hq, rfl⟩

end D13

end CFSG.GH74.GLS.Stage1.Thm6.Sec13
