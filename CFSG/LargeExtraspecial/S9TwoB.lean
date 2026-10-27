module

public import CFSG.LargeExtraspecial.S9TwoA

public section

attribute [-instance] instAddCommGroupOfIsSimpleAddGroupOfIsNilpotent
  instCommGroupOfIsSimpleGroupOfIsNilpotent

namespace CFSG.LargeExtraspecial.S9

open Subgroup Module QuadraticMap CFSG.RankThree.OrthogonalInvolutions
open CFSG.LargeExtraspecial.S4 CFSG.LargeExtraspecial.S6 CFSG.LargeExtraspecial.OrthoF2

universe u

variable {G : Type u} [Group G] [Finite G] {S : Setting G} {g : G}

theorem finrank_WV_add_eight_of_four (H : Hyp4 S g) {t : S.O} (ht1 : t ≠ 1)
    (h4 : finrank (ZMod 2) (Vt S g t) = 4) :
    finrank (ZMod 2) ((Wt S g t).map (Vt S g t).mkQ) + 8 = 2 * S.width := by
  have h1 := S8.finrank_WV_add_finrank_Vt H ht1 (g := g)
  have h2 := finrank_Wt (S := S) (g := g) (t := t)
  have h3 := S.finrank_Qt_eq_two_mul_width
  rw [h4] at h1 h2
  omega

section A6

variable (hCE : CentralExtInput.{u}) (H : Hyp4 S g) (hNo : NoA2 S g) (C : Cons311 S g)
  {t : S.O} (ht : t ∈ S.Lbar g) (ht1 : t ≠ 1) (hVQ : ¬ V S g t ≤ S.Qa g)
  (hA6 : A6Case H C ht ht1 hVQ)
include hCE H hNo C ht ht1 hVQ hA6

theorem card_Abar_mul_four_a6 :
    Nat.card (S.Lbar g ⊓ Nbar S g t : Subgroup S.O) * 4 = 2 ^ (S.width - 1) := by
  obtain ⟨h, hh, hb⟩ := exists_pair H C ht ht1 hVQ
  obtain ⟨Q, hQ, -, hQa, -, -, hEa, -⟩ := timmesfeld_6_2_two hCE H hNo C ht ht1 hVQ hA6 hh hb
  have h1 := card_Lbar_eq_mul H.conj_mem ht (t := t)
  rw [C.card_Lbar, hEa, CFSG.LargeExtraspecial.card_pointRadical hQ (aV_ne_zero H ht) hQa,
    hA6.finrank_eq] at h1
  rw [h1, mul_comm]
  norm_num

theorem four_lt_width_a6 (hA : S.Lbar g ⊓ Nbar S g t ≠ zpowers t) : 4 < S.width := by
  have hcard := card_Abar_mul_four_a6 hCE H hNo C ht ht1 hVQ hA6
  have htt : t * t = 1 := mul_self_of_mem_Lbar S H.conj_mem ht
  have hto : orderOf t = 2 := orderOf_eq_prime (by rw [pow_two]; exact htt) ht1
  have hle : zpowers t ≤ S.Lbar g ⊓ Nbar S g t := by
    rw [zpowers_le]
    exact ⟨ht, self_mem_Nbar H ht⟩
  have hlt : Nat.card (zpowers t) < Nat.card (S.Lbar g ⊓ Nbar S g t : Subgroup S.O) :=
    Subgroup.card_lt_of_lt (lt_of_le_of_ne hle (Ne.symm hA))
  rw [Nat.card_zpowers, hto] at hlt
  by_contra hn
  push Not at hn
  have h8 : 2 ^ (S.width - 1) ≤ 8 :=
    calc 2 ^ (S.width - 1) ≤ 2 ^ 3 := Nat.pow_le_pow_right (by norm_num) (by omega)
      _ = 8 := by norm_num
  omega

theorem eight_le_finrank_WV_a6 (hA : S.Lbar g ⊓ Nbar S g t ≠ zpowers t) :
    8 ≤ finrank (ZMod 2) ((Wt S g t).map (Vt S g t).mkQ) := by
  obtain ⟨h, hh, hb⟩ := exists_pair H C ht ht1 hVQ
  obtain ⟨k, hk⟩ := timmesfeld_6_2_two_dvd hCE H hNo C ht ht1 hVQ hA6 hh hb
  have hne := finrank_WV_ne_four_a6 hCE H hNo C ht ht1 hVQ hA6 hh hb
  have hn := four_lt_width_a6 hCE H hNo C ht ht1 hVQ hA6 hA
  have hd := finrank_WV_add_eight_of_four H ht1 hA6.finrank_eq
  omega

theorem conj_mem_Nbar_a6 (hA : S.Lbar g ⊓ Nbar S g t ≠ zpowers t) {α : S.O}
    (hα : α ∈ S.Lbar g ⊓ Nbar S g t) {x : S.O} (hxL : x * α * x⁻¹ ∈ S.Lbar g) :
    x * α * x⁻¹ ∈ Nbar S g t := by
  by_contra hxN
  obtain ⟨h, hh, hb⟩ := exists_pair H C ht ht1 hVQ
  have h8 := eight_le_finrank_WV_a6 hCE H hNo C ht ht1 hVQ hA6 hA
  have hge := finrank_commSpace_ge_a6 hCE H hNo C ht ht1 hVQ hA6 hh hb hxL hxN
  have hle := finrank_commSpace_le_seven_a6 hCE H C ht ht1 hVQ hA6 hh hb hα
  have hconj : finrank (ZMod 2) (commSpace ((x * α * x⁻¹ : S.O) : S.Qt ≃ₗ[ZMod 2] S.Qt)) =
      finrank (ZMod 2) (commSpace (α : S.Qt ≃ₗ[ZMod 2] S.Qt)) := by
    rw [S8.commSpace_conj, LinearEquiv.finrank_map_eq]
  omega

end A6

end CFSG.LargeExtraspecial.S9
