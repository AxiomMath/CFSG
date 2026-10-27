module

public import CFSG.CGT.PushingUpLit.CGT6.EmbEndNat

public section

namespace CFSG.CGT.PushingUpLit.CGT6

open CFSG
open CFSG.Open (standardIsStandardSubgroup)

section Orders

variable {V : Type} [CommGroup V]

theorem YSL5.card_eq {Y : Subgroup (MulAut V)} (h : YSL5 Y) : Nat.card ↥Y = 120 := by
  obtain ⟨e⟩ := h
  have : Fact (Nat.Prime 5) := ⟨by norm_num⟩
  rw [Nat.card_congr e.toEquiv, CFSG.SL2MinimalFaithful.card_specialLinearGroup_fin_two,
    Nat.card_zmod]
  norm_num

theorem not_ysl5_of_ysl {Y : Subgroup (MulAut V)} {f : ℕ} (hf : 2 ≤ f) (h : YSL Y f) :
    ¬ YSL5 Y := by
  intro h5
  have h1 := h.card_eq (by omega)
  have h2 := h5.card_eq
  rw [h1] at h2
  rcases (show f = 2 ∨ 3 ≤ f by omega) with rfl | h3
  · norm_num at h2
  · have ha : 2 ^ 3 ≤ 2 ^ f := Nat.pow_le_pow_right (by norm_num) h3
    have hb : 2 ^ 6 ≤ 2 ^ (2 * f) := Nat.pow_le_pow_right (by norm_num) (by omega)
    have hc : 2 ^ 3 * (2 ^ 6 - 1) ≤ 2 ^ f * (2 ^ (2 * f) - 1) :=
      Nat.mul_le_mul ha (Nat.sub_le_sub_right hb 1)
    omega

theorem not_ysl5_of_yAlt {Y : Subgroup (MulAut V)} {m : ℕ} (hm : 7 ≤ m) (h : YAlt Y m) :
    ¬ YSL5 Y := by
  intro h5
  obtain ⟨e⟩ := h
  have : Nontrivial (Fin m) := Fin.nontrivial_iff_two_le.mpr (by omega)
  have h1 : Nat.card ↥Y = Nat.card (alternatingGroup (Fin m)) := Nat.card_congr e.toEquiv
  rw [h5.card_eq, nat_card_alternatingGroup, Nat.card_eq_fintype_card (α := Fin m),
    Fintype.card_fin] at h1
  have h2 : Nat.factorial 7 ≤ Nat.factorial m := Nat.factorial_le hm
  have h3 : Nat.factorial 7 = 5040 := by decide
  omega

end Orders

section Std

variable {V : Type} [CommGroup V] [Finite V] {G T Y : Subgroup (MulAut V)}

theorem EndCfg4.std_of_YSL (h : EndCfg4 G T Y) {f : ℕ} (hf : 2 ≤ f) (hY : YSL Y f) :
    standardIsStandardSubgroup (Y.subgroupOf G) :=
  h.std.resolve_right fun ht => not_ysl5_of_ysl hf hY ht.1

theorem EndCfg4.std_of_YAlt (h : EndCfg4 G T Y) {m : ℕ} (hm : 7 ≤ m) (hY : YAlt Y m) :
    standardIsStandardSubgroup (Y.subgroupOf G) :=
  h.std.resolve_right fun ht => not_ysl5_of_yAlt hm hY ht.1

end Std

end CFSG.CGT.PushingUpLit.CGT6
