module

public import CFSG.Goldschmidt.Steps.G2Semi
public import CFSG.Goldschmidt.Steps.G2Grp
public import CFSG.Goldschmidt.Steps.G28

public section

namespace CFSG.Goldschmidt

open CFSG.Open CFSG.QuasithinUnique G2
open scoped Pointwise

theorem G210 : S_G210 := by
  intro G _ _ A X y h hsemi
  have : Fact (IsElemAbelian 2 A) := ⟨h.elem⟩
  have hL := linHyp_of_onanHyp h
  have hirr := irreducible_of_onanHyp h
  set η := conjRep h.le ⟨y, h.mem⟩ with hη
  have hfix : fixSp η = sub A (Subgroup.centralizer ({y} : Set G)) :=
    fixSp_conjRep h.le ⟨y, h.mem⟩
  have hsemiV : ∀ x ∈ (conjRep h.le).range, x • fixSp η ≠ fixSp η → ∀ k : ℕ,
      (η ^ k) • (x • fixSp η) = x • fixSp η → η ^ k = 1 := by
    rintro _ ⟨x, rfl⟩ hxW k hk
    have hxA : conjSub (x : G)⁻¹ A = A := conjSub_eq_of_mem_normalizer (h.le (X.inv_mem x.2))
    have hykA : conjSub (y ^ k)⁻¹ A = A :=
      conjSub_eq_of_mem_normalizer (h.le (X.inv_mem (X.pow_mem h.mem k)))
    rw [hfix, conjRep_smul_sub] at hxW hk
    rw [hη, ← conjRep_pow, conjRep_smul_sub, sub_eq_sub_iff] at hk
    rw [Ne, sub_eq_sub_iff] at hxW
    set W := A ⊓ Subgroup.centralizer ({y} : Set G) with hW
    have hxW' : conjSub (x : G)⁻¹ W ≠ W := by
      rwa [hW, conjSub_inf, hxA]
    have hk' : conjSub (y ^ k)⁻¹ (conjSub (x : G)⁻¹ W) = conjSub (x : G)⁻¹ W := by
      rw [hW, conjSub_inf, conjSub_inf, hxA, hykA]
      simpa using hk
    have hk'' : conjSub (y ^ k) (conjSub (x : G)⁻¹ W) = conjSub (x : G)⁻¹ W := by
      conv_lhs => rw [← hk']
      rw [conjSub_conjSub, inv_mul_cancel, conjSub_one]
    have hyk := hsemi _ (X.inv_mem x.2) hxW' k hk''
    rw [← conjRep_pow, conjRep_eq_one_iff]
    simpa using hyk
  have hk1 := hL.finrank_fixSp_eq_one hirr hsemiV
  have hW2 : Nat.card (A ⊓ Subgroup.centralizer ({y} : Set G) : Subgroup G) = 2 := by
    rw [← card_sub, ← hfix, ONan.natCard_submodule, hk1]
    norm_num
  refine ⟨hW2, ?_⟩
  set A₀ := subOf (comSp η) with hA₀def
  have hA₀ : A₀ ≤ A := subOf_le _
  have hfr := Submodule.finrank_add_eq_of_isCompl hL.isCompl
  rw [hk1] at hfr
  have hcardA : Nat.card A = 2 * Nat.card A₀ := by
    rw [card_subOf, ← card_additive, ONan.natCard_space, ONan.natCard_submodule, ← hfr, pow_succ,
      mul_comm]
  have hidx : (A₀.subgroupOf A).index = 2 := by
    have h1 := Subgroup.index_mul_card (A₀.subgroupOf A)
    rw [Nat.card_congr (Subgroup.subgroupOfEquivOfLe hA₀).toEquiv, hcardA] at h1
    have hpos : 0 < Nat.card A₀ := Nat.card_pos
    have := Nat.eq_of_mul_eq_mul_right hpos h1
    exact this
  have h4 : 4 ≤ Nat.card A := by
    have hm := hL.two_le_finrank_comSp
    rw [hcardA, card_subOf, ONan.natCard_submodule]
    calc 4 ≤ 2 * 2 ^ 2 := by norm_num
      _ ≤ 2 * 2 ^ Module.finrank (ZMod 2) (comSp η) :=
          Nat.mul_le_mul_left _ (Nat.pow_le_pow_right (by norm_num) hm)
  have hG28 := G28 G A X A₀ h.elem h4 h.le h.irreducible hA₀ hidx
  have hA₀com : ∀ g ∈ A₀, g ∈ ⁅A, Subgroup.zpowers y⁆ := by
    rintro g ⟨hgA, hgD⟩
    exact comSp_le_sub h.le ⟨y, h.mem⟩ hgD
  obtain ⟨d, hdD, hd0⟩ := Submodule.exists_mem_ne_zero_of_ne_bot hL.comSp_ne_bot
  have hdA₀ : ((Additive.toMul d : A) : G) ∈ A₀ := (mem_iff_mem_subOf d).mp hdD
  have hd1 : ((Additive.toMul d : A) : G) ≠ 1 := fun h1 => hd0 (by
    apply Additive.toMul.injective
    exact Subtype.ext h1)
  have key : ∀ b ∈ A, b ≠ 1 →
      ∃ x ∈ X, x⁻¹ * b * x = ((Additive.toMul d : A) : G) := by
    intro b hb hb1
    obtain ⟨n, hn, hnb⟩ := hG28 b hb hb1
    have hnb1 : n⁻¹ * b * n ≠ 1 := fun h1 => hb1 (by
      have : b = n * (n⁻¹ * b * n) * n⁻¹ := by group
      rw [this, h1]
      group)
    obtain ⟨k, hk⟩ := h.trans _ (hA₀com _ hnb) _ (hA₀com _ hdA₀) hnb1 hd1
    refine ⟨n * y ^ k, X.mul_mem hn (X.pow_mem h.mem k), ?_⟩
    rw [← hk]
    group
  intro b hb c hc hb1 hc1
  obtain ⟨x₁, hx₁, h1⟩ := key b hb hb1
  obtain ⟨x₂, hx₂, h2⟩ := key c hc hc1
  refine ⟨x₁ * x₂⁻¹, X.mul_mem hx₁ (X.inv_mem hx₂), ?_⟩
  calc (x₁ * x₂⁻¹)⁻¹ * b * (x₁ * x₂⁻¹) = x₂ * (x₁⁻¹ * b * x₁) * x₂⁻¹ := by group
    _ = x₂ * (x₂⁻¹ * c * x₂) * x₂⁻¹ := by rw [h1, h2]
    _ = c := by group

end CFSG.Goldschmidt
