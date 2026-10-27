module

public import CFSG.Open.Catalog

public section

attribute [-instance] instAddCommGroupOfIsSimpleAddGroupOfIsNilpotent
  instCommGroupOfIsSimpleGroupOfIsNilpotent

namespace CFSG.LocalAnalysis.RankThreeTheoremC.A6.I1435

open Subgroup CFSG.Open

abbrev M3 : Type := Multiplicative (ZMod 3)

abbrev W3 : Type := M3 ≀ᵣ M3

@[expose] def wBase : Subgroup W3 := (RegularWreathProduct.rightHom : W3 →* M3).ker

theorem mem_wBase {w : W3} : w ∈ wBase ↔ w.right = 1 := MonoidHom.mem_ker

theorem card_M3 : Nat.card M3 = 3 := by
  rw [Nat.card_eq_fintype_card]
  rfl

theorem card_W3 : Nat.card W3 = 81 := by
  rw [RegularWreathProduct.card, card_M3]
  norm_num

@[expose] def wBaseEquiv : ↥wBase ≃ (M3 → M3) where
  toFun w := (w : W3).left
  invFun f := ⟨⟨f, 1⟩, mem_wBase.mpr rfl⟩
  left_inv w := Subtype.ext (RegularWreathProduct.ext rfl (mem_wBase.mp w.2).symm)
  right_inv _ := rfl

theorem card_wBase : Nat.card wBase = 27 := by
  rw [Nat.card_congr wBaseEquiv, Nat.card_fun, card_M3]
  norm_num

theorem wBase_comm {a b : W3} (ha : a ∈ wBase) (hb : b ∈ wBase) : a * b = b * a := by
  rw [mem_wBase] at ha hb
  refine RegularWreathProduct.ext ?_ ?_
  · rw [RegularWreathProduct.mul_left, RegularWreathProduct.mul_left, ha, hb]
    simp only [inv_one, one_mul]
    exact mul_comm _ _
  · rw [RegularWreathProduct.mul_right, RegularWreathProduct.mul_right, ha, hb]

theorem M3_orbit : ∀ t x y : M3, t ≠ 1 → y = x ∨ y = t * x ∨ y = t * (t * x) := by
  decide

theorem left_const_of_commute {a b : W3} (ha : a.right ≠ 1) (hb : b.right = 1)
    (h : b * a = a * b) (x y : M3) : b.left x = b.left y := by
  have hl := congrArg RegularWreathProduct.left h
  rw [RegularWreathProduct.mul_left, RegularWreathProduct.mul_left, hb] at hl
  have hinv : ∀ z, b.left (a.right⁻¹ * z) = b.left z := by
    intro z
    have hz := congrFun hl z
    simp only [Pi.mul_apply, inv_one, one_mul] at hz
    rw [mul_comm (b.left z)] at hz
    exact (mul_left_cancel hz).symm
  have ht : a.right⁻¹ ≠ 1 := inv_ne_one.mpr ha
  rcases M3_orbit _ x y ht with rfl | rfl | rfl
  · rfl
  · exact (hinv x).symm
  · rw [hinv, hinv]

theorem eq_wBase_of_comm {A : Subgroup W3} (hA : ∀ a ∈ A, ∀ b ∈ A, a * b = b * a)
    (h27 : 27 ≤ Nat.card A) : A = wBase := by
  have hle : A ≤ wBase := by
    by_contra hn
    obtain ⟨a, haA, haB⟩ := SetLike.not_le_iff_exists.mp hn
    have ha : a.right ≠ 1 := fun h => haB (mem_wBase.mpr h)
    have hcard : Nat.card ↥(A ⊓ wBase) ≤ 3 := by
      have hinj : Function.Injective fun b : ↥(A ⊓ wBase) => (b : W3).left 1 := by
        intro b c hbc
        have hb := left_const_of_commute ha (mem_wBase.mp b.2.2) (hA _ b.2.1 _ haA)
        have hc := left_const_of_commute ha (mem_wBase.mp c.2.2) (hA _ c.2.1 _ haA)
        refine Subtype.ext (RegularWreathProduct.ext (funext fun x => ?_) ?_)
        · rw [hb x 1, hc x 1]
          exact hbc
        · rw [mem_wBase.mp b.2.2, mem_wBase.mp c.2.2]
      exact (Nat.card_le_card_of_injective _ hinj).trans card_M3.le
    have hidx : (A ⊓ wBase).index ≤ A.index * wBase.index := Subgroup.index_inf_le
    have h1 := Subgroup.card_mul_index A
    have h2 := Subgroup.card_mul_index wBase
    have h3 := Subgroup.card_mul_index (A ⊓ wBase)
    rw [card_W3] at h1 h2 h3
    rw [card_wBase] at h2
    have hBi : wBase.index = 3 := by omega
    have hAi : A.index ≤ 3 := by
      by_contra hc
      have : 27 * 4 ≤ Nat.card A * A.index := Nat.mul_le_mul h27 (by omega)
      omega
    have hI : (A ⊓ wBase).index ≤ 9 := by
      rw [hBi] at hidx
      calc (A ⊓ wBase).index ≤ A.index * 3 := hidx
        _ ≤ 3 * 3 := Nat.mul_le_mul_right 3 hAi
    have : Nat.card ↥(A ⊓ wBase) * (A ⊓ wBase).index ≤ 3 * 9 := Nat.mul_le_mul hcard hI
    omega
  exact Subgroup.eq_of_le_of_card_ge hle (by rw [card_wBase]; exact h27)

theorem eq_bot_of_normal {N : Subgroup W3} (hN : ∀ w : W3, ∀ n ∈ N, w * n * w⁻¹ ∈ N)
    (hNB : N ⊓ wBase = ⊥) : N = ⊥ := by
  rw [eq_bot_iff]
  intro n hn
  rw [mem_bot]
  by_contra hn1
  have hr : n.right ≠ 1 := by
    intro h
    have hmem : n ∈ N ⊓ wBase := ⟨hn, mem_wBase.mpr h⟩
    rw [hNB, mem_bot] at hmem
    exact hn1 hmem
  let b : W3 := ⟨fun x => x, 1⟩
  have hd : b * n * b⁻¹ * n⁻¹ ∈ N ⊓ wBase := by
    refine Subgroup.mem_inf.mpr ⟨mul_mem (hN b n hn) (inv_mem hn), mem_wBase.mpr ?_⟩
    simp [b]
  rw [hNB, mem_bot, mul_inv_eq_one, mul_inv_eq_iff_eq_mul] at hd
  have h := left_const_of_commute hr rfl hd 1 (Multiplicative.ofAdd 1)
  exact absurd h (by decide)

section Transport

variable {X : Type*} [Group X] {P : Subgroup X} (e : ↥P ≃* W3)

@[expose] def baseIn : Subgroup X := (wBase.map e.symm.toMonoidHom).map P.subtype

theorem baseIn_le : baseIn e ≤ P := map_subtype_le _

include e in
theorem card_of_equiv : Nat.card P = 81 := by
  rw [Nat.card_congr e.toEquiv, card_W3]

theorem card_baseIn : Nat.card (baseIn e) = 27 := by
  rw [baseIn, card_map_of_injective P.subtype_injective,
    card_map_of_injective e.symm.injective, card_wBase]

theorem baseIn_comm {a b : X} (ha : a ∈ baseIn e) (hb : b ∈ baseIn e) : a * b = b * a := by
  obtain ⟨a', ⟨a'', ha'', rfl⟩, rfl⟩ := ha
  obtain ⟨b', ⟨b'', hb'', rfl⟩, rfl⟩ := hb
  simp only [subtype_apply, MulEquiv.coe_toMonoidHom]
  rw [← Subgroup.coe_mul, ← Subgroup.coe_mul, ← map_mul, ← map_mul, wBase_comm ha'' hb'']

theorem eq_baseIn_of_comm {A : Subgroup X} (hAP : A ≤ P) (hA : ∀ a ∈ A, ∀ b ∈ A, a * b = b * a)
    (h27 : 27 ≤ Nat.card A) : A = baseIn e := by
  set A' : Subgroup W3 := (A.subgroupOf P).map e.toMonoidHom with hA'
  have hA'c : ∀ a ∈ A', ∀ b ∈ A', a * b = b * a := by
    rintro _ ⟨a, ha, rfl⟩ _ ⟨b, hb, rfl⟩
    simp only [MulEquiv.coe_toMonoidHom]
    rw [← map_mul, ← map_mul]
    congr 1
    exact Subtype.ext (hA _ ha _ hb)
  have hcard : Nat.card A' = Nat.card A := by
    rw [hA', card_map_of_injective e.injective, Nat.card_congr (subgroupOfEquivOfLe hAP).toEquiv]
  have hA'B : A' = wBase := eq_wBase_of_comm hA'c (hcard ▸ h27)
  have hsub : A.subgroupOf P = wBase.map e.symm.toMonoidHom := by
    rw [← hA'B, hA', map_map]
    have : e.symm.toMonoidHom.comp e.toMonoidHom = MonoidHom.id _ := by
      ext x
      simp
    rw [this, map_id]
  rw [baseIn, ← hsub, map_subgroupOf_eq_of_le hAP]

theorem thompsonSubgroup_eq_baseIn [Finite X] : thompsonSubgroup P = baseIn e := by
  have hfam : ambientMaxCardAbelianFamily P = {baseIn e} := by
    ext A
    simp only [Set.mem_singleton_iff]
    constructor
    · rintro ⟨hAP, hAc, hmax⟩
      have hle := hmax (baseIn e) (baseIn_le e)
        ⟨⟨fun a b => Subtype.ext (baseIn_comm e a.2 b.2)⟩⟩
      rw [card_baseIn] at hle
      exact eq_baseIn_of_comm e hAP (fun a ha b hb => congrArg Subtype.val
        (hAc.is_comm.comm ⟨a, ha⟩ ⟨b, hb⟩)) hle
    · rintro rfl
      refine ⟨baseIn_le e, ⟨⟨fun a b => Subtype.ext (baseIn_comm e a.2 b.2)⟩⟩, ?_⟩
      intro B hBP hBc
      by_contra hlt
      rw [not_le, card_baseIn] at hlt
      have hB := eq_baseIn_of_comm e hBP (fun a ha b hb => congrArg Subtype.val
        (hBc.is_comm.comm ⟨a, ha⟩ ⟨b, hb⟩)) hlt.le
      rw [hB, card_baseIn] at hlt
      exact lt_irrefl _ hlt
  rw [thompsonSubgroup, ambientMaxCardThompson, hfam, sSup_singleton]

theorem eq_bot_of_normalized {N : Subgroup X} (hNP : N ≤ P)
    (hN : ∀ p ∈ P, ∀ n ∈ N, p * n * p⁻¹ ∈ N) (hNB : N ⊓ baseIn e = ⊥) : N = ⊥ := by
  set N' : Subgroup W3 := (N.subgroupOf P).map e.toMonoidHom with hN'
  have hnorm : ∀ w : W3, ∀ n ∈ N', w * n * w⁻¹ ∈ N' := by
    rintro w _ ⟨n, hn, rfl⟩
    refine ⟨e.symm w * n * (e.symm w)⁻¹, ?_, ?_⟩
    · rw [SetLike.mem_coe, mem_subgroupOf] at hn ⊢
      simpa using hN _ (e.symm w).2 _ hn
    · simp
  have hbot : N' ⊓ wBase = ⊥ := by
    rw [eq_bot_iff]
    rintro _ ⟨⟨n, hn, rfl⟩, hnB⟩
    rw [mem_bot]
    have hmem : (n : X) ∈ N ⊓ baseIn e := by
      refine ⟨hn, ⟨n, ⟨e n, hnB, by simp⟩, rfl⟩⟩
    rw [hNB, mem_bot] at hmem
    have : n = 1 := Subtype.ext hmem
    simp [this]
  have h := eq_bot_of_normal hnorm hbot
  rw [hN', map_eq_bot_iff_of_injective _ e.injective] at h
  rw [eq_bot_iff]
  intro n hn
  have : (⟨n, hNP hn⟩ : ↥P) ∈ N.subgroupOf P := hn
  rw [h, mem_bot] at this
  rw [mem_bot]
  exact congrArg Subtype.val this

end Transport

end CFSG.LocalAnalysis.RankThreeTheoremC.A6.I1435
