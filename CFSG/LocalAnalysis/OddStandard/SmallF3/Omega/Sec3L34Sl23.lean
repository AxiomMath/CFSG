module

public import CFSG.LocalAnalysis.OddStandard.SmallF3.Omega.Defs

public section

namespace CFSG.OddStandard.SmallF3.Omega

open Subgroup

variable {G : Type} [Group G]

private abbrev SL23 := Matrix.SpecialLinearGroup (Fin 2) (ZMod 3)

private def slA : SL23 := ⟨!![0, 1; -1, 0], by rw [Matrix.det_fin_two_of]; decide⟩

private def slB : SL23 := ⟨!![1, 1; 1, -1], by rw [Matrix.det_fin_two_of]; decide⟩

private def quatToSlFun : QuaternionGroup 2 → SL23
  | QuaternionGroup.a i => slA ^ i.val
  | QuaternionGroup.xa i => slB * slA ^ i.val

private lemma quatToSlFun_map_mul :
    ∀ a b : QuaternionGroup 2, quatToSlFun (a * b) = quatToSlFun a * quatToSlFun b := by
  decide +kernel

private lemma quatToSlFun_injective : Function.Injective quatToSlFun := by
  decide +kernel

private def quatToSl : QuaternionGroup 2 →* SL23 :=
  MonoidHom.mk' quatToSlFun quatToSlFun_map_mul

private lemma sl_pow_four_of_pow_eight : ∀ g : SL23, g ^ 8 = 1 → g ^ 4 = 1 := by
  decide +kernel

private def slQ8 : Subgroup SL23 where
  carrier := {g | g ^ 4 = 1}
  mul_mem' := by decide +kernel
  one_mem' := by decide
  inv_mem' := by decide +kernel

private lemma quatToSl_range_le_slQ8 : quatToSl.range ≤ slQ8 := by
  intro g hg
  obtain ⟨x, rfl⟩ := hg
  show (quatToSl x) ^ 4 = 1
  have hx : x ^ 4 = 1 := by revert x; decide +kernel
  rw [← map_pow, hx, map_one]

private lemma mem_quatToSl_range_of_pow_four :
    ∀ g : SL23, g ^ 4 = 1 → ∃ x : QuaternionGroup 2, quatToSl x = g := by
  decide +kernel

private lemma slQ8_le_quatToSl_range : slQ8 ≤ quatToSl.range := by
  intro g hg
  exact mem_quatToSl_range_of_pow_four g hg

private lemma quatToSl_range_eq_slQ8 : quatToSl.range = slQ8 :=
  le_antisymm quatToSl_range_le_slQ8 slQ8_le_quatToSl_range

private lemma slQ8_normal : slQ8.Normal := by
  constructor
  intro n hn g
  show (g * n * g⁻¹) ^ 4 = 1
  have h : g * n * g⁻¹ = (MulAut.conj g) n := by simp [MulAut.conj_apply]
  rw [h, ← map_pow, hn, map_one]

private lemma card_quaternionGroup_two : Nat.card (QuaternionGroup 2) = 8 := by
  rw [Nat.card_eq_fintype_card, QuaternionGroup.card]

private lemma slQ8_card : Nat.card slQ8 = 8 := by
  have hrange : Nat.card quatToSl.range = 8 :=
    (Nat.card_congr
        (MonoidHom.ofInjective (f := quatToSl) quatToSlFun_injective).toEquiv).symm.trans
      card_quaternionGroup_two
  rw [← quatToSl_range_eq_slQ8]
  exact hrange

private lemma eq_slQ8_of_card_eq_eight (T : Subgroup SL23) (hT : Nat.card T = 8) :
    T = slQ8 := by
  apply Subgroup.eq_of_le_of_card_ge
  · intro g hg
    have h8' : (⟨g, hg⟩ : T) ^ Nat.card T = 1 := pow_card_eq_one'
    have h8 : g ^ 8 = 1 := by
      have h := congrArg (fun x : T => (x : SL23)) h8'
      simpa [hT] using h
    exact sl_pow_four_of_pow_eight g h8
  · rw [slQ8_card, hT]

theorem normal_of_natCard_eq_eight_sl23
    (T : Subgroup (Matrix.SpecialLinearGroup (Fin 2) (ZMod 3))) (hT : Nat.card T = 8) :
    T.Normal := by
  rw [eq_slQ8_of_card_eq_eight T hT]
  exact slQ8_normal

theorem nonempty_mulEquiv_quaternion_of_natCard_eq_eight_sl23
    (T : Subgroup (Matrix.SpecialLinearGroup (Fin 2) (ZMod 3))) (hT : Nat.card T = 8) :
    Nonempty (QuaternionGroup 2 ≃* T) := by
  have hTeq : T = slQ8 := eq_slQ8_of_card_eq_eight T hT
  have h : QuaternionGroup 2 ≃* slQ8 :=
    (MonoidHom.ofInjective (f := quatToSl) quatToSlFun_injective).trans
      (MulEquiv.subgroupCongr quatToSl_range_eq_slQ8)
  exact ⟨h.trans (MulEquiv.subgroupCongr hTeq).symm⟩

end CFSG.OddStandard.SmallF3.Omega
