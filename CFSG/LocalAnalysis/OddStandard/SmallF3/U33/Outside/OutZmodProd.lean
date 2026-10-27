module

public import Mathlib.GroupTheory.NoncommCoprod
public import CFSG.GH74.GLS.Bg.TwoGroups.Models

public section

namespace CFSG.OddStandard.SmallF3.HarrisU33.Outside

open Subgroup CFSG.GH74.GLS.Bg.TwoGroups

private noncomputable def zmodPowersHom {G : Type*} [Group G] (a : G) (m : ℕ) [NeZero m]
    (ha : orderOf a = m) : Multiplicative (ZMod m) →* G where
  toFun i := a ^ i.toAdd.val
  map_one' := by
    show a ^ (Multiplicative.toAdd (1 : Multiplicative (ZMod m))).val = 1
    rw [toAdd_one, ZMod.val_zero, pow_zero]
  map_mul' i k := by
    show a ^ (Multiplicative.toAdd (i * k)).val =
      a ^ (Multiplicative.toAdd i).val * a ^ (Multiplicative.toAdd k).val
    rw [toAdd_mul, ZMod.val_add]
    rw [show ((Multiplicative.toAdd i).val + (Multiplicative.toAdd k).val) % m =
        ((Multiplicative.toAdd i).val + (Multiplicative.toAdd k).val) % orderOf a by rw [ha]]
    rw [pow_mod_orderOf, pow_add]

@[simp] private theorem zmodPowersHom_ofAdd_apply {G : Type*} [Group G] (a : G) (m : ℕ)
    [NeZero m] (ha : orderOf a = m) (i : ZMod m) :
    zmodPowersHom a m ha (Multiplicative.ofAdd i) = a ^ i.val := rfl

private theorem pow_val_one {G : Type*} [Group G] (a : G) (m : ℕ) [NeZero m]
    (ha : orderOf a = m) : a ^ (1 : ZMod m).val = a := by
  rw [ZMod.val_one_eq_one_mod]
  rw [show 1 % m = 1 % orderOf a by rw [ha]]
  rw [pow_mod_orderOf, pow_one]

private theorem zmodPowersHom_ofAdd_one {G : Type*} [Group G] (a : G) (m : ℕ) [NeZero m]
    (ha : orderOf a = m) : zmodPowersHom a m ha (Multiplicative.ofAdd 1) = a := by
  rw [zmodPowersHom_ofAdd_apply, pow_val_one a m ha]

private theorem zmodPowersHom_injective {G : Type*} [Group G] (a : G) (m : ℕ) [NeZero m]
    (ha : orderOf a = m) : Function.Injective (zmodPowersHom a m ha) := by
  intro i k hik
  change a ^ i.toAdd.val = a ^ k.toAdd.val at hik
  have hi : i.toAdd.val < orderOf a := by rw [ha]; exact ZMod.val_lt i.toAdd
  have hk : k.toAdd.val < orderOf a := by rw [ha]; exact ZMod.val_lt k.toAdd
  have hval : i.toAdd.val = k.toAdd.val := pow_injOn_Iio_orderOf (x := a) hi hk hik
  exact Multiplicative.toAdd.injective (ZMod.val_injective m hval)

private theorem zmodPowersHom_range {G : Type*} [Group G] (a : G) (m : ℕ) [NeZero m]
    (ha : orderOf a = m) : (zmodPowersHom a m ha).range = zpowers a := by
  apply le_antisymm
  · rintro x ⟨i, rfl⟩
    exact Subgroup.npow_mem_zpowers a i.toAdd.val
  · rw [Subgroup.zpowers_le]
    exact ⟨Multiplicative.ofAdd 1, zmodPowersHom_ofAdd_one a m ha⟩

private theorem zmodPowersHom_commute {G : Type*} [Group G] (a b : G) (m : ℕ) [NeZero m]
    (ha : orderOf a = m) (hb : orderOf b = m) (hab : Commute a b) :
    ∀ x y : Multiplicative (ZMod m), Commute (zmodPowersHom a m ha x) (zmodPowersHom b m hb y) :=
  fun x y => hab.pow_pow x.toAdd.val y.toAdd.val

private noncomputable def zmodProdHom {G : Type*} [Group G] (a b : G) (m : ℕ) [NeZero m]
    (ha : orderOf a = m) (hb : orderOf b = m) (hab : Commute a b) :
    Multiplicative (ZMod m × ZMod m) →* G :=
  (MonoidHom.noncommCoprod (zmodPowersHom a m ha) (zmodPowersHom b m hb)
    (zmodPowersHom_commute a b m ha hb hab)).comp
      (MulEquiv.prodMultiplicative (ZMod m) (ZMod m))

@[simp] private theorem zmodProdHom_ofAdd_apply {G : Type*} [Group G] (a b : G) (m : ℕ)
    [NeZero m] (ha : orderOf a = m) (hb : orderOf b = m) (hab : Commute a b) (i j : ZMod m) :
    zmodProdHom a b m ha hb hab (Multiplicative.ofAdd (i, j)) = a ^ i.val * b ^ j.val := by
  rw [zmodProdHom, MonoidHom.comp_apply]
  change (MonoidHom.noncommCoprod (zmodPowersHom a m ha) (zmodPowersHom b m hb)
      (zmodPowersHom_commute a b m ha hb hab))
      (Multiplicative.ofAdd i, Multiplicative.ofAdd j) = a ^ i.val * b ^ j.val
  rw [MonoidHom.noncommCoprod_apply, zmodPowersHom_ofAdd_apply, zmodPowersHom_ofAdd_apply]

private theorem zmodProdHom_ofAdd_one_zero {G : Type*} [Group G] (a b : G) (m : ℕ) [NeZero m]
    (ha : orderOf a = m) (hb : orderOf b = m) (hab : Commute a b) :
    zmodProdHom a b m ha hb hab (Multiplicative.ofAdd (1, 0)) = a := by
  rw [zmodProdHom_ofAdd_apply, pow_val_one a m ha, ZMod.val_zero, pow_zero, mul_one]

private theorem zmodProdHom_ofAdd_zero_one {G : Type*} [Group G] (a b : G) (m : ℕ) [NeZero m]
    (ha : orderOf a = m) (hb : orderOf b = m) (hab : Commute a b) :
    zmodProdHom a b m ha hb hab (Multiplicative.ofAdd (0, 1)) = b := by
  rw [zmodProdHom_ofAdd_apply, ZMod.val_zero, pow_zero, pow_val_one b m hb, one_mul]

private theorem zmodProdHom_injective {G : Type*} [Group G] (a b : G) (m : ℕ) [NeZero m]
    (ha : orderOf a = m) (hb : orderOf b = m) (hab : Commute a b)
    (h : zpowers a ⊓ zpowers b = ⊥) :
    Function.Injective (zmodProdHom a b m ha hb hab) := by
  let g := MonoidHom.noncommCoprod (zmodPowersHom a m ha) (zmodPowersHom b m hb)
    (zmodPowersHom_commute a b m ha hb hab)
  have hg : Function.Injective g :=
    (MonoidHom.noncommCoprod_injective (zmodPowersHom a m ha) (zmodPowersHom b m hb)
      (zmodPowersHom_commute a b m ha hb hab)).mpr
      ⟨zmodPowersHom_injective a m ha, zmodPowersHom_injective b m hb, by
        rw [zmodPowersHom_range a m ha, zmodPowersHom_range b m hb]
        exact disjoint_iff.mpr h⟩
  intro x y hxy
  have hgxy := hxy
  simp only [zmodProdHom, MonoidHom.comp_apply, g] at hgxy
  exact (MulEquiv.prodMultiplicative (ZMod m) (ZMod m)).injective (hg hgxy)

private theorem zmodProdHom_range {G : Type*} [Group G] (a b : G) (m : ℕ) [NeZero m]
    (ha : orderOf a = m) (hb : orderOf b = m) (hab : Commute a b) :
    (zmodProdHom a b m ha hb hab).range = zpowers a ⊔ zpowers b := by
  apply le_antisymm
  · rintro x ⟨y, rfl⟩
    obtain ⟨i, j, rfl⟩ : ∃ i j : ZMod m, y = Multiplicative.ofAdd (i, j) := by
      cases y with
      | ofAdd p => cases p with
        | mk i j => exact ⟨i, j, rfl⟩
    rw [zmodProdHom_ofAdd_apply]
    exact Subgroup.mul_mem_sup (Subgroup.npow_mem_zpowers a i.val)
      (Subgroup.npow_mem_zpowers b j.val)
  · rw [sup_le_iff]
    constructor
    · rw [Subgroup.zpowers_le]
      exact ⟨Multiplicative.ofAdd (1, 0), zmodProdHom_ofAdd_one_zero a b m ha hb hab⟩
    · rw [Subgroup.zpowers_le]
      exact ⟨Multiplicative.ofAdd (0, 1), zmodProdHom_ofAdd_zero_one a b m ha hb hab⟩

theorem exists_hom_zmod_prod {G : Type*} [Group G] (a b : G) (hab : a * b = b * a) (m : ℕ)
    [NeZero m] (ha : orderOf a = m) (hb : orderOf b = m) (h : zpowers a ⊓ zpowers b = ⊥) :
    ∃ φ : Multiplicative (ZMod m × ZMod m) →* G, Function.Injective φ ∧
      φ.range = zpowers a ⊔ zpowers b ∧ φ (Multiplicative.ofAdd (1, 0)) = a ∧
        φ (Multiplicative.ofAdd (0, 1)) = b := by
  refine ⟨zmodProdHom a b m ha hb hab, zmodProdHom_injective a b m ha hb hab h,
    zmodProdHom_range a b m ha hb hab, zmodProdHom_ofAdd_one_zero a b m ha hb hab,
    zmodProdHom_ofAdd_zero_one a b m ha hb hab⟩

theorem exists_mulEquiv_zmod_prod {G : Type*} [Group G] (a b : G) (hab : a * b = b * a) (m : ℕ)
    [NeZero m] (ha : orderOf a = m) (hb : orderOf b = m) (h : zpowers a ⊓ zpowers b = ⊥) :
    Nonempty (↥(zpowers a ⊔ zpowers b) ≃* Multiplicative (ZMod m × ZMod m)) := by
  obtain ⟨φ, hφinj, hφrange, -, -⟩ := exists_hom_zmod_prod a b hab m ha hb h
  exact ⟨((MonoidHom.ofInjective hφinj).trans (MulEquiv.subgroupCongr hφrange)).symm⟩

theorem exists_mulEquiv_Z4Z4 {G : Type*} [Group G] (a b : G) (hab : a * b = b * a)
    (ha : orderOf a = 4) (hb : orderOf b = 4) (h : zpowers a ⊓ zpowers b = ⊥) :
    Nonempty (↥(zpowers a ⊔ zpowers b) ≃* Z4Z4) := by
  obtain ⟨e⟩ := exists_mulEquiv_zmod_prod a b hab 4 ha hb h
  exact ⟨e⟩

theorem card_zpowers_sup_zpowers {G : Type*} [Group G] (a b : G) (hab : a * b = b * a) (m : ℕ)
    [NeZero m] (ha : orderOf a = m) (hb : orderOf b = m) (h : zpowers a ⊓ zpowers b = ⊥) :
    Nat.card ↥(zpowers a ⊔ zpowers b) = m * m := by
  obtain ⟨e⟩ := exists_mulEquiv_zmod_prod a b hab m ha hb h
  rw [Nat.card_congr e.toEquiv, Nat.card_congr Multiplicative.toAdd, Nat.card_prod,
    Nat.card_zmod]

end CFSG.OddStandard.SmallF3.HarrisU33.Outside
