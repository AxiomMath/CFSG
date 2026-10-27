module

public import CFSG.LocalAnalysis.ComponentClassification.GSThmBCatalog82A10Perm
public import Mathlib.GroupTheory.SpecificGroups.Dihedral

public section

namespace CFSG.ComponentClassification.GSThmB.P29.A10

open Equiv Equiv.Perm Subgroup CFSG.ComponentClassification.GSThmB.Catalog82A10

@[expose] def rhoA : Perm (Fin 10) := swap 0 3 * swap 0 1 * swap 0 2

@[expose] def t0 : Perm (Fin 10) := swap 0 4 * swap 1 5 * swap 2 6 * swap 3 7

@[expose] def aMap : DihedralGroup 4 → Perm (Fin 10)
  | .r i => rhoA ^ i.val
  | .sr i => swap 0 1 * rhoA ^ i.val

@[expose] def bMap (y : DihedralGroup 4) : Perm (Fin 10) := t0 * aMap y * t0⁻¹

@[expose] def cMap (z : Multiplicative (ZMod 2)) : Perm (Fin 10) :=
  swap 8 9 ^ (Multiplicative.toAdd z).val

abbrev W : Type := (DihedralGroup 4 × DihedralGroup 4) × Multiplicative (ZMod 2)

@[expose] def phiFun (w : W) : Perm (Fin 10) := aMap w.1.1 * bMap w.1.2 * cMap w.2

@[expose] def swapW (w : W) : W := ((w.1.2, w.1.1), w.2)

@[expose] def parD : DihedralGroup 4 → Multiplicative (ZMod 2)
  | .r i => Multiplicative.ofAdd (i.val : ZMod 2)
  | .sr i => Multiplicative.ofAdd ((i.val + 1 : ℕ) : ZMod 2)

theorem aMap_mul : ∀ x y : DihedralGroup 4, aMap (x * y) = aMap x * aMap y := by decide

theorem cMap_mul : ∀ x y : Multiplicative (ZMod 2), cMap (x * y) = cMap x * cMap y := by decide

theorem comm_ab : ∀ x y : DihedralGroup 4, aMap x * bMap y = bMap y * aMap x := by decide

theorem comm_abc : ∀ (v : DihedralGroup 4 × DihedralGroup 4) (z : Multiplicative (ZMod 2)),
    aMap v.1 * bMap v.2 * cMap z = cMap z * (aMap v.1 * bMap v.2) := by decide +kernel

@[expose] def aHom : DihedralGroup 4 →* Perm (Fin 10) := MonoidHom.mk' aMap aMap_mul

@[expose] def bHom : DihedralGroup 4 →* Perm (Fin 10) := (MulAut.conj t0).toMonoidHom.comp aHom

@[expose] def cHom : Multiplicative (ZMod 2) →* Perm (Fin 10) := MonoidHom.mk' cMap cMap_mul

@[expose] def phi : W →* Perm (Fin 10) :=
  (aHom.noncommCoprod bHom fun x y => comm_ab x y).noncommCoprod cHom fun v z => comm_abc v z

theorem phi_apply (w : W) : phi w = phiFun w := rfl

theorem phiFun_eq_one : ∀ w : W, phiFun w = 1 → w = 1 := by decide +kernel

theorem phiFun_comm : ∀ w : W, phiFun w * sigmaTwo = sigmaTwo * phiFun w := by decide +kernel

theorem t0_mul_self : t0 * t0 = 1 := by decide

theorem sign_t0 : sign t0 = 1 := by decide +kernel

theorem t0_not_comm : t0 * sigmaTwo ≠ sigmaTwo * t0 := by decide

theorem sigmaTwo_fix : ∀ x ∈ fixTwo, sigmaTwo x = x := by decide

theorem t0_phiFun : ∀ w : W, t0 * phiFun w * t0 = phiFun (swapW w) := by decide +kernel

theorem altOn_iff : ∀ w : W, (sign (phiFun w) = 1 ∧ (phiFun w).support ⊆ fixTwo) ↔
    (w.1.1 = 1 ∧ parD w.1.2 = w.2) := by decide +kernel

theorem sign_iff : ∀ w : W, sign (phiFun w) = 1 ↔ parD w.1.1 * parD w.1.2 = w.2 := by
  decide +kernel

theorem parD_mul : ∀ x y : DihedralGroup 4, parD (x * y) = parD x * parD y := by decide

theorem parD_one : parD 1 = 1 := by decide

theorem parD_xor : ∀ b : DihedralGroup 4, Xor (parD (b * DihedralGroup.sr 0) = 1) (parD b = 1) := by
  decide

theorem fix_iff : ∀ x : DihedralGroup 4,
    (∀ y ∈ fixTwo, phiFun ((x, 1), parD x) y = y) ↔ parD x = 1 := by decide +kernel

theorem phiFun_outer : ∀ x : DihedralGroup 4, parD x ≠ 1 → ∀ y ∈ fixTwo,
    phiFun ((x, 1), parD x) y = swap 8 9 y := by decide +kernel

theorem phiFun_sigmaTwo :
    phiFun ((DihedralGroup.r 2, 1), parD (DihedralGroup.r 2)) = sigmaTwo := by
  decide

@[expose] def P : Subgroup (Perm (Fin 10)) := phi.range

theorem mem_P {g : Perm (Fin 10)} : g ∈ P ↔ ∃ w, phiFun w = g := MonoidHom.mem_range

theorem phi_injective : Function.Injective phi := by
  rw [← MonoidHom.ker_eq_bot_iff, eq_bot_iff]
  intro w hw
  exact (mem_bot).mpr (phiFun_eq_one w hw)

theorem card_P : Nat.card P = 128 := by
  rw [P, ← Nat.card_congr (MonoidHom.ofInjective phi_injective).toEquiv, Nat.card_prod,
    Nat.card_prod, DihedralGroup.nat_card, Nat.card_eq_fintype_card]
  rfl

theorem isPGroup_P : IsPGroup 2 P := IsPGroup.of_card (n := 7) (by rw [card_P]; norm_num)

theorem P_le_centralizer : P ≤ centralizer ({sigmaTwo} : Set (Perm (Fin 10))) := by
  rintro _ ⟨w, rfl⟩
  rw [mem_centralizer_iff]
  rintro _ rfl
  exact (phiFun_comm w).symm

theorem card_centralizer_sigmaTwo :
    Nat.card (centralizer ({sigmaTwo} : Set (Perm (Fin 10)))) = 5760 := by
  rw [card_centralizer_of_orderOf_two orderOf_sigmaTwo, card_support_sigmaTwo]
  decide

theorem relIndex_P : P.relIndex (centralizer ({sigmaTwo} : Set (Perm (Fin 10)))) = 45 := by
  have h := relIndex_mul_card P (centralizer ({sigmaTwo} : Set (Perm (Fin 10))))
  rw [inf_eq_left.mpr P_le_centralizer, card_P, card_centralizer_sigmaTwo] at h
  omega

end CFSG.ComponentClassification.GSThmB.P29.A10
