module

public import CFSG.LargeExtraspecial.S10Dec

public section

attribute [-instance] instAddCommGroupOfIsSimpleAddGroupOfIsNilpotent
  instCommGroupOfIsSimpleGroupOfIsNilpotent

namespace CFSG.LargeExtraspecial.S10

open Subgroup Module QuadraticMap CFSG.RankThree.OrthogonalInvolutions
open CFSG.LargeExtraspecial.S4 CFSG.LargeExtraspecial.S6

universe u

theorem perm_three_comm_cube : ∀ a b : Equiv.Perm (Fin 3), (a * b * a⁻¹ * b⁻¹) ^ 3 = 1 := by
  decide +kernel

theorem perm_three_mul_cube : ∀ a b : Equiv.Perm (Fin 3), a ^ 3 = 1 → b ^ 3 = 1 →
    (a * b) ^ 3 = 1 := by
  decide +kernel

theorem perm_three_cube_comm : ∀ σ : Equiv.Perm (Fin 3), σ ^ 3 = 1 →
    ∃ a b : Equiv.Perm (Fin 3), σ = a * b * a⁻¹ * b⁻¹ := by
  decide +kernel

theorem perm_three_card_cube :
    (Finset.univ.filter fun σ : Equiv.Perm (Fin 3) => σ ^ 3 = 1).card = 3 := by
  decide +kernel

variable {G : Type u} [Group G] [Finite G] {S : Setting G} {g : G} {t : S.O}

namespace DirDec

variable {Xb Yb : Subgroup S.O} (D : DirDec S g t Xb Yb)
include D

@[expose] noncomputable def cubeSub : Subgroup S.O where
  carrier := {y | y ∈ Yb ∧ y ^ 3 = 1}
  mul_mem' := by
    rintro a b ⟨ha, ha3⟩ ⟨hb, hb3⟩
    refine ⟨mul_mem ha hb, ?_⟩
    obtain ⟨e⟩ := D.iso
    have h1 : e ⟨a, ha⟩ ^ 3 = 1 := by rw [← map_pow]; rw [show (⟨a, ha⟩ : Yb) ^ 3 = 1 from
      Subtype.ext ha3, map_one]
    have h2 : e ⟨b, hb⟩ ^ 3 = 1 := by rw [← map_pow]; rw [show (⟨b, hb⟩ : Yb) ^ 3 = 1 from
      Subtype.ext hb3, map_one]
    have h3 := perm_three_mul_cube _ _ h1 h2
    rw [← map_mul, ← map_pow] at h3
    have := e.injective (h3.trans (map_one e).symm)
    exact congrArg Subtype.val this
  one_mem' := ⟨one_mem _, one_pow 3⟩
  inv_mem' := by
    rintro a ⟨ha, ha3⟩
    exact ⟨inv_mem ha, by rw [inv_pow, ha3, inv_one]⟩

theorem commutator_eq : ⁅Yb, Yb⁆ = D.cubeSub := by
  obtain ⟨e⟩ := D.iso
  apply le_antisymm
  · rw [commutator_le]
    intro a ha b hb
    refine ⟨?_, ?_⟩
    · rw [commutatorElement_def]
      exact mul_mem (mul_mem (mul_mem ha hb) (inv_mem ha)) (inv_mem hb)
    · have h1 := perm_three_comm_cube (e ⟨a, ha⟩) (e ⟨b, hb⟩)
      rw [← map_inv, ← map_inv, ← map_mul, ← map_mul, ← map_mul, ← map_pow] at h1
      have := e.injective (h1.trans (map_one e).symm)
      have h2 := congrArg Subtype.val this
      simpa [commutatorElement_def] using h2
  · rintro y ⟨hy, hy3⟩
    have he3 : e ⟨y, hy⟩ ^ 3 = 1 := by
      rw [← map_pow, show (⟨y, hy⟩ : Yb) ^ 3 = 1 from Subtype.ext hy3, map_one]
    obtain ⟨a, b, hab⟩ := perm_three_cube_comm _ he3
    have hy' : (⟨y, hy⟩ : Yb) = e.symm a * e.symm b * (e.symm a)⁻¹ * (e.symm b)⁻¹ :=
      e.injective (by simp [hab])
    have := congrArg Subtype.val hy'
    simp only [Subgroup.coe_mul, Subgroup.coe_inv] at this
    rw [this]
    exact Subgroup.commutator_mem_commutator (e.symm a).2 (e.symm b).2

theorem mem_commutator_iff {y : S.O} : y ∈ ⁅Yb, Yb⁆ ↔ y ∈ Yb ∧ y ^ 3 = 1 := by
  rw [D.commutator_eq]
  rfl

theorem card_commutator : Nat.card (⁅Yb, Yb⁆ : Subgroup S.O) = 3 := by
  obtain ⟨e⟩ := D.iso
  rw [← perm_three_card_cube]
  have h : ↥(⁅Yb, Yb⁆ : Subgroup S.O) ≃
      ↥(Finset.univ.filter fun σ : Equiv.Perm (Fin 3) => σ ^ 3 = 1) :=
    { toFun := fun y => ⟨e ⟨y, ((D.mem_commutator_iff).mp y.2).1⟩, by
        simp only [Finset.mem_filter, Finset.mem_univ, true_and]
        rw [← map_pow, show (⟨(y : S.O), ((D.mem_commutator_iff).mp y.2).1⟩ : Yb) ^ 3 = 1 from
          Subtype.ext ((D.mem_commutator_iff).mp y.2).2, map_one]⟩
      invFun := fun σ => ⟨(e.symm σ : S.O), (D.mem_commutator_iff).mpr ⟨(e.symm σ).2, by
        have hσ := (Finset.mem_filter.mp σ.2).2
        have : (e.symm σ) ^ 3 = 1 := by rw [← map_pow, hσ, map_one]
        exact congrArg Subtype.val this⟩⟩
      left_inv := fun y => by simp
      right_inv := fun σ => by simp }
  rw [Nat.card_congr h, Nat.card_eq_fintype_card, Fintype.card_coe]

theorem commutator_ne_bot : (⁅Yb, Yb⁆ : Subgroup S.O) ≠ ⊥ := by
  intro h
  have := D.card_commutator
  rw [h, card_bot] at this
  exact absurd this (by norm_num)

theorem conj_mem_commutator {r : S.O} (hr : r ∈ Rbar S g t) {y : S.O} (hy : y ∈ ⁅Yb, Yb⁆) :
    r * y * r⁻¹ ∈ ⁅Yb, Yb⁆ := by
  rw [D.mem_commutator_iff] at hy ⊢
  refine ⟨D.conj_mem_Yb hr hy.1, ?_⟩
  rw [conj_pow, hy.2, mul_one, mul_inv_cancel]

end DirDec

theorem timmesfeld_10_3_alpha (hCE : CentralExtInput.{u}) (X : Hyp10 S g t) {Xb Yb : Subgroup S.O}
    (D : DirDec S g t Xb Yb) {v : S.Qt}
    (hv : ∀ y ∈ ⁅Yb, Yb⁆, (y : S.Qt ≃ₗ[ZMod 2] S.Qt) v = v) : v = 0 := by
  set C := fixSub S ⁅Yb, Yb⁆ with hC
  have hvC : v ∈ C := fun y hy => hv y hy
  by_contra hv0
  have hCne : C ≠ ⊥ := fun h => hv0 ((Submodule.mem_bot (ZMod 2)).mp (h ▸ hvC))
  have hinv : ∀ x ∈ Rbar S g t, ∀ u ∈ C, (x : S.Qt ≃ₗ[ZMod 2] S.Qt) u ∈ C := by
    intro x hx u hu y hy
    have h1 := hu _ (D.conj_mem_commutator (inv_mem hx) hy)
    have e1 : ((x⁻¹ * y * x⁻¹⁻¹ : S.O) : S.Qt ≃ₗ[ZMod 2] S.Qt) u =
        ((x : S.Qt ≃ₗ[ZMod 2] S.Qt)).symm ((y : S.Qt ≃ₗ[ZMod 2] S.Qt)
          ((x : S.Qt ≃ₗ[ZMod 2] S.Qt) u)) := by
      rw [inv_inv, Subgroup.coe_mul, Subgroup.coe_mul, LinearEquiv.mul_apply,
        LinearEquiv.mul_apply]
      rfl
    rw [e1] at h1
    have := congrArg (x : S.Qt ≃ₗ[ZMod 2] S.Qt) h1
    rwa [LinearEquiv.apply_symm_apply] at this
  have hVC := Vt_le_of_invariant X.H hCne hinv
  apply D.commutator_ne_bot
  rw [eq_bot_iff]
  intro y hy
  have hyY := ((D.mem_commutator_iff).mp hy).1
  have hyN : y ∈ Nbar S g t := mem_Nbar.mpr ⟨D.le_Rbar_right hyY, fun u hu => hVC hu y hy⟩
  exact (Subgroup.mem_bot).mpr (D.eq_one_of_mem_Nbar hCE X hyY hyN)

end CFSG.LargeExtraspecial.S10
