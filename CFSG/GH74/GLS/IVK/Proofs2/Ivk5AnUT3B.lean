module

public import CFSG.Foundations.Basic
public import CFSG.GH74.GLS.Bg.TwoGroups.L23Models

public section

namespace CFSG.GH74.GLS.IVK.Proofs2.Ivk5An

open CFSG.GH74.GLS.Bg.TwoGroups CFSG.GH74.GLS.Bg.TwoGroups.L23 CFSG
open scoped commutatorElement

namespace UT3Aux

theorem mem_zpowers_iff_of_sq_eq_one {G : Type*} [Group G] {g : G} (h : g * g = 1) {x : G} :
    x ∈ Subgroup.zpowers g ↔ x = 1 ∨ x = g := by
  constructor
  · intro hx
    obtain ⟨k, hk'⟩ := Subgroup.mem_zpowers_iff.mp hx
    rw [← hk']
    have h2 : g ^ (2 : ℤ) = 1 := by rw [zpow_two]; exact h
    have hk : k = 2 * (k / 2) + k % 2 := (Int.mul_ediv_add_emod k 2).symm
    rcases Int.emod_two_eq_zero_or_one k with h0 | h1
    · left
      rw [hk, h0, add_zero, zpow_mul, h2, one_zpow]
    · right
      rw [hk, h1, zpow_add, zpow_mul, h2, one_zpow, one_mul, zpow_one]
  · rintro (rfl | rfl)
    · exact one_mem _
    · exact Subgroup.mem_zpowers _

@[expose] def omegaCoeff (x y : F4c) : ZMod 2 := (x * y).b

theorem omegaCoeff_add_left (x x' y : F4c) :
    omegaCoeff (x + x') y = omegaCoeff x y + omegaCoeff x' y := by
  revert x x' y; decide

theorem omegaCoeff_add_right (x y y' : F4c) :
    omegaCoeff x (y + y') = omegaCoeff x y + omegaCoeff x y' := by
  revert x y y'; decide

theorem omegaCoeff_zero_left (y : F4c) : omegaCoeff 0 y = 0 := by revert y; decide

theorem omegaCoeff_zero_right (x : F4c) : omegaCoeff x 0 = 0 := by revert x; decide

theorem F4c_add_self (x : F4c) : x + x = 0 := by revert x; decide

theorem zmod2_add_self (u : ZMod 2) : u + u = 0 := by revert u; decide

@[ext] structure Ext32 where
  a : F4c
  b : F4c
  s : ZMod 2

namespace Ext32

instance : DecidableEq Ext32 := fun x y =>
  decidable_of_iff (x.a = y.a ∧ x.b = y.b ∧ x.s = y.s) (by cases x; cases y; simp)

instance : Fintype Ext32 :=
  Fintype.ofEquiv (F4c × F4c × ZMod 2)
    { toFun := fun t => ⟨t.1, t.2.1, t.2.2⟩
      invFun := fun x => (x.a, x.b, x.s)
      left_inv := fun t => rfl
      right_inv := fun x => by cases x; rfl }

instance : Mul Ext32 := ⟨fun x y => ⟨x.a + y.a, x.b + y.b, x.s + y.s + omegaCoeff x.a y.b⟩⟩

instance : One Ext32 := ⟨⟨0, 0, 0⟩⟩

instance : Inv Ext32 := ⟨fun x => ⟨x.a, x.b, x.s + omegaCoeff x.a x.b⟩⟩

theorem mul_def (x y : Ext32) :
    x * y = ⟨x.a + y.a, x.b + y.b, x.s + y.s + omegaCoeff x.a y.b⟩ := rfl

theorem one_def : (1 : Ext32) = ⟨0, 0, 0⟩ := rfl

theorem inv_def (x : Ext32) : x⁻¹ = ⟨x.a, x.b, x.s + omegaCoeff x.a x.b⟩ := rfl

instance : Group Ext32 where
  mul_assoc x y z := by
    refine Ext32.ext ?_ ?_ ?_
    · simp only [mul_def]; exact add_assoc _ _ _
    · simp only [mul_def]; exact add_assoc _ _ _
    · simp only [mul_def, omegaCoeff_add_left, omegaCoeff_add_right]; ring
  one_mul x := by
    refine Ext32.ext ?_ ?_ ?_
    · simp only [mul_def, one_def]; exact zero_add _
    · simp only [mul_def, one_def]; exact zero_add _
    · simp only [mul_def, one_def, omegaCoeff_zero_left]; ring
  mul_one x := by
    refine Ext32.ext ?_ ?_ ?_
    · simp only [mul_def, one_def]; exact add_zero _
    · simp only [mul_def, one_def]; exact add_zero _
    · simp only [mul_def, one_def, omegaCoeff_zero_right]; ring
  inv_mul_cancel x := by
    refine Ext32.ext ?_ ?_ ?_
    · simp only [mul_def, one_def, inv_def]; exact F4c_add_self _
    · simp only [mul_def, one_def, inv_def]; exact F4c_add_self _
    · simp only [mul_def, one_def, inv_def]
      calc x.s + omegaCoeff x.a x.b + x.s + omegaCoeff x.a x.b
          = (x.s + x.s) + (omegaCoeff x.a x.b + omegaCoeff x.a x.b) := by ring
        _ = 0 := by rw [zmod2_add_self, zmod2_add_self, add_zero]

@[expose] def z : Ext32 := ⟨0, 0, 1⟩

theorem mul_self_z : z * z = 1 := by decide

theorem z_ne_one : z ≠ 1 := by decide

theorem mem_zpowers_z_iff (x : Ext32) : x ∈ Subgroup.zpowers z ↔ x.a = 0 ∧ x.b = 0 := by
  rw [mem_zpowers_iff_of_sq_eq_one mul_self_z]
  revert x
  decide

theorem mem_center_iff (x : Ext32) : x ∈ Subgroup.center Ext32 ↔ x.a = 0 ∧ x.b = 0 := by
  rw [Subgroup.mem_center_iff]
  revert x
  decide

theorem center_eq : Subgroup.center Ext32 = Subgroup.zpowers z := by
  ext x
  rw [mem_center_iff, mem_zpowers_z_iff]

theorem commutator_eq : _root_.commutator Ext32 = Subgroup.zpowers z := by
  apply le_antisymm
  · rw [_root_.commutator_def, Subgroup.commutator_le]
    intro g hg h hh
    clear hg hh
    rw [mem_zpowers_z_iff]
    revert g h
    decide
  · rw [Subgroup.zpowers_le, _root_.commutator_def]
    have h : ⁅(⟨⟨0, 1⟩, 0, 0⟩ : Ext32), ⟨0, ⟨1, 0⟩, 0⟩⁆ = z := by decide
    rw [← h]
    exact Subgroup.commutator_mem_commutator (Subgroup.mem_top _) (Subgroup.mem_top _)

theorem card_eq : Nat.card Ext32 = 2 ^ 5 := by
  rw [Nat.card_eq_fintype_card]; decide

theorem orderOf_z : orderOf z = 2 := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  exact orderOf_eq_prime (by rw [sq]; exact mul_self_z) z_ne_one

theorem card_center : Nat.card (Subgroup.center Ext32) = 2 := by
  rw [center_eq, Nat.card_zpowers, orderOf_z]

theorem frattini_eq : frattini Ext32 = Subgroup.zpowers z := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have : Fact (IsPGroup 2 Ext32) := ⟨IsPGroup.of_card card_eq⟩
  rw [frattini_eq_closure_commutator_union_powers (p := 2) (R := Ext32), commutator_eq]
  apply le_antisymm
  · rw [Subgroup.closure_le]
    rintro x (hx | ⟨y, rfl⟩)
    · exact hx
    · show y ^ 2 ∈ Subgroup.zpowers z
      rw [mem_zpowers_z_iff, sq]
      revert y
      decide
  · exact fun x hx => Subgroup.subset_closure (Or.inl hx)

theorem isExtraspecialPGroup : IsExtraspecialPGroup 2 Ext32 :=
  ⟨IsPGroup.of_card card_eq, commutator_eq.trans center_eq.symm, frattini_eq.trans center_eq.symm,
    card_center⟩

end Ext32

@[expose] def proj : UT3 F4c →* Ext32 :=
  MonoidHom.mk' (fun x => ⟨x.a, x.b, x.c.b⟩) (fun _ _ => rfl)

theorem proj_apply (x : UT3 F4c) : proj x = ⟨x.a, x.b, x.c.b⟩ := rfl

theorem proj_surjective : Function.Surjective proj := fun y => ⟨⟨y.a, y.b, ⟨0, y.s⟩⟩, rfl⟩

theorem ker_proj : proj.ker = Subgroup.zpowers (⟨0, 0, 1⟩ : UT3 F4c) := by
  ext x
  rw [MonoidHom.mem_ker, mem_zpowers_iff_of_sq_eq_one
    (by decide : (⟨0, 0, 1⟩ : UT3 F4c) * ⟨0, 0, 1⟩ = 1)]
  revert x
  decide

end UT3Aux

theorem exists_extraspecial_quot :
    ∃ (P : Type) (_ : Group P) (φ : UT3 F4c →* P), Function.Surjective φ ∧
      φ.ker = Subgroup.zpowers (⟨0, 0, 1⟩ : UT3 F4c) ∧ IsExtraspecialPGroup 2 P :=
  ⟨UT3Aux.Ext32, inferInstance, UT3Aux.proj, UT3Aux.proj_surjective, UT3Aux.ker_proj,
    UT3Aux.Ext32.isExtraspecialPGroup⟩

theorem exists_extraspecial_quot_of_equiv {G : Type} [Group G] (e : G ≃* UT3 F4c) {t : G}
    (ht : e t = ⟨0, 0, 1⟩) :
    ∃ (P : Type) (_ : Group P) (φ : G →* P), Function.Surjective φ ∧
      φ.ker = Subgroup.zpowers t ∧ IsExtraspecialPGroup 2 P := by
  obtain ⟨P, _, φ, hsurj, hker, hext⟩ := exists_extraspecial_quot
  refine ⟨P, _, φ.comp e.toMonoidHom, hsurj.comp e.surjective, ?_, hext⟩
  have h1 : Subgroup.zpowers (e t) = (Subgroup.zpowers t).map e.toMonoidHom :=
    (MonoidHom.map_zpowers e.toMonoidHom t).symm
  rw [← MonoidHom.comap_ker, hker, ← ht, h1]
  exact Subgroup.comap_map_eq_self_of_injective e.injective _

end CFSG.GH74.GLS.IVK.Proofs2.Ivk5An
