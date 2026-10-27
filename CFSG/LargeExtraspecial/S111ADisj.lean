module

public import CFSG.LargeExtraspecial.S111AStar

public section

attribute [-instance] instAddCommGroupOfIsSimpleAddGroupOfIsNilpotent
  instCommGroupOfIsSimpleGroupOfIsNilpotent

namespace CFSG.LargeExtraspecial.S11

open Subgroup Module CFSG.LargeExtraspecial.S4

variable {G : Type*} [Group G] [Finite G] {S : Setting G} {g : G} {A : Subgroup G}

omit [Finite G] in
theorem IncClosed.clPre_clSub (hA : IncClosed S A) : S.clPre (S.clSub A) = A :=
  S.clPre_clSub hA.le_QG hA.z_mem

omit [Finite G] in
theorem IncClosed.card_eq (hA : IncClosed S A) : Nat.card A = 2 * Nat.card (S.clSub A) := by
  conv_lhs => rw [← hA.clPre_clSub]
  exact S.card_clPre _

theorem Cfg111.Lbar_inf_eq_bot (C : Cfg111 S g A) {h k j : G} (hh : h ∈ S.M)
    (hA : A ⊓ A.map (MulAut.conj h).toMonoidHom = zpowers S.z) (hk : k * S.z * k⁻¹ ∈ A)
    (hkz : k * S.z * k⁻¹ ≠ S.z) (hj : j * S.z * j⁻¹ ∈ A.map (MulAut.conj h).toMonoidHom)
    (hjz : j * S.z * j⁻¹ ≠ S.z) : S.Lbar k ⊓ S.Lbar j = ⊥ := by
  by_contra hne
  have hjA := C.mem_of_Lbar_inf_ne_bot hk hkz ((C.inc.map_conj hh).le_QG hj) hjz hne
  have hmem : j * S.z * j⁻¹ ∈ A ⊓ A.map (MulAut.conj h).toMonoidHom := ⟨hjA, hj⟩
  rw [hA, Setting.mem_zpowers_iff_of_mul_self S.z_mul_z] at hmem
  rcases hmem with e | e
  · exact conj_z_ne_one S j e
  · exact hjz e

theorem Cfg111.inf_Qa_le (C : Cfg111 S g A) {h k : G} (hh : h ∈ S.M)
    (hA : A ⊓ A.map (MulAut.conj h).toMonoidHom = zpowers S.z) (hk : k * S.z * k⁻¹ ∈ A)
    (hkz : k * S.z * k⁻¹ ≠ S.z) : A.map (MulAut.conj h).toMonoidHom ⊓ S.Qa k ≤ zpowers S.z := by
  rintro x ⟨hxh, hxk⟩
  rw [← hA]
  refine ⟨?_, hxh⟩
  by_cases hx1 : x = 1
  · rw [hx1]
    exact one_mem _
  obtain ⟨j, rfl⟩ := (C.inc.map_conj hh).conj x hxh hx1
  exact C.star hk hkz ((C.inc.map_conj hh).le_QG hxh) hxk

omit [Finite G] in
theorem inf_map_conj_symm {h : G} (hA : A ⊓ A.map (MulAut.conj h).toMonoidHom = zpowers S.z) :
    A.map (MulAut.conj h).toMonoidHom ⊓
      (A.map (MulAut.conj h).toMonoidHom).map (MulAut.conj h⁻¹).toMonoidHom = zpowers S.z := by
  rw [map_conj_inv_map_conj, inf_comm, hA]

theorem Cfg111.inf_Qa_le_of_mem_map (C : Cfg111 S g A) {h j : G} (hh : h ∈ S.M)
    (hA : A ⊓ A.map (MulAut.conj h).toMonoidHom = zpowers S.z)
    (hj : j * S.z * j⁻¹ ∈ A.map (MulAut.conj h).toMonoidHom) (hjz : j * S.z * j⁻¹ ≠ S.z) :
    A ⊓ S.Qa j ≤ zpowers S.z := by
  have := (C.conj hh).inf_Qa_le (S.M.inv_mem hh) (inf_map_conj_symm hA) hj hjz
  rwa [map_conj_inv_map_conj] at this

end CFSG.LargeExtraspecial.S11
