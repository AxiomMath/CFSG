module

public import CFSG.GroupTheory.QuasiDihedralFusion.Structure
public import CFSG.LocalAnalysis.ComponentClassification.ClassicalModelStatedBridge

public noncomputable section

namespace CFSG.ComponentClassification.HarrisLit

open CFSG Subgroup CFSG.Open CFSG.Semidihedral

theorem index_two_subgroup_semidihedral_cases {n : ℕ} (hn : 4 ≤ n)
    {H : Subgroup (SemidihedralGroup n)} (hH : H.index = 2) :
    IsCyclic ↥H ∨ Nonempty (↥H ≃* DihedralGroup (2 ^ (n - 2))) ∨
      Nonempty (↥H ≃* QuaternionGroup (2 ^ (n - 3))) := by
  rcases (index_eq_two_iff n (by omega) H).mp hH with rfl | rfl | rfl
  · exact .inl (rotationSubgroup_cyclic n)
  · exact .inr (.inl ⟨(dihedralEquiv n hn).symm⟩)
  · exact .inr (.inr ⟨(quaternionEquiv n hn).symm⟩)

theorem quaternionSubgroup_map_mulAut {n : ℕ} (hn : 4 ≤ n) (φ : MulAut (SemidihedralGroup n)) :
    (quaternionSubgroup n).map φ.toMonoidHom = quaternionSubgroup n := by
  have h2 : 2 ≤ 2 ^ (n - 3) := by
    calc 2 = 2 ^ 1 := by norm_num
      _ ≤ 2 ^ (n - 3) := Nat.pow_le_pow_right (by norm_num) (by omega)
  have hidx : ((quaternionSubgroup n).map φ.toMonoidHom).index = 2 := by
    rw [MulEquiv.toMonoidHom_eq_coe, Subgroup.index_map_equiv]
    exact (index_eq_two_iff n (by omega) _).mpr (.inr (.inr rfl))
  let eq : QuaternionGroup (2 ^ (n - 3)) ≃* ↥((quaternionSubgroup n).map φ.toMonoidHom) :=
    (quaternionEquiv n hn).trans
      ((quaternionSubgroup n).equivMapOfInjective φ.toMonoidHom φ.injective)
  rcases (index_eq_two_iff n (by omega) _).mp hidx with h | h | h
  ·
    exfalso
    have hcyc : IsCyclic ↥((quaternionSubgroup n).map φ.toMonoidHom) := by
      rw [h]
      exact rotationSubgroup_cyclic n
    have hcomm : ∀ x y : ↥((quaternionSubgroup n).map φ.toMonoidHom), x * y = y * x :=
      fun x y => (IsCyclic.isMulCommutative (α := ↥((quaternionSubgroup n).map
        φ.toMonoidHom))).is_comm.comm x y
    apply QuasiDihedralFusion.quaternionGroup_not_isMulCommutative h2
    exact ⟨⟨fun a b => eq.injective (by rw [map_mul, map_mul]; exact hcomm _ _)⟩⟩
  ·
    exfalso
    let ed : ↥((quaternionSubgroup n).map φ.toMonoidHom) ≃* DihedralGroup (half n) :=
      (MulEquiv.subgroupCongr h).trans (dihedralEquiv n hn).symm
    exact QuasiDihedralFusion.not_injective_quaternion_dihedral h2 (ed.toMonoidHom.comp
      eq.toMonoidHom) (ed.injective.comp eq.injective)
  · exact h

theorem exists_normal_quaternion_of_semidihedral {G : Type*} [Group G] {P : Subgroup G} [P.Normal]
    {n : ℕ} (hn : 4 ≤ n) (e : ↥P ≃* SemidihedralGroup n) :
    ∃ N : Subgroup G, N.Normal ∧ Nonempty (↥N ≃* QuaternionGroup (2 ^ (n - 3))) := by
  refine ⟨((quaternionSubgroup n).map e.symm.toMonoidHom).map P.subtype, ⟨fun x hx g => ?_⟩,
    ⟨(((quaternionSubgroup n).map e.symm.toMonoidHom).equivMapOfInjective _
      P.subtype_injective).symm.trans
      ((((quaternionSubgroup n).equivMapOfInjective _ e.symm.injective).symm).trans
        (quaternionEquiv n hn).symm)⟩⟩
  obtain ⟨_, ⟨q, hq, rfl⟩, rfl⟩ := hx
  set φ : MulAut (SemidihedralGroup n) := e.symm.trans ((MulAut.conjNormal g).trans e) with hφ
  have hφq : φ q ∈ quaternionSubgroup n := by
    rw [← quaternionSubgroup_map_mulAut hn φ]
    exact ⟨q, hq, rfl⟩
  refine ⟨e.symm (φ q), ⟨φ q, hφq, rfl⟩, ?_⟩
  rw [hφ, MulEquiv.trans_apply, MulEquiv.trans_apply, MulEquiv.symm_apply_apply,
    Subgroup.coe_subtype, MulAut.conjNormal_apply]
  rfl

end CFSG.ComponentClassification.HarrisLit
