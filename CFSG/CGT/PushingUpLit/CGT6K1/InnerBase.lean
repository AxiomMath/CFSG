module

public import CFSG.LocalAnalysis.EvenBN.GMSK.SL2Facts

public section

namespace CFSG.CGT.PushingUpLit.CGT6K1

open CFSG.LocalAnalysis.EvenBN.GMSK

theorem fixedRoot_simple {D : Type*} [Group D] {n : ℕ} (hn : 2 ≤ n) {K : Type*} [Field K]
    [Fintype K] (hK : Fintype.card K = 2 ^ n) {α : MulAut D} {S : Subgroup D}
    (hSα : S ≤ α.toMonoidHom.eqLocus (MonoidHom.id D))
    (hSK : Nonempty (S ≃* Matrix.SpecialLinearGroup (Fin 2) K)) :
    IsSimpleGroup (S.subgroupOf (α.toMonoidHom.eqLocus (MonoidHom.id D))) ∧
      (∃ a b : S.subgroupOf (α.toMonoidHom.eqLocus (MonoidHom.id D)), a * b ≠ b * a) ∧
      Nonempty (S.subgroupOf (α.toMonoidHom.eqLocus (MonoidHom.id D)) ≃*
        Matrix.SpecialLinearGroup (Fin 2) K) := by
  obtain ⟨φ⟩ := hSK
  let e := (Subgroup.subgroupOfEquivOfLe hSα).trans φ
  have h4 : 4 ≤ Fintype.card K := by
    rw [hK]
    calc 4 = 2 ^ 2 := by norm_num
      _ ≤ 2 ^ n := Nat.pow_le_pow_right (by norm_num) hn
  have := sl2_isSimpleGroup (two_eq_zero_of_card (by omega) hK) h4
  obtain ⟨a, b, hab⟩ := sl2_exists_mul_ne (K := K)
  exact ⟨e.isSimpleGroup, ⟨e.symm a, e.symm b, fun h => hab (e.symm.injective (by
    rw [map_mul, map_mul, h]))⟩, ⟨e⟩⟩

end CFSG.CGT.PushingUpLit.CGT6K1
