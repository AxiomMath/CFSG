module

public import CFSG.GH74.GLS.IVK.Defs

public section

namespace CFSG.GH74.GLS.SP.Local

open DihedralGroup

private def dihRot (k : ℕ) : Subgroup (DihedralGroup k) where
  carrier := {g | ∃ i, g = r i}
  mul_mem' := by
    rintro _ _ ⟨i, rfl⟩ ⟨j, rfl⟩
    exact ⟨i + j, rfl⟩
  one_mem' := ⟨0, rfl⟩
  inv_mem' := by
    rintro _ ⟨i, rfl⟩
    exact ⟨-i, rfl⟩

theorem dihedral_inv_of_gen {Q : Type} [Group Q] (k : ℕ) (hk : 3 ≤ k) (φ : Q ≃* DihedralGroup k)
    (x z : Q) (hx : orderOf x = k) (hz : orderOf z = 2)
    (hgen : Subgroup.zpowers x ⊔ Subgroup.zpowers z = ⊤) :
    z * x * z⁻¹ = x⁻¹ := by
  have hzi : z⁻¹ = z := by
    have hzz : z * z = 1 := by
      rw [← sq]
      exact hz ▸ pow_orderOf_eq_one z
    exact inv_eq_of_mul_eq_one_right hzz
  have hφx : ∃ i, φ x = r i := by
    have hord : orderOf (φ x) = k := by rw [MulEquiv.orderOf_eq]; exact hx
    cases h : φ x with
    | r i => exact ⟨i, rfl⟩
    | sr i =>
      rw [h, orderOf_sr] at hord
      omega
  obtain ⟨i, hi⟩ := hφx
  have hφz : ∃ j, φ z = sr j := by
    cases h : φ z with
    | sr j => exact ⟨j, rfl⟩
    | r j =>
      exfalso
      have hle : Subgroup.zpowers x ⊔ Subgroup.zpowers z ≤ (dihRot k).comap φ.toMonoidHom := by
        refine sup_le ?_ ?_
        · rw [Subgroup.zpowers_le]
          exact ⟨i, hi⟩
        · rw [Subgroup.zpowers_le]
          exact ⟨j, h⟩
      rw [hgen] at hle
      obtain ⟨l, hl⟩ := hle (Subgroup.mem_top (φ.symm (sr 0)))
      simp at hl
  obtain ⟨j, hj⟩ := hφz
  apply φ.injective
  rw [hzi, map_mul, map_mul, map_inv, hi, hj]
  simp only [sr_mul_r, sr_mul_sr, inv_r]
  congr 1
  ring

theorem inv_of_isDihedralOrder {G : Type} [Group G] (x z : G) (n : ℕ) (hn : 3 ≤ n)
    (hdih : IVK.IsDihedralOrder ↥(Subgroup.zpowers x ⊔ Subgroup.zpowers z) (2 ^ n))
    (hx : orderOf x = 2 ^ (n - 1)) (hz : orderOf z = 2) :
    z * x * z⁻¹ = x⁻¹ := by
  obtain ⟨k, hk2n, -, ⟨ψ⟩⟩ := hdih
  have hkn : k = 2 ^ (n - 1) := by
    have h2 : 2 ^ n = 2 * 2 ^ (n - 1) := by
      rw [← pow_succ']
      congr 1
      omega
    omega
  have hk3 : 3 ≤ k := by
    rw [hkn]
    calc 3 ≤ 2 ^ 2 := by norm_num
      _ ≤ 2 ^ (n - 1) := Nat.pow_le_pow_right (by norm_num) (by omega)
  set S : Subgroup G := Subgroup.zpowers x ⊔ Subgroup.zpowers z
  let x' : S := ⟨x, Subgroup.mem_sup_left (Subgroup.mem_zpowers x)⟩
  let z' : S := ⟨z, Subgroup.mem_sup_right (Subgroup.mem_zpowers z)⟩
  have hx' : orderOf x' = k := by
    rw [hkn, ← hx]
    exact Subgroup.orderOf_mk x _
  have hz' : orderOf z' = 2 := by
    rw [← hz]
    exact Subgroup.orderOf_mk z _
  have hgen : Subgroup.zpowers x' ⊔ Subgroup.zpowers z' = ⊤ := by
    apply Subgroup.map_injective (Subgroup.subtype_injective S)
    rw [Subgroup.map_sup, MonoidHom.map_zpowers, MonoidHom.map_zpowers, Subgroup.map_top,
      Subgroup.range_subtype]
    rfl
  have h := dihedral_inv_of_gen k hk3 ψ x' z' hx' hz' hgen
  exact congrArg Subtype.val h

end CFSG.GH74.GLS.SP.Local
