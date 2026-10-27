module

public import CFSG.LieType.Chevalley.E7Three.CoordinateActions

public section

set_option autoImplicit false

namespace CFSG.LieType.Chevalley.E7Three.TriangularActions

open CFSG.LieType.Chevalley.E7Three.CoordinateActions

abbrev P := ZMod 3 × ZMod 3 × ZMod 3

@[expose] def x : MulAut D := u ^ 2
@[expose] def z : MulAut D := v * u * v⁻¹
@[expose] def y : MulAut D := w * z * w⁻¹

@[expose] def tri (p : P) : MulAut D :=
  x ^ p.1.val * z ^ p.2.1.val * y ^ p.2.2.val

@[expose] def mulParam (p q : P) : P :=
  (p.1 + q.1, p.2.1 + q.2.1 - q.1 * p.2.2, p.2.2 + q.2.2)

@[expose] def invParam (p : P) : P :=
  (-p.1, -p.2.1 - p.1 * p.2.2, -p.2.2)

theorem tri_mul : ∀ p q : P, tri p * tri q = tri (mulParam p q) := by decide +kernel
theorem tri_inv : ∀ p : P, (tri p)⁻¹ = tri (invParam p) := by decide +kernel
theorem tri_injective : Function.Injective tri := by decide +kernel

@[expose] def triGroup : Subgroup (MulAut D) where
  carrier := Set.range tri
  one_mem' := ⟨(0, 0, 0), by simp [tri]⟩
  mul_mem' := by
    rintro a b ⟨p, rfl⟩ ⟨q, rfl⟩
    exact ⟨mulParam p q, (tri_mul p q).symm⟩
  inv_mem' := by
    rintro a ⟨p, rfl⟩
    exact ⟨invParam p, (tri_inv p).symm⟩

theorem card_triGroup : Nat.card triGroup = 27 := by
  let e : P ≃ triGroup := Equiv.ofInjective tri tri_injective
  rw [← Nat.card_congr e]
  simp only [Nat.card_prod, Nat.card_zmod]

theorem triGroup_le_of_u_v_w {S : Subgroup (MulAut D)}
    (hu : u ∈ S) (hv : v ∈ S) (hw : w ∈ S) : triGroup ≤ S := by
  have hx : x ∈ S := S.pow_mem hu 2
  have hz : z ∈ S := S.mul_mem (S.mul_mem hv hu) (S.inv_mem hv)
  have hy : y ∈ S := S.mul_mem (S.mul_mem hw hz) (S.inv_mem hw)
  rintro a ⟨p, rfl⟩
  exact S.mul_mem (S.mul_mem (S.pow_mem hx _) (S.pow_mem hz _)) (S.pow_mem hy _)

theorem twentySeven_dvd_card_of_u_v_w {S : Subgroup (MulAut D)}
    (hu : u ∈ S) (hv : v ∈ S) (hw : w ∈ S) : 27 ∣ Nat.card S := by
  have h := Subgroup.card_dvd_of_le (triGroup_le_of_u_v_w hu hv hw)
  simpa only [card_triGroup] using h

theorem threeFiveOne_dvd_card_of_u_v_w {S : Subgroup (MulAut D)}
    (hu : u ∈ S) (hv : v ∈ S) (hw : w ∈ S) : 351 ∣ Nat.card S := by
  exact (show Nat.Coprime 27 13 by decide +kernel).mul_dvd_of_dvd_of_dvd
    (twentySeven_dvd_card_of_u_v_w hu hv hw) (thirteen_dvd_card_of_u_v_w hu hv hw)

end CFSG.LieType.Chevalley.E7Three.TriangularActions
