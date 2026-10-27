module

public import CFSG.GH74.Filter.Witness

public section

namespace CFSG.GH74.Filter.Lie

@[expose] def q8Frattini : QuaternionGroup 2 →* Multiplicative (ZMod 2 × ZMod 2) where
  toFun g := match g with
    | .a i => Multiplicative.ofAdd (ZMod.castHom (by decide : 2 ∣ 4) (ZMod 2) i, 0)
    | .xa i => Multiplicative.ofAdd (ZMod.castHom (by decide : 2 ∣ 4) (ZMod 2) i, 1)
  map_one' := by decide
  map_mul' := by decide

theorem q8Frattini_surjective : Function.Surjective q8Frattini := by decide

theorem q8Frattini_center :
    ∀ g : QuaternionGroup 2, (∀ y, g * y = y * g) → q8Frattini g = 1 := by decide

theorem q8Frattini_comm : ∀ a b : Multiplicative (ZMod 2 × ZMod 2), a * b = b * a := by decide

theorem q8Frattini_sq : ∀ a : Multiplicative (ZMod 2 × ZMod 2), a ^ 2 = 1 := by decide

theorem q8Frattini_card : Nat.card (Multiplicative (ZMod 2 × ZMod 2)) = 4 := by
  simp [Nat.card_eq_fintype_card]

theorem commute_of_mul_eq_central {P : Type*} [Group P] {t u v c : P}
    (hc : c ∈ Subgroup.center P) (htv : Commute t v) (h : u * v = c) : Commute t u := by
  have hu : u = c * v⁻¹ := by rw [← h]; group
  have htc : Commute t c := Subgroup.mem_center_iff.1 hc t
  rw [hu]
  exact htc.mul_right htv.inv_right

theorem not_gen4_quotient_of_Q8_cube {P : Type*} [Group P] [Finite P] (N : Subgroup P) [N.Normal]
    (hN : N ≤ Subgroup.center P) (ψ : Fin 3 → QuaternionGroup 2 →* P)
    (hinj : ∀ i, Function.Injective (ψ i))
    (hcomm : ∀ i j, i ≠ j → ∀ x y, Commute (ψ i x) (ψ j y)) :
    ¬ Gen4 (P ⧸ N) := by
  have h01 := hcomm 0 1 (by decide)
  have h02 := hcomm 0 2 (by decide)
  have h12 := hcomm 1 2 (by decide)
  let α₂ : QuaternionGroup 2 × QuaternionGroup 2 →* P := (ψ 1).noncommCoprod (ψ 2) h12
  have hα₂ : ∀ yz, α₂ yz = ψ 1 yz.1 * ψ 2 yz.2 := fun yz => by
    simp [α₂, MonoidHom.noncommCoprod_apply]
  let α₁ : QuaternionGroup 2 × (QuaternionGroup 2 × QuaternionGroup 2) →* P :=
    (ψ 0).noncommCoprod α₂ (fun x yz => by
      rw [hα₂]
      exact (h01 x yz.1).mul_right (h02 x yz.2))
  have hα₁ : ∀ x yz, α₁ (x, yz) = ψ 0 x * (ψ 1 yz.1 * ψ 2 yz.2) := fun x yz => by
    simp [α₁, MonoidHom.noncommCoprod_apply, hα₂]
  let α : QuaternionGroup 2 × (QuaternionGroup 2 × QuaternionGroup 2) →* P ⧸ N :=
    (QuotientGroup.mk' N).comp α₁
  let β : QuaternionGroup 2 × (QuaternionGroup 2 × QuaternionGroup 2) →*
      Multiplicative (ZMod 2 × ZMod 2) × (Multiplicative (ZMod 2 × ZMod 2) ×
        Multiplicative (ZMod 2 × ZMod 2)) :=
    q8Frattini.prodMap (q8Frattini.prodMap q8Frattini)
  refine not_gen4_of_surjection α β ?_ ?_ ?_ ?_ ?_
  · exact Prod.map_surjective.2 ⟨q8Frattini_surjective, Prod.map_surjective.2
      ⟨q8Frattini_surjective, q8Frattini_surjective⟩⟩
  · exact fun a b => Prod.ext (q8Frattini_comm _ _) (Prod.ext (q8Frattini_comm _ _)
      (q8Frattini_comm _ _))
  · exact fun a => Prod.ext (q8Frattini_sq _) (Prod.ext (q8Frattini_sq _) (q8Frattini_sq _))
  · rw [Nat.card_prod, Nat.card_prod, q8Frattini_card]
    norm_num
  · rintro ⟨x, y, z⟩ hxyz
    have hc : ψ 0 x * (ψ 1 y * ψ 2 z) ∈ Subgroup.center P := by
      refine hN ?_
      have := (QuotientGroup.eq_one_iff _).1 (MonoidHom.mem_ker.1 hxyz)
      simpa [α, hα₁] using this
    have hx : q8Frattini x = 1 := by
      refine q8Frattini_center x fun t => hinj 0 ?_
      rw [map_mul, map_mul]
      exact (commute_of_mul_eq_central hc ((h01 t y).mul_right (h02 t z)) rfl).symm.eq
    have hy : q8Frattini y = 1 := by
      refine q8Frattini_center y fun t => hinj 1 ?_
      rw [map_mul, map_mul]
      refine (commute_of_mul_eq_central (t := ψ 1 t) (u := ψ 1 y) (v := ψ 0 x * ψ 2 z)
        (c := ψ 0 x * (ψ 1 y * ψ 2 z)) hc ((h01 x t).symm.mul_right (h12 t z)) ?_).symm.eq
      rw [← mul_assoc, ← (h01 x y).eq, mul_assoc]
    have hz : q8Frattini z = 1 := by
      refine q8Frattini_center z fun t => hinj 2 ?_
      rw [map_mul, map_mul]
      refine (commute_of_mul_eq_central (t := ψ 2 t) (u := ψ 2 z) (v := ψ 0 x * ψ 1 y)
        (c := ψ 0 x * (ψ 1 y * ψ 2 z)) hc ((h02 x t).symm.mul_right (h12 y t).symm) ?_).symm.eq
      rw [((h02 x z).symm.mul_right (h12 y z).symm).eq, mul_assoc]
    exact Prod.ext hx (Prod.ext hy hz)

end CFSG.GH74.Filter.Lie
