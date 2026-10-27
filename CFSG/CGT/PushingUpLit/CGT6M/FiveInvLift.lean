module

public import CFSG.CGT.PushingUpLit.CGT6M.FiveLift

public section

namespace CFSG.CGT.PushingUpLit.CGT6M

variable {L Q : Type*} [Group L] [Group Q]

theorem exists_inverted_c55_of_cover [Finite L] {ν : L →* Q} (hν : Function.Surjective ν)
    (hK : ν.ker ≤ Subgroup.center L) (hK5 : ¬ 5 ∣ Nat.card ν.ker) {Φbar : C55 →* Q}
    (hΦ : Function.Injective Φbar) {z : L} (hz2 : z * z = 1)
    (hz : ∀ u : C55, ν z * Φbar u * (ν z)⁻¹ = (Φbar u)⁻¹) :
    ∃ Φ : C55 →* L, Function.Injective Φ ∧ ∀ u : C55, z * Φ u * z⁻¹ = (Φ u)⁻¹ := by
  have hP5 : IsPGroup 5 Φbar.range :=
    isPGroup_c55.of_surjective Φbar.rangeRestrict Φbar.rangeRestrict_surjective
  obtain ⟨P, hinj, hmap, hnorm⟩ := exists_lift_five ν hν hK hK5 hP5
  have hex : ∀ u : C55, ∃ p ∈ P, ν p = Φbar u := fun u => by
    have h1 : Φbar u ∈ P.map ν := by
      rw [hmap]
      exact ⟨u, rfl⟩
    obtain ⟨p, hp, hpu⟩ := Subgroup.mem_map.mp h1
    exact ⟨p, hp, hpu⟩
  choose p hpP hpν using hex
  let Φ : C55 →* L := MonoidHom.mk' p (fun u v => by
    refine hinj _ (hpP _) _ (P.mul_mem (hpP u) (hpP v)) ?_
    rw [hpν, map_mul Φbar, map_mul ν, hpν, hpν])
  have hΦp : ∀ u, Φ u = p u := fun u => rfl
  have hzi : (ν z)⁻¹ = ν z := inv_eq_of_mul_eq_one_right (by rw [← map_mul, hz2, map_one])
  have hconj : ∀ w : C55, ν z * Φbar w * (ν z)⁻¹ = Φbar w⁻¹ := fun w => by
    rw [hz, map_inv]
  have hnz : ν z ∈ Subgroup.normalizer (Φbar.range : Set Q) := by
    rw [Subgroup.mem_normalizer_iff]
    intro h
    constructor
    · rintro ⟨w, rfl⟩
      exact ⟨w⁻¹, (hconj w).symm⟩
    · rintro ⟨w, hw⟩
      refine ⟨w⁻¹, ?_⟩
      calc Φbar w⁻¹ = ν z * Φbar w * (ν z)⁻¹ := (hconj w).symm
        _ = (ν z)⁻¹ * Φbar w * ν z := by rw [hzi]
        _ = (ν z)⁻¹ * (ν z * h * (ν z)⁻¹) * ν z := by rw [hw]
        _ = h := by group
  refine ⟨Φ, fun u v huv => hΦ ?_, fun u => ?_⟩
  · rw [← hpν u, ← hpν v]
    exact congrArg ν huv
  · show z * p u * z⁻¹ = (p u)⁻¹
    refine hinj _ (hnorm z hnz _ (hpP u)) _ ((P.inv_mem (hpP u))) ?_
    rw [map_mul, map_mul, map_inv, map_inv, hpν, hz]

end CFSG.CGT.PushingUpLit.CGT6M
