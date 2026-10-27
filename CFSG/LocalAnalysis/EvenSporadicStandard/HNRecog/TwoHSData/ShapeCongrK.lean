module

public import CFSG.LocalAnalysis.EvenSporadicStandard.HNRecog.TwoHSData.ShapeCongr

public section

namespace CFSG.EvenSporadicStandard.HNRecog

open Subgroup

universe u v

variable {X : Type u} {X' : Type v} [Group X] [Group X']

theorem IsPlusExtraspecial.map_mulEquiv {m : ℕ} {Γ Γ' : Type*} [Group Γ] [Group Γ'] (e : Γ ≃* Γ')
    {D : Subgroup Γ} (h : IsPlusExtraspecial m D) :
    IsPlusExtraspecial m (D.map e.toMonoidHom) := by
  obtain ⟨hExt, hcard, E, hED, hEel, hEcard⟩ := h
  refine ⟨TwoHSData.isExtraspecial_of_mulEquiv (TwoHSData.mapMulEquiv e D) hExt, ?_,
    E.map e.toMonoidHom, Subgroup.map_mono hED, ?_, ?_⟩
  · rw [Subgroup.card_map_of_injective e.injective, hcard]
  · haveI : IsMulCommutative ↥E := hEel.1
    exact ⟨inferInstance, fun x hx => by
      obtain ⟨y, hy, rfl⟩ := Subgroup.mem_map.mp hx
      rw [← map_pow, hEel.2 y hy, map_one]⟩
  · rw [Subgroup.card_map_of_injective e.injective, hEcard]

theorem IsShapeK.of_mulEquiv (e : X ≃* X') (h : IsShapeK X) : IsShapeK X' := by
  obtain ⟨N, hNn, hNp, hNcard, ⟨hquot⟩, ⟨hcen⟩, Q, hQplus, hQsup, hQcard⟩ := h
  haveI : N.Normal := hNn
  let N' : Subgroup X' := N.map e.toMonoidHom
  let φ : N ≃* N' := TwoHSData.mapMulEquiv e N
  haveI : N'.Normal := TwoHSData.instNormalMapMulEquiv e N
  let Q' : Subgroup N' := Q.map φ.toMonoidHom
  have hmap_center : (Subgroup.center N).map φ.toMonoidHom = Subgroup.center N' := by
    apply le_antisymm
    · exact Subgroup.map_center_le_center φ.surjective
    · rintro x hx
      obtain ⟨y, rfl⟩ := φ.surjective x
      refine Subgroup.mem_map.mpr ⟨y, ?_, rfl⟩
      rw [Subgroup.mem_center_iff] at hx ⊢
      intro z
      apply φ.injective
      rw [map_mul, map_mul]
      exact hx (φ z)
  refine ⟨N', inferInstance, hNp.of_equiv φ, (Nat.card_congr φ.toEquiv).symm.trans hNcard,
    ⟨(TwoHSData.quotMapMulEquiv e N).symm.trans hquot⟩,
    ⟨(Subgroup.centerCongr φ).symm.trans hcen⟩, Q',
    IsPlusExtraspecial.map_mulEquiv φ hQplus, ?_, ?_⟩
  · have h := congrArg (Subgroup.map φ.toMonoidHom) hQsup
    rw [Subgroup.map_sup, hmap_center,
      Subgroup.map_top_of_surjective φ.toMonoidHom φ.surjective] at h
    exact h
  · have hinf : (Subgroup.center N ⊓ Q).map φ.toMonoidHom = Subgroup.center N' ⊓ Q' := by
      rw [Subgroup.map_inf_eq (Subgroup.center N) Q φ.toMonoidHom φ.injective, hmap_center]
    rw [← hinf, Subgroup.card_map_of_injective φ.injective, hQcard]

end CFSG.EvenSporadicStandard.HNRecog
