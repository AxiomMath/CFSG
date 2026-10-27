module

public import CFSG.LargeExtraspecial.RepresentationSupport.ExtraspecialTwoScalarCenterDimensionBound

public section

namespace CFSG.LargeExtraspecial

namespace RepresentationSupport

namespace ExtraspecialTwoFaithfulDimensionBound

theorem dimension_lower_bound {F : Type*} [Field F] (hF : (2 : F) ≠ 0)
    {W : Type*} [AddCommGroup W] [Module F W] [Module.Finite F W]
    {E : Type*} [Group E] [Finite E] (hE : CFSG.IsExtraspecialPGroup 2 E)
    {w : ℕ} (hcard : Nat.card E = 2 ^ (1 + 2 * w))
    (ρ : Representation F E W) (hρ : Function.Injective ρ) :
    2 ^ w ≤ Module.finrank F W := by
  classical
  have hcen : Nat.card (Subgroup.center E) = 2 := hE.2.2.2
  haveI : Finite (Subgroup.center E) := inferInstance
  have hnt : Nontrivial (Subgroup.center E) := by
    rw [← Finite.one_lt_card_iff_nontrivial, hcen]; norm_num
  obtain ⟨z', hz'⟩ := exists_ne (1 : Subgroup.center E)
  set z : E := (z' : E) with hzdef
  have hz : z ∈ Subgroup.center E := z'.2
  have hz1 : z ≠ 1 := fun h => hz' (Subtype.ext h)
  have hz2 : z ^ 2 = 1 := by
    have := pow_card_eq_one' (G := Subgroup.center E) (x := z')
    rw [hcen] at this
    exact congrArg Subtype.val this
  have hρz2 : ρ z * ρ z = 1 := by rw [← map_mul, ← pow_two, hz2, map_one]
  have hρz1 : ρ z ≠ 1 := fun h => hz1 (hρ (by rw [h, map_one]))
  let M : Submodule F W := LinearMap.ker (ρ z + LinearMap.id)
  have hM : ∀ g, M ≤ M.comap (ρ g) := by
    intro g v hv
    have hv' : ρ z v = -v := by
      have : ρ z v + v = 0 := hv
      exact eq_neg_of_add_eq_zero_left this
    show ρ z (ρ g v) + ρ g v = 0
    have hc : ρ z * ρ g = ρ g * ρ z := by
      rw [← map_mul, ← map_mul, (Subgroup.mem_center_iff.1 hz g)]
    have : ρ z (ρ g v) = ρ g (ρ z v) := congrArg (fun f => f v) hc
    rw [this, hv', map_neg, neg_add_cancel]
  haveI : Nontrivial M := by
    have : ∃ v, ρ z v ≠ v := by
      by_contra h
      push Not at h
      exact hρz1 (LinearMap.ext fun v => by simpa using h v)
    obtain ⟨v, hv⟩ := this
    have hzu : ρ z (v - ρ z v) = -(v - ρ z v) := by
      have : ρ z (ρ z v) = v := congrArg (fun f => f v) hρz2
      rw [map_sub, this]; abel
    refine ⟨⟨⟨v - ρ z v, ?_⟩, 0, ?_⟩⟩
    · show ρ z (v - ρ z v) + (v - ρ z v) = 0
      rw [hzu, neg_add_cancel]
    · intro h
      have := congrArg Subtype.val h
      exact hv (sub_eq_zero.1 this).symm
  let σ : Representation F E M := Representation.subrepresentation ρ M hM
  have hσ : σ z = -LinearMap.id := by
    ext ⟨v, hv⟩
    have hv' : ρ z v = -v := by
      have : ρ z v + v = 0 := hv
      exact eq_neg_of_add_eq_zero_left this
    simp [σ, hv']
  have h := ExtraspecialTwoScalarCenterDimensionBound.dimension_lower_bound hF hE hcard σ z hz hz1 hσ
  exact h.trans (Submodule.finrank_le M)

end ExtraspecialTwoFaithfulDimensionBound

end RepresentationSupport

end CFSG.LargeExtraspecial
