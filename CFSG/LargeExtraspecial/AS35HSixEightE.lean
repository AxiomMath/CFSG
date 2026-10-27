module

public import CFSG.LargeExtraspecial.AS35HQuot
public import CFSG.LargeExtraspecial.Setting
public import CFSG.RankThree.OrthogonalInvolutions.Basic

public section

attribute [-instance] instAddCommGroupOfIsSimpleAddGroupOfIsNilpotent
  instCommGroupOfIsSimpleGroupOfIsNilpotent

namespace CFSG.LargeExtraspecial

open Subgroup Module CFSG.RankThree.OrthogonalInvolutions CQuot

namespace Setting

variable {G : Type} [Group G] [Finite G] (S : Setting G)

omit [Finite G] in
theorem conj_mem_range_of_card_le {K X : Type} [Group K] [Group X] [Finite K] (f : X →* K)
    (hcard : Nat.card (K ⧸ center K) ≤
      Nat.card ((QuotientGroup.mk' (center K)).comp f).range)
    (g : K) {v : K} (hv : v ∈ f.range) : g * v * g⁻¹ ∈ f.range := by
  have htop : ((QuotientGroup.mk' (center K)).comp f).range = ⊤ :=
    Subgroup.eq_top_of_le_card _ hcard
  have hg : QuotientGroup.mk' (center K) g ∈ ((QuotientGroup.mk' (center K)).comp f).range := by
    rw [htop]
    exact mem_top _
  obtain ⟨w, hw⟩ := hg
  have hζ : (f w)⁻¹ * g ∈ center K := QuotientGroup.eq.mp hw
  obtain ⟨w', rfl⟩ := hv
  refine ⟨w * w' * w⁻¹, ?_⟩
  rw [map_mul, map_mul, map_inv]
  have hc := mem_center_iff.mp hζ (f w')
  calc f w * f w' * (f w)⁻¹ = f w * ((f w' * ((f w)⁻¹ * g)) * ((f w)⁻¹ * g)⁻¹) * (f w)⁻¹ := by
        group
    _ = f w * ((((f w)⁻¹ * g) * f w') * ((f w)⁻¹ * g)⁻¹) * (f w)⁻¹ := by rw [hc]
    _ = g * f w' * g⁻¹ := by group

end Setting

end CFSG.LargeExtraspecial
