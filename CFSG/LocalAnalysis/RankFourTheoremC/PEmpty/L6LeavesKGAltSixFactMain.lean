module

public import CFSG.LocalAnalysis.RankFourTheoremC.PEmpty.L6LeavesKGAltSixFactPerm
public import CFSG.LocalAnalysis.RankFourTheoremC.PEmpty.L6LeavesKGDefs

public section

namespace CFSG.LocalAnalysis.RankFourTheoremC.PEmpty

open KGAltSixFact

theorem kGAltSix_of_hom {G : Type} [Group G] [Finite G] (ι : G →* Equiv.Perm (Fin 6))
    (hι : Function.Injective ι) (S : Subgroup G) (z : G) (hz : orderOf z = 5)
    (hS : IsPGroup 2 S) (hzS : z ∈ Subgroup.normalizer (S : Set G)) : S = ⊥ := by
  have h5 : z ^ 5 = 1 := by
    rw [← hz]
    exact pow_orderOf_eq_one z
  have hT2 : IsPGroup 2 (S.map ι) := by
    obtain ⟨n, hn⟩ := (IsPGroup.iff_card).1 hS
    exact (IsPGroup.iff_card).2 ⟨n, by rw [Subgroup.card_map_of_injective hι, hn]⟩
  have hσ5 : (ι z) ^ 5 = 1 := by
    rw [← map_pow, h5, map_one]
  have hσ1 : ι z ≠ 1 := by
    intro h
    have hz1 : z = 1 := hι (by rw [h, map_one])
    rw [hz1, orderOf_one] at hz
    norm_num at hz
  have hnorm : ∀ t : Equiv.Perm (Fin 6), t ∈ S.map ι ↔ ι z * t * (ι z)⁻¹ ∈ S.map ι := by
    intro t
    constructor
    · rintro ⟨s, hs, rfl⟩
      have hzs : z * s * z⁻¹ ∈ S := (Subgroup.mem_set_normalizer_iff.1 hzS s).1 hs
      have e : ι z * ι s * (ι z)⁻¹ = ι (z * s * z⁻¹) := by
        simp [map_mul, map_inv]
      rw [e]
      exact Subgroup.mem_map_of_mem ι hzs
    · rintro ⟨s, hs, hsy⟩
      have hzs : z⁻¹ * s * z ∈ S := by
        apply (Subgroup.mem_set_normalizer_iff.1 hzS (z⁻¹ * s * z)).2
        have e : z * (z⁻¹ * s * z) * z⁻¹ = s := by group
        rw [e]
        exact hs
      refine Subgroup.mem_map.2 ⟨z⁻¹ * s * z, hzs, ?_⟩
      rw [map_mul, map_mul, map_inv, hsy]
      group
  have hTbot : S.map ι = ⊥ := core_perm (ι z) (S.map ι) hσ5 hσ1 hT2 hnorm
  rw [Subgroup.eq_bot_iff_forall]
  intro s hs
  have hmem : ι s ∈ S.map ι := Subgroup.mem_map_of_mem ι hs
  rw [hTbot, Subgroup.mem_bot] at hmem
  exact hι (hmem.trans (map_one ι).symm)

theorem kGAltSix_of_embed {A : Type} [Group A] [Finite A] (X S : Subgroup A) (z : A)
    (ι : X →* Equiv.Perm (Fin 6)) (hι : Function.Injective ι) (hz : orderOf z = 5)
    (hzX : z ∈ X) (hSX : S ≤ X) (hS : IsPGroup 2 S)
    (hzS : z ∈ Subgroup.normalizer (S : Set A)) : S = ⊥ := by
  have hS' : IsPGroup 2 (S.subgroupOf X) := by
    obtain ⟨n, hn⟩ := (IsPGroup.iff_card).1 hS
    refine (IsPGroup.iff_card).2 ⟨n, ?_⟩
    rw [Nat.card_congr (Subgroup.subgroupOfEquivOfLe hSX).toEquiv, hn]
  have hz' : orderOf (⟨z, hzX⟩ : X) = 5 := by
    rw [Subgroup.orderOf_mk]
    exact hz
  have hz'S : (⟨z, hzX⟩ : X) ∈ Subgroup.normalizer ((S.subgroupOf X : Subgroup X) : Set X) := by
    rw [Subgroup.mem_set_normalizer_iff]
    intro h
    simp only [SetLike.mem_coe, Subgroup.mem_subgroupOf, Subgroup.coe_mul, Subgroup.coe_inv]
    exact Subgroup.mem_set_normalizer_iff.1 hzS h
  have hbot := kGAltSix_of_hom ι hι (S.subgroupOf X) ⟨z, hzX⟩ hz' hS' hz'S
  rw [Subgroup.eq_bot_iff_forall]
  intro s hs
  have hmem : (⟨s, hSX hs⟩ : X) ∈ S.subgroupOf X := Subgroup.mem_subgroupOf.2 hs
  rw [hbot, Subgroup.mem_bot] at hmem
  exact congrArg Subtype.val hmem

theorem kGAltSix_holds : KGAltSix := by
  intro A _ _ X S z hX hz hzX hSX hS hzS
  rcases hX with h | h
  · obtain ⟨e⟩ := h
    exact kGAltSix_of_embed X S z
      ((alternatingGroup (Fin 6)).subtype.comp e.toMonoidHom)
      (Subtype.val_injective.comp e.injective) hz hzX hSX hS hzS
  · obtain ⟨e⟩ := h
    exact kGAltSix_of_embed X S z e.toMonoidHom e.injective hz hzX hSX hS hzS

end CFSG.LocalAnalysis.RankFourTheoremC.PEmpty

end
