module

public import CFSG.Dihedral.DisconnectedInvolutionGraph.OddCore

public section

namespace CFSG.DisconnectedInvolutionGraph.Helpers

variable {G K : Type*} [Group G] [Group K] [Finite G]

omit [Finite G] in
theorem odd_kernel_preimage_odd (hom : G →* K) (hoddKernel : Odd (Nat.card hom.ker))
    (subgroup : Subgroup K) (hoddSubgroup : Odd (Nat.card subgroup)) :
    Odd (Nat.card (subgroup.comap hom)) := by
  let preimage := subgroup.comap hom
  let restricted : preimage →* subgroup :=
    (hom.comp preimage.subtype).codRestrict subgroup (by intro element; exact element.property)
  have hrangeOdd : Odd (Nat.card restricted.range) :=
    hoddSubgroup.of_dvd_nat restricted.range.card_subgroup_dvd_card
  let kernelEmbedding : restricted.ker →* hom.ker :=
    { toFun := fun element => ⟨element.val.val, congrArg Subtype.val element.property⟩
      map_one' := rfl
      map_mul' := fun _ _ => rfl }
  have hkernelInjective : Function.Injective kernelEmbedding := by
    intro first second hequal
    exact Subtype.ext (Subtype.ext
      (congrArg (fun element : hom.ker => element.val) hequal))
  have hkernelCard : Nat.card restricted.ker = Nat.card kernelEmbedding.range := by
    exact Nat.card_congr (MulEquiv.ofBijective kernelEmbedding.rangeRestrict
      ⟨(MonoidHom.rangeRestrict_injective_iff).mpr hkernelInjective,
        kernelEmbedding.rangeRestrict_surjective⟩).toEquiv
  have hkernelOdd : Odd (Nat.card restricted.ker) := by
    rw [hkernelCard]
    exact hoddKernel.of_dvd_nat kernelEmbedding.range.card_subgroup_dvd_card
  have hcard := restricted.ker.card_eq_card_quotient_mul_card_subgroup
  rw [Nat.card_congr (QuotientGroup.quotientKerEquivRange restricted).toEquiv] at hcard
  rw [hcard]
  exact hrangeOdd.mul hkernelOdd

theorem oddCore_quotient_eq_bot :
    let _ := oddCore_normal (G := G)
    oddCore (G ⧸ oddCore G) = ⊥ := by
  let _ := oddCore_normal (G := G)
  change oddCore (G ⧸ oddCore G) = ⊥
  let quotient := QuotientGroup.mk' (oddCore G)
  let quotientCore := oddCore (G ⧸ oddCore G)
  let preimage := quotientCore.comap quotient
  have hoddKernel : Odd (Nat.card quotient.ker) := by
    rw [QuotientGroup.ker_mk']
    exact oddCore_odd
  have hoddPreimage := odd_kernel_preimage_odd quotient hoddKernel quotientCore oddCore_odd
  have hnormalPreimage : preimage.Normal := by
    let _ := oddCore_normal (G := G ⧸ oddCore G)
    infer_instance
  have hpreimageLe := normal_odd_le_oddCore preimage hnormalPreimage hoddPreimage
  have hcoreLe : quotientCore ≤ (oddCore G).map quotient := by
    rw [← Subgroup.map_comap_eq_self_of_surjective (QuotientGroup.mk'_surjective (oddCore G))
      quotientCore]
    exact Subgroup.map_mono hpreimageLe
  have hmapBot : (oddCore G).map quotient = ⊥ := by
    apply ((oddCore G).map_eq_bot_iff).mpr
    rw [QuotientGroup.ker_mk']
  exact bot_unique (hmapBot ▸ hcoreLe)

end CFSG.DisconnectedInvolutionGraph.Helpers
