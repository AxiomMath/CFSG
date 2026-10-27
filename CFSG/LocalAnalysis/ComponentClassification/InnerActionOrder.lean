module

public import CFSG.LocalAnalysis.ComponentClassification.OuterAutomorphisms

public section

namespace CFSG.ComponentClassification.InnerActionOrder

theorem conjugation_kernel (G : Type*) [Group G] : (MulAut.conj : G →* MulAut G).ker = Subgroup.center G := by
  ext element
  constructor
  · intro hkernel
    apply Subgroup.mem_center_iff.mpr
    intro other
    have heq := congrArg (fun automorphism : MulAut G => automorphism other) hkernel
    change element * other * element⁻¹ = other at heq
    have hmul := congrArg (fun member : G => member * element) heq
    simpa only [mul_assoc, inv_mul_cancel, mul_one] using hmul.symm
  · intro hcentral
    apply MulEquiv.ext
    intro other
    change element * other * element⁻¹ = other
    rw [← Subgroup.mem_center_iff.mp hcentral other, mul_assoc, mul_inv_cancel, mul_one]

theorem inner_card (G : Type*) [Group G] :
    Nat.card (OuterAutomorphisms.inner G) = Nat.card (G ⧸ Subgroup.center G) := by
  change Nat.card (MulAut.conj : G →* MulAut G).range = _
  rw [← Subgroup.index_ker (MulAut.conj : G →* MulAut G), conjugation_kernel, Subgroup.index_eq_card]

theorem centerless_card (G : Type*) [Group G] (hcenter : Subgroup.center G = ⊥) :
    Nat.card (OuterAutomorphisms.inner G) = Nat.card G := by
  rw [inner_card, hcenter]
  exact Nat.card_congr (QuotientGroup.quotientBot (G := G)).toEquiv

theorem image_card {G : Type*} [Group G] (image : Subgroup (MulAut G))
    (hinner : OuterAutomorphisms.inner G ≤ image) :
    Nat.card image = Nat.card (OuterAutomorphisms.inner G) *
      Nat.card (((QuotientGroup.mk' (OuterAutomorphisms.inner G)).comp image.subtype).range) := by
  let quotient := (QuotientGroup.mk' (OuterAutomorphisms.inner G)).comp image.subtype
  have hkernel : quotient.ker = (OuterAutomorphisms.inner G).subgroupOf image := by
    ext automorphism
    exact QuotientGroup.eq_one_iff automorphism.val
  have hkernelCard : Nat.card quotient.ker = Nat.card (OuterAutomorphisms.inner G) := by
    rw [hkernel]
    exact Nat.card_congr (Subgroup.subgroupOfEquivOfLe hinner).toEquiv
  have hcard := quotient.ker.card_mul_index
  rw [Subgroup.index_ker, hkernelCard] at hcard
  exact hcard.symm

end CFSG.ComponentClassification.InnerActionOrder
