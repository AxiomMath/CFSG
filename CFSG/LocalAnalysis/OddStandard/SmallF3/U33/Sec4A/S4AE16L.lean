module

public import CFSG.LocalAnalysis.OddStandard.SmallF3.U33.Sec4A.S4AC0A
public import CFSG.LocalAnalysis.OddStandard.SmallF3.U33.Sec4A.S4ACosetCount
public import CFSG.LocalAnalysis.OddStandard.SmallF3.U33.WreathB
public import CFSG.GroupTheory.ElementaryAbelianTransport
public import CFSG.LocalAnalysis.SectionRank.PRank
public import CFSG.LocalAnalysis.OddStandard.SmallF3.U33.Sec4A.S4ADefs

public section

namespace CFSG.OddStandard.SmallF3.HarrisU33.S4A

open Subgroup

variable {G : Type} [Group G] [Finite G] {t : G} {L S : Subgroup G} {x₁ x₂ lam rho tau : G}

theorem card_le_four_of_elemAbelian_wreathGrp (h : WreathRel x₁ x₂ lam) {E : Subgroup G}
    (hE : E ≤ wreathGrp x₁ x₂ lam) (hEe : CFSG.Open.IsElemAbelian 2 E) : Nat.card E ≤ 4 := by
  haveI : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  obtain ⟨k, hk⟩ := IsPGroup.iff_card.mp hEe.isPGroup
  have hk2 : k ≤ CFSG.Open.pRank 2 (wreathGrp x₁ x₂ lam) :=
    CFSG.SectionRank.le_pRank (by norm_num) hE hEe hk
  rw [WreathRel.pRank_eq_two h] at hk2
  calc Nat.card E = 2 ^ k := hk
    _ ≤ 2 ^ 2 := (Nat.pow_le_pow_iff_right (by norm_num : 1 < 2)).mpr hk2
    _ = 4 := by norm_num

theorem relIndex_L_invCent_eq_four (h : Ctx t L S x₁ x₂ lam rho tau)
    (h43 : twoCore t = zpowers t) : L.relIndex (invCent t) = 4 := by
  have hFle : twoCore t ⊔ L ≤ invCent t :=
    sup_le (twoCore_le_invCent t) (L_le_invCent h.hyp)
  have hmul := Subgroup.relIndex_mul_relIndex (H := L) (K := twoCore t ⊔ L)
    (L := invCent t) le_sup_right hFle
  rw [h.relIndex_two] at hmul
  have hcardK : Nat.card (twoCore t ⊔ L : Subgroup G) = Nat.card (twoCore t) * Nat.card L :=
    card_sup_of_commute (twoCore_commute h.hyp) h.hyp.twoCore_inf
  have hPcard : Nat.card (twoCore t) = 2 := by
    rw [h43, Nat.card_zpowers, h.hyp.ord_t]
  have hrel : L.relIndex (twoCore t ⊔ L) = 2 := by
    have hlag := Subgroup.relIndex_mul_card (H := L) (K := twoCore t ⊔ L)
    rw [inf_eq_left.mpr le_sup_right] at hlag
    rw [hcardK, hPcard] at hlag
    have hpos : 0 < Nat.card L := by
      haveI : Nonempty ↥L := ⟨⟨1, L.one_mem⟩⟩
      exact Nat.card_pos
    exact Nat.mul_right_cancel hpos hlag
  rw [hrel] at hmul
  omega

theorem card_inf_L_of_E16 (h : Ctx t L S x₁ x₂ lam rho tau) (h43 : twoCore t = zpowers t)
    {Y : Subgroup G} (hY : IsE16In S Y) : Nat.card (Y ⊓ L : Subgroup G) = 4 := by
  obtain ⟨hYle, hYab, hYcard⟩ := hY
  have hYT : Y ⊓ L ≤ wreathGrp x₁ x₂ lam := by
    rw [← h.toCtx0.inf_eq]
    exact inf_le_inf hYle le_rfl
  have hEe : CFSG.Open.IsElemAbelian 2 (Y ⊓ L : Subgroup G) := hYab.mono inf_le_left
  have hle4 : Nat.card (Y ⊓ L : Subgroup G) ≤ 4 :=
    card_le_four_of_elemAbelian_wreathGrp h.wreath hYT hEe
  have hcount := card_le_card_inf_mul_relIndex (H := invCent t) (L := L) (Y := Y)
    (L_le_invCent h.hyp) (hYle.trans h.toCtx0.le_invCent)
  rw [relIndex_L_invCent_eq_four h h43, hYcard] at hcount
  omega

theorem exists_mem_E16_coset (h : Ctx t L S x₁ x₂ lam rho tau) (h43 : twoCore t = zpowers t)
    {Y : Subgroup G} (hY : IsE16In S Y) : ∀ g ∈ invCent t, ∃ y ∈ Y, g⁻¹ * y ∈ L := by
  refine exists_mem_coset_of_card_eq (H := invCent t) (L := L) (Y := Y)
    (L_le_invCent h.hyp) (hY.1.trans h.toCtx0.le_invCent) ?_
  rw [card_inf_L_of_E16 h h43 hY, relIndex_L_invCent_eq_four h h43, hY.2.2]

end CFSG.OddStandard.SmallF3.HarrisU33.S4A
