module

public import CFSG.LocalAnalysis.ProperTwoGeneratedCore.LocalCriterionCentralizerHullKernel
public import CFSG.LocalAnalysis.ProperTwoGeneratedCore.LocalCriterionClassFreeAffineHullAutomorphisms
public import CFSG.LocalAnalysis.ShultStronglyClosedTI.LocalEmbeddingConsequences

public noncomputable section

namespace CFSG.ProperTwoGeneratedCore.LocalCriterionCentralizerHull

open CFSG.BenderSuzuki CFSG.BenderSuzuki.PFAppendixIII
open CFSG.FiveTransitive.CharacteristicAutomorphism
open CFSG.ProperTwoGeneratedCore.LocalCriterionClassFreeAffineHull
open CFSG.ProperTwoGeneratedCore.LocalCriterionCosetNormalizerIndex
open CFSG.ShultStronglyClosedTI

universe u

variable {G : Type u} [Group G]

theorem center_odd_of_strong_embedding [Finite G] (P : Subgroup G)
    (hP : IsStronglyEmbedded P) : Odd (Nat.card (Subgroup.center G)) := by
  apply Nat.not_even_iff_odd.mp
  intro heven
  obtain ⟨x, hx⟩ := exists_prime_orderOf_dvd_card'
    (G := Subgroup.center G) 2 (even_iff_two_dvd.mp heven)
  have hxG : orderOf (x : G) = 2 := (Subgroup.orderOf_coe x).trans hx
  exact no_central_involution_of_strong_embedding hP
    ⟨(orderOf_eq_prime_iff.mp hxG).2, (orderOf_eq_prime_iff.mp hxG).1⟩ x.property

theorem inner_conjugation_ker : (MulAut.conj : G →* MulAut G).ker = Subgroup.center G := by
  ext x
  constructor
  · intro hx
    apply Subgroup.mem_center_iff.mpr
    intro y
    have hxy := congrArg (fun a : MulAut G => a y) hx
    have hconj : x * y * x⁻¹ = y := hxy
    have hm := congrArg (fun a : G => a * x) hconj
    simpa only [mul_assoc, inv_mul_cancel, mul_one] using hm.symm
  · intro hx
    apply MulEquiv.ext
    intro y
    change x * y * x⁻¹ = y
    rw [← Subgroup.mem_center_iff.mp hx y, mul_assoc, mul_inv_cancel, mul_one]

theorem inner_square_one_lift [Finite G]
    (hodd : Odd (Nat.card (Subgroup.center G))) (a : MulAut G)
    (ha : a ∈ innerAutomorphismSubgroup G) (hsq : a ^ 2 = 1) :
    ∃ x : G, x ^ 2 = 1 ∧ MulAut.conj x = a := by
  by_cases haone : a = 1
  · exact ⟨1, by simp, by simpa only [map_one] using haone.symm⟩
  · let f : G →* innerAutomorphismSubgroup G := (MulAut.conj : G →* MulAut G).rangeRestrict
    have hker : f.ker = Subgroup.center G := by
      change (MulAut.conj : G →* MulAut G).rangeRestrict.ker = Subgroup.center G
      rw [MonoidHom.ker_rangeRestrict, inner_conjugation_ker]
    have haI : IsInvolution (⟨a, ha⟩ : innerAutomorphismSubgroup G) :=
      ⟨fun h => haone (congrArg Subtype.val h), Subtype.ext hsq⟩
    obtain ⟨x, hx, hfx⟩ := involution_lift_of_central_odd_kernel f
      (MonoidHom.rangeRestrict_surjective _) (hker.symm ▸ hodd)
      (hker.symm ▸ (show Subgroup.center G ≤ Subgroup.center G from le_rfl)) haI
    exact ⟨x, hx.sq_eq_one, congrArg Subtype.val hfx⟩

theorem characteristic_quotient_conj (N : Subgroup G) [N.Characteristic] (x : G) :
    quotient N (MulAut.conj x) = MulAut.conj (QuotientGroup.mk' N x) := by
  apply MulEquiv.ext
  intro y
  refine Quotient.inductionOn y ?_
  intro a
  change quotient N (MulAut.conj x) (QuotientGroup.mk' N a) =
    MulAut.conj (QuotientGroup.mk' N x) (QuotientGroup.mk' N a)
  simp only [quotient_apply_mk, MulAut.conj_apply, map_mul, map_inv]

theorem normal_quotient_inner_square_one_lift [Finite G]
    (L : Subgroup G) [L.Normal] (N : Subgroup L) [N.Characteristic]
    (hodd : Odd (Nat.card N)) (hcentral : N ≤ Subgroup.center L)
    (hgen : Subgroup.closure {x : L | IsInvolution x} = ⊤)
    (hcenter : Odd (Nat.card (Subgroup.center L))) (x : G) (hx : x ^ 2 = 1)
    (hinner : normalQuotientConjugation L N x ∈ innerAutomorphismSubgroup (L ⧸ N)) :
    ∃ l : L, l ^ 2 = 1 ∧ MulAut.conjNormal x = MulAut.conj l := by
  obtain ⟨y, hy⟩ := hinner
  obtain ⟨a, ha⟩ := QuotientGroup.mk'_surjective N y
  have hquotient : quotient N (MulAut.conj a) = quotient N (MulAut.conjNormal x) := by
    rw [characteristic_quotient_conj, ha]
    exact hy
  have hinjective : Function.Injective (quotient N) :=
    (quotient N).ker_eq_bot_iff.mp (characteristic_quotient_ker_eq_bot N hodd hcentral hgen)
  have haction : MulAut.conj a = MulAut.conjNormal x := hinjective hquotient
  have hsquare : (MulAut.conjNormal (H := L) x) ^ 2 = 1 := by
    rw [← map_pow, hx, map_one]
  obtain ⟨l, hl, hlaction⟩ := inner_square_one_lift hcenter
    (MulAut.conjNormal x) ⟨a, haction⟩ hsquare
  exact ⟨l, hl, hlaction.symm⟩

end CFSG.ProperTwoGeneratedCore.LocalCriterionCentralizerHull
