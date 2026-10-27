module

public import CFSG.CharacterTheory.Wreathed.BaseNormalizerQuotient
public import CFSG.CharacterTheory.Wreathed.BaseOmega
public import CFSG.CharacterTheory.Wreathed.VNormalizerAction
public import CFSG.GroupTheory.PrimePowerActionLift

public noncomputable section

namespace CFSG.Wreathed

open scoped Classical

universe u

variable {G : Type u} [Group G] [Finite G]

theorem modelBaseNormalizer_involutions_transitive (n : ℕ) (hn : 1 ≤ n)
    (S : Sylow 2 G) (e : S ≃* Wreath (2 ^ n))
    (hsix : Nonempty (Subgroup.normalizer (modelBase S e : Set G) ⧸
      (Subgroup.centralizer (modelBase S e : Set G)).subgroupOf
        (Subgroup.normalizer (modelBase S e : Set G)) ≃* Equiv.Perm (Fin 3)))
    (x y : G) (hx : x ∈ modelBase S e) (hy : y ∈ modelBase S e)
    (hxorder : orderOf x = 2) (hyorder : orderOf y = 2) :
    ∃ g : G, g ∈ Subgroup.normalizer (modelBase S e : Set G) ∧ g * x * g⁻¹ = y := by
  obtain ⟨esix⟩ := hsix
  have hcard : Nat.card (modelBaseAction S e).range = 6 := by
    rw [← Nat.card_congr (modelBaseNormalizerQuotientEquiv S e).toEquiv,
      Nat.card_congr esix.toEquiv, Nat.card_eq_fintype_card, Fintype.card_perm]
    decide
  let f := CFSG.LargeEvenClassification.Helpers.frattiniAutAction (baseSubgroup (2 ^ n))
  have hred : (modelBaseAction S e).range.map f = modelBaseReducedImage n S e := by
    unfold modelBaseReducedImage
    change (modelBaseAction S e).range.map f =
      (f.comp (modelBaseAction S e).range.subtype).range
    rw [MonoidHom.range_comp]
    rw [Subgroup.range_subtype]
  have hcardRed : Nat.card ((modelBaseAction S e).range.map f) = 6 := by
    rw [hred, ← Nat.card_congr (modelBaseImageReductionEquiv n hn S e).toEquiv, hcard]
  let xB : modelBase S e := ⟨x, hx⟩
  let yB : modelBase S e := ⟨y, hy⟩
  let x0 := (modelBaseEquiv S e).symm xB
  let y0 := (modelBaseEquiv S e).symm yB
  have hx0 : orderOf x0 = 2 :=
    ((modelBaseEquiv S e).symm.orderOf_eq xB).trans
      ((Subgroup.orderOf_coe xB).symm.trans hxorder)
  have hy0 : orderOf y0 = 2 :=
    ((modelBaseEquiv S e).symm.orderOf_eq yB).trans
      ((Subgroup.orderOf_coe yB).symm.trans hyorder)
  obtain ⟨a, ha⟩ := base_involutions_transitive_of_frattini_image_card_six n hn
    (modelBaseAction S e).range hcardRed x0 y0 hx0 hy0
  obtain ⟨g, hg⟩ := a.property
  have hpoint : modelBaseAction S e g x0 = y0 := by
    rw [hg]
    exact ha
  have h := congrArg (fun b : baseSubgroup (2 ^ n) => wreathModelHom S e b.val) hpoint
  rw [modelBaseAction_coe] at h
  have hxactual : wreathModelHom S e x0.val = x := by
    exact congrArg Subtype.val ((modelBaseEquiv S e).apply_symm_apply xB)
  have hyactual : wreathModelHom S e y0.val = y := by
    exact congrArg Subtype.val ((modelBaseEquiv S e).apply_symm_apply yB)
  rw [hxactual, hyactual] at h
  exact ⟨g.val, g.property, h⟩

theorem modelVNormalizer_exists_odd_three_power_actor (n : ℕ) (hn : 2 ≤ n)
    (S : Sylow 2 G) (e : S ≃* Wreath (2 ^ n))
    (hsix : Nonempty (Subgroup.normalizer (modelV S e : Set G) ⧸
      modelVInnerCentralizer S e ≃* Equiv.Perm (Fin 3))) :
    ∃ g : Subgroup.normalizer (modelV S e : Set G),
      (∃ k : ℕ, 0 < k ∧ orderOf g = 3 ^ k) ∧ Odd (orderOf g) ∧
        orderOf (modelVQuotientAction S e g) = 3 := by
  let : Fact (Nat.Prime 3) := ⟨by decide⟩
  obtain ⟨esix⟩ := hsix
  have hcard : Nat.card (modelVQuotientAction S e).range = 6 := by
    rw [← Nat.card_congr (modelVNormalizerQuotientEquiv n hn S e).toEquiv,
      Nat.card_congr esix.toEquiv, Nat.card_eq_fintype_card, Fintype.card_perm]
    decide
  obtain ⟨a, haorder⟩ := exists_prime_orderOf_dvd_card' 3
    (by rw [hcard]; decide : 3 ∣ Nat.card (modelVQuotientAction S e).range)
  have haorderA : orderOf a.val = 3 :=
    (Subgroup.orderOf_coe a).trans haorder
  obtain ⟨g, hg, k, hk, hgorder⟩ := CFSG.exists_prime_power_order_representative 3
    (modelVQuotientAction S e) a.val a.property haorderA
  refine ⟨g, ⟨k, hk, hgorder⟩, ?_, ?_⟩
  · rw [hgorder]
    exact (by decide : Odd (3 : ℕ)).pow
  · rw [hg]
    exact haorderA

omit [Finite G] in
theorem modelVNormalizer_order_three_cycles_all_nonzero (n : ℕ) (hn : 2 ≤ n)
    (S : Sylow 2 G) (e : S ≃* Wreath (2 ^ n))
    (g : Subgroup.normalizer (modelV S e : Set G))
    (horder : orderOf (modelVQuotientAction S e g) = 3)
    (x : Original.V (2 ^ n) ⧸ Subgroup.center (Original.V (2 ^ n))) (hx : x ≠ 1) :
    modelVQuotientAction S e g x ≠ x ∧
      modelVQuotientAction S e g (modelVQuotientAction S e g x) ≠ x ∧
      modelVQuotientAction S e g (modelVQuotientAction S e g x) ≠
        modelVQuotientAction S e g x ∧
      ∀ y : Original.V (2 ^ n) ⧸ Subgroup.center (Original.V (2 ^ n)), y ≠ 1 →
        y = x ∨ y = modelVQuotientAction S e g x ∨
          y = modelVQuotientAction S e g (modelVQuotientAction S e g x) := by
  let : IsKleinFour (Original.V (2 ^ n) ⧸ Subgroup.center (Original.V (2 ^ n))) :=
    original_v_center_quotient_isKleinFour n hn
  exact CFSG.kleinFour_order_three_cycle _ (modelVQuotientAction S e g) horder x hx

end CFSG.Wreathed
