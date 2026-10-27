module

public import CFSG.CharacterTheory.Wreathed.BaseReduction
public import CFSG.GroupTheory.KleinFourAutomorphism

public noncomputable section

namespace CFSG.Wreathed

open scoped Classical

universe u

theorem base_frattini_quotient_isKleinFour (n : ℕ) (hn : 1 ≤ n) :
    IsKleinFour (baseSubgroup (2 ^ n) ⧸ frattini (baseSubgroup (2 ^ n))) := by
  constructor
  · exact base_frattini_quotient_card n hn
  · rw [Monoid.exponent_eq_of_mulEquiv (baseFrattiniQuotientEquiv n hn)]
    exact CFSG.standardHomocyclicCover_exponent (Multiplicative (ZMod 2)) 2

variable {G : Type u} [Group G]

@[expose] def modelBaseSwapActor {m : ℕ} (S : Sylow 2 G) (e : S ≃* Wreath m) :
    Subgroup.normalizer (modelBase S e : Set G) :=
  ⟨(e.symm (Original.z m)).val,
    sylow_le_modelBase_normalizer S e (e.symm (Original.z m)).property⟩

theorem modelBaseSwapActor_order {m : ℕ} (S : Sylow 2 G) (e : S ≃* Wreath m) :
    orderOf (modelBaseSwapActor S e) = 2 := by
  rw [← Subgroup.orderOf_coe]
  change orderOf (wreathModelHom S e (Original.z m)) = 2
  rw [orderOf_injective _ (wreathModelHom_injective S e)]
  exact Original.orderOf_z m

theorem modelBaseSwapAction_order (n : ℕ) (hn : 1 ≤ n)
    (S : Sylow 2 G) (e : S ≃* Wreath (2 ^ n)) :
    orderOf (modelBaseAction S e (modelBaseSwapActor S e)) = 2 := by
  let a := modelBaseAction S e (modelBaseSwapActor S e)
  have hpow : a ^ 2 = 1 := by
    rw [← map_pow]
    have h := pow_orderOf_eq_one (modelBaseSwapActor S e)
    rw [modelBaseSwapActor_order] at h
    rw [h, map_one]
  have hne : a ≠ 1 := by
    intro hone
    have hfix := DFunLike.congr_fun hone
      (⟨Original.s (2 ^ n), by simp [Original.s]⟩ : baseSubgroup (2 ^ n))
    have hswap : a
        (⟨Original.s (2 ^ n), by simp [Original.s]⟩ : baseSubgroup (2 ^ n)) =
      (⟨Original.t (2 ^ n), by simp [Original.t]⟩ : baseSubgroup (2 ^ n)) := by
      apply Subtype.ext
      change (modelBaseAction S e
        ⟨(e.symm (Original.z (2 ^ n))).val,
          sylow_le_modelBase_normalizer S e (e.symm (Original.z (2 ^ n))).property⟩
        (⟨Original.s (2 ^ n), by simp [Original.s]⟩ : baseSubgroup (2 ^ n))).val = _
      rw [modelBaseAction_sylow_coe, e.apply_symm_apply]
      exact conjugate_base_by_swap _ _ _ _ _
    rw [hswap] at hfix
    exact base_frattini_generators_distinct n hn
      (congrArg (QuotientGroup.mk' (frattini (baseSubgroup (2 ^ n)))) hfix.symm)
  let : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  exact orderOf_eq_prime_iff.mpr ⟨hpow, hne⟩

@[expose] def modelBaseReducedImage (n : ℕ) (S : Sylow 2 G)
    (e : S ≃* Wreath (2 ^ n)) :
    Subgroup (MulAut (baseSubgroup (2 ^ n) ⧸ frattini (baseSubgroup (2 ^ n)))) :=
  ((CFSG.LargeEvenClassification.Helpers.frattiniAutAction
    (baseSubgroup (2 ^ n))).domRestrict (modelBaseAction S e).range).range

@[expose] def modelBaseImageReductionEquiv [Finite G]
    (n : ℕ) (hn : 1 ≤ n) (S : Sylow 2 G) (e : S ≃* Wreath (2 ^ n)) :
    (modelBaseAction S e).range ≃* modelBaseReducedImage n S e :=
  MonoidHom.ofInjective (modelBaseAction_range_reduction_injective n hn S e)

theorem modelBaseImage_alternatives [Finite G] (n : ℕ) (hn : 1 ≤ n)
    (S : Sylow 2 G) (e : S ≃* Wreath (2 ^ n)) :
    Nat.card (modelBaseAction S e).range = 2 ∨
      Nonempty ((modelBaseAction S e).range ≃* Equiv.Perm (Fin 3)) := by
  let E := baseSubgroup (2 ^ n) ⧸ frattini (baseSubgroup (2 ^ n))
  let : IsKleinFour E := base_frattini_quotient_isKleinFour n hn
  let a : (modelBaseAction S e).range :=
    ⟨modelBaseAction S e (modelBaseSwapActor S e), ⟨modelBaseSwapActor S e, rfl⟩⟩
  let f := (CFSG.LargeEvenClassification.Helpers.frattiniAutAction
    (baseSubgroup (2 ^ n))).domRestrict (modelBaseAction S e).range
  have ha : orderOf a = 2 := by
    rw [← Subgroup.orderOf_coe]
    exact modelBaseSwapAction_order n hn S e
  have hf : Function.Injective f := modelBaseAction_range_reduction_injective n hn S e
  have hfa : orderOf (f a) = 2 := by rw [orderOf_injective f hf, ha]
  rcases CFSG.kleinFour_automorphism_subgroup_alternatives E
    (modelBaseReducedImage n S e) (f a) ⟨a, rfl⟩ hfa with htwo | hsix
  · exact Or.inl ((Nat.card_congr (modelBaseImageReductionEquiv n hn S e).toEquiv).trans htwo)
  · obtain ⟨esix⟩ := hsix
    exact Or.inr ⟨(modelBaseImageReductionEquiv n hn S e).trans esix⟩

end CFSG.Wreathed
