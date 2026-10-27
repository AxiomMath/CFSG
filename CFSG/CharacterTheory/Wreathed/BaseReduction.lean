module

public import CFSG.CharacterTheory.Wreathed.BaseNormalizer
public import CFSG.CharacterTheory.Wreathed.BaseFrattini
public import CFSG.GroupTheory.SylowActionKernel

public noncomputable section

namespace CFSG.Wreathed

open scoped Classical

universe u

theorem baseFrattiniQuotientEquiv_mk (n : ℕ) (hn : 1 ≤ n)
    (b : baseSubgroup (2 ^ n)) :
    baseFrattiniQuotientEquiv n hn ((QuotientGroup.mk'
      (frattini (baseSubgroup (2 ^ n)))) b) =
        CFSG.standardHomocyclicCoverReduction (Multiplicative (ZMod 2)) 2 n hn
          (baseHomocyclicEquiv (2 ^ n) b) := by
  rfl

theorem base_frattini_generators_distinct (n : ℕ) (hn : 1 ≤ n) :
    ((QuotientGroup.mk' (frattini (baseSubgroup (2 ^ n))))
      (⟨Original.s (2 ^ n), by simp [Original.s]⟩ : baseSubgroup (2 ^ n))) ≠
      ((QuotientGroup.mk' (frattini (baseSubgroup (2 ^ n))))
        (⟨Original.t (2 ^ n), by simp [Original.t]⟩ : baseSubgroup (2 ^ n))) := by
  intro h
  have hq := congrArg (baseFrattiniQuotientEquiv n hn) h
  rw [baseFrattiniQuotientEquiv_mk, baseFrattiniQuotientEquiv_mk] at hq
  have hc := congrArg (fun b : CFSG.StandardHomocyclicCover (Multiplicative (ZMod 2)) 2 =>
    Multiplicative.toAdd b (Multiplicative.ofAdd 0)) hq
  change (ZMod.castHom (dvd_pow_self 2 (Nat.ne_of_gt hn)) (ZMod 2)) 1 =
    (ZMod.castHom (dvd_pow_self 2 (Nat.ne_of_gt hn)) (ZMod 2)) 0 at hc
  have hbad : (1 : ZMod 2) = 0 := by simpa only [map_one, map_zero] using hc
  exact one_ne_zero hbad

variable {G : Type u} [Group G]

theorem modelBaseAction_sylow_coe {m : ℕ} (S : Sylow 2 G) (e : S ≃* Wreath m)
    (s : S) (b : baseSubgroup m) :
    (modelBaseAction S e ⟨s.val, sylow_le_modelBase_normalizer S e s.property⟩ b).val =
      e s * b.val * (e s)⁻¹ := by
  apply wreathModelHom_injective S e
  rw [modelBaseAction_coe, map_mul, map_mul, map_inv]
  have hs : wreathModelHom S e (e s) = s.val :=
    congrArg Subtype.val (e.symm_apply_apply s)
  rw [hs]

theorem base_action_on_sylow_kernel_of_reduction
    (n : ℕ) (hn : 1 ≤ n) (S : Sylow 2 G) (e : S ≃* Wreath (2 ^ n))
    (s : S)
    (hred : CFSG.LargeEvenClassification.Helpers.frattiniAutAction
      (baseSubgroup (2 ^ n))
        (modelBaseAction S e ⟨s.val, sylow_le_modelBase_normalizer S e s.property⟩) = 1) :
    modelBaseAction S e ⟨s.val, sylow_le_modelBase_normalizer S e s.property⟩ = 1 := by
  obtain ⟨⟨i, j, f⟩, hs⟩ := (coordinateEquiv (2 ^ n)).symm.surjective (e s)
  change element (2 ^ n) i j f = e s at hs
  rcases swap_exponent_cases f with rfl | rfl
  · apply MulEquiv.ext
    intro b
    apply Subtype.ext
    rw [modelBaseAction_sylow_coe, ← hs]
    obtain ⟨⟨a, c⟩, rfl⟩ := (baseCoordinateEquiv (2 ^ n)).symm.surjective b
    exact conjugate_base_by_base _ _ _ _ _
  · have hfix := DFunLike.congr_fun hred
      (((QuotientGroup.mk' (frattini (baseSubgroup (2 ^ n))))
        (⟨Original.s (2 ^ n), by simp [Original.s]⟩ : baseSubgroup (2 ^ n))))
    have hswap : modelBaseAction S e
        ⟨s.val, sylow_le_modelBase_normalizer S e s.property⟩
          (⟨Original.s (2 ^ n), by simp [Original.s]⟩ : baseSubgroup (2 ^ n)) =
      (⟨Original.t (2 ^ n), by simp [Original.t]⟩ : baseSubgroup (2 ^ n)) := by
      apply Subtype.ext
      rw [modelBaseAction_sylow_coe, ← hs]
      exact conjugate_base_by_swap _ _ _ _ _
    change (QuotientGroup.mk' (frattini (baseSubgroup (2 ^ n))))
      (modelBaseAction S e ⟨s.val, sylow_le_modelBase_normalizer S e s.property⟩
        (⟨Original.s (2 ^ n), by simp [Original.s]⟩ : baseSubgroup (2 ^ n))) =
      (QuotientGroup.mk' (frattini (baseSubgroup (2 ^ n))))
        (⟨Original.s (2 ^ n), by simp [Original.s]⟩ : baseSubgroup (2 ^ n)) at hfix
    rw [hswap] at hfix
    exact False.elim (base_frattini_generators_distinct n hn hfix.symm)

theorem modelBaseAction_range_reduction_injective [Finite G]
    (n : ℕ) (hn : 1 ≤ n) (S : Sylow 2 G) (e : S ≃* Wreath (2 ^ n)) :
    Function.Injective
      ((CFSG.LargeEvenClassification.Helpers.frattiniAutAction
        (baseSubgroup (2 ^ n))).domRestrict (modelBaseAction S e).range) := by
  apply CFSG.injective_on_image_of_isPGroup_ker_of_sylow
    (modelBaseNormalizerSylow S e) (modelBaseAction S e)
    (CFSG.LargeEvenClassification.Helpers.frattiniAutAction (baseSubgroup (2 ^ n)))
    (base_frattini_automorphism_kernel_isPGroup n)
  intro g hg hred
  rw [modelBaseNormalizerSylow_coe] at hg
  exact base_action_on_sylow_kernel_of_reduction n hn S e ⟨g.val, hg⟩ hred

end CFSG.Wreathed
