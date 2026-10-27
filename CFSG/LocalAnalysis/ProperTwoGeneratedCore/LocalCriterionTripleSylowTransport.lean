module

public import CFSG.LocalAnalysis.ProperTwoGeneratedCore.LocalCriterionOddQuotient
public import CFSG.LocalAnalysis.ProperTwoGeneratedCore.LocalCriterionThreePointOddCore

public noncomputable section

namespace CFSG.ProperTwoGeneratedCore.LocalCriterionTripleSylow

open CFSG.ShultStronglyClosedTI
open CFSG.BenderSuzuki.PFAppendixIII CFSG.BenderSuzuki.PFchapter1section1
open CFSG.ProperTwoGeneratedCore.LocalCriterionGeometry

universe u

variable {G : Type u} [Group G]

theorem mem_right_conjugate_iff (H : Subgroup G) (x a : G) :
    a ∈ rightConjugate H x ↔ x * a * x⁻¹ ∈ H := by
  change a ∈ H.map (MulAut.conj x⁻¹).toMonoidHom ↔ _
  rw [Subgroup.mem_map_equiv]
  simp only [MulAut.conj_symm_apply, inv_inv]

theorem local_embedding_right_conjugate [Finite G]
    {H : Subgroup G} {z : G} (h : InvolutionPointLocalEmbedding H z) (x : G) :
    InvolutionPointLocalEmbedding (rightConjugate H x) (rightConjugateElem z x) := by
  let e := MulAut.conj x⁻¹
  have hker : e.toMonoidHom.ker = ⊥ :=
    (MonoidHom.ker_eq_bot_iff _).mpr e.injective
  have hodd : Odd (Nat.card e.toMonoidHom.ker) := by
    rw [hker, Subgroup.card_bot]
    decide
  have hproper : H.map e.toMonoidHom ≠ ⊤ := by
    intro htop
    apply h.proper
    apply top_unique
    intro a _
    have he : e a ∈ H.map e.toMonoidHom := by rw [htop]; exact Subgroup.mem_top _
    rw [Subgroup.mem_map_equiv] at he
    simpa only [MulEquiv.symm_apply_apply] using he
  simpa only [e, MulEquiv.coe_toMonoidHom, MulAut.conj_apply, inv_inv, rightConjugateElem,
    rightConjugate, Subgroup.conjBy]
    using local_involution_point_embedding_image e.toMonoidHom e.surjective hodd h hproper

theorem central_sylow_right_conjugate [Finite G]
    (S : Sylow 2 G) {z : G} (hzS : z ∈ (S : Subgroup G))
    (hzcenter : (⟨z, hzS⟩ : (S : Subgroup G)) ∈ Subgroup.center (S : Subgroup G))
    (x : G) :
    ∃ T : Sylow 2 G,
      (T : Subgroup G) = rightConjugate (S : Subgroup G) x ∧
      ∃ hzT : rightConjugateElem z x ∈ (T : Subgroup G),
        (⟨rightConjugateElem z x, hzT⟩ : (T : Subgroup G)) ∈
          Subgroup.center (T : Subgroup G) := by
  have hcomm : ∀ s ∈ (S : Subgroup G), Commute z s := by
    intro s hs
    have hc := Subgroup.mem_center_iff.mp hzcenter (⟨s, hs⟩ : (S : Subgroup G))
    exact (congrArg Subtype.val hc).symm
  obtain ⟨T, hT, hzT, hTc⟩ := central_sylow_two_image
    (MulAut.conj x⁻¹).toMonoidHom (MulAut.conj x⁻¹).surjective S hzS hcomm
  have hez : (MulAut.conj x⁻¹).toMonoidHom z = rightConjugateElem z x := by
    simp only [MulEquiv.coe_toMonoidHom, MulAut.conj_apply, inv_inv, rightConjugateElem]
  rw [hez] at hzT hTc
  refine ⟨T, ?_, hzT, Subgroup.mem_center_iff.mpr ?_⟩
  · simpa only [rightConjugate, Subgroup.conjBy] using hT
  intro t
  exact Subtype.ext (hTc t t.property).symm.eq

@[expose] def rebaseRightCoset (H : Subgroup G) (x : G) :
    rightCosetSpace (rightConjugate H x) → rightCosetSpace H :=
  Quotient.map' (fun a : G => x * a) (fun a b hab => by
    rw [QuotientGroup.rightRel_apply] at hab ⊢
    rw [mem_right_conjugate_iff] at hab
    simpa only [mul_inv_rev, mul_assoc] using hab)

theorem rebaseRightCoset_mk (H : Subgroup G) (x a : G) :
    rebaseRightCoset H x (rightCosetMk (rightConjugate H x) a) =
      rightCosetMk H (x * a) := rfl

theorem rebaseRightCoset_injective (H : Subgroup G) (x : G) :
    Function.Injective (rebaseRightCoset H x) := by
  intro a b
  refine Quotient.inductionOn₂ a b fun c d hcd => ?_
  apply Quotient.sound
  change (QuotientGroup.rightRel (rightConjugate H x)) c d
  rw [QuotientGroup.rightRel_apply, mem_right_conjugate_iff]
  have hrel := Quotient.exact hcd
  change (QuotientGroup.rightRel H) (x * c) (x * d) at hrel
  rw [QuotientGroup.rightRel_apply] at hrel
  simpa only [mul_inv_rev, mul_assoc] using hrel

theorem rebaseRightCoset_translate (H : Subgroup G) (x : G)
    (omega : rightCosetSpace (rightConjugate H x)) (g : G) :
    rebaseRightCoset H x (rightCosetTranslate (rightConjugate H x) omega g) =
      rightCosetTranslate H (rebaseRightCoset H x omega) g := by
  refine Quotient.inductionOn' omega fun a => ?_
  change rightCosetMk H (x * (a * g)) = rightCosetMk H ((x * a) * g)
  rw [mul_assoc]

theorem rebaseRightCoset_stabilizer (H : Subgroup G) (x : G)
    (omega : rightCosetSpace (rightConjugate H x)) :
    rightCosetStabilizer (rightConjugate H x) omega =
      rightCosetStabilizer H (rebaseRightCoset H x omega) := by
  ext g
  rw [mem_rightCosetStabilizer_iff, mem_rightCosetStabilizer_iff]
  constructor
  · intro hfix
    rw [← rebaseRightCoset_translate, hfix]
  · intro hfix
    apply rebaseRightCoset_injective H x
    rw [rebaseRightCoset_translate, hfix]

theorem opposite_pair_stabilizer_eq (H : Subgroup G) (x z : G) :
    pairPointStabilizer (rightConjugate H x)
        (rightCosetMk (rightConjugate H x) z) =
      rightCosetStabilizer H (rightCosetMk H x) ⊓
        rightCosetStabilizer H (rightCosetTranslate H (rightCosetMk H x) z) := by
  unfold pairPointStabilizer
  rw [rebaseRightCoset_stabilizer H x, rebaseRightCoset_stabilizer H x,
    rebaseRightCoset_mk, rebaseRightCoset_mk, mul_one, rightCosetTranslate_mk]

theorem distinguished_mem_transported_class (z x : G) :
    z ∈ involutionPointClass (rightConjugateElem z x) := by
  refine ⟨x⁻¹, ?_⟩
  simp only [rightConjugateElem, inv_inv]
  group

theorem distinguished_mem_opposite_pair_fiber (H : Subgroup G) (z x : G) :
    z ∈ rightPairFlipFiber (rightConjugate H x) (rightConjugateElem z x)
      (rightCosetMk (rightConjugate H x) z) := by
  refine ⟨distinguished_mem_transported_class z x, ?_⟩
  rw [rightCosetTranslate_mk, one_mul]

theorem opposite_point_ne_base {H : Subgroup G} {z : G}
    (h : InvolutionPointLocalEmbedding H z) {x : G}
    (hx : rightCosetMk H x ≠ rightCosetMk H 1) :
    rightCosetMk (rightConjugate H x) z ≠ rightCosetMk (rightConjugate H x) 1 := by
  intro heq
  have heq' := congrArg (rebaseRightCoset H x) heq
  rw [rebaseRightCoset_mk, rebaseRightCoset_mk, mul_one] at heq'
  apply hx
  exact (rightCosetTranslate_distinguished_fixed_iff h (rightCosetMk H x)).mp heq'

end CFSG.ProperTwoGeneratedCore.LocalCriterionTripleSylow
