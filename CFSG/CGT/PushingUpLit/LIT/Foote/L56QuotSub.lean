module

public import CFSG.CGT.PushingUpLit.LIT.Foote.L56Quot
public import CFSG.CGT.PushingUpLit.LIT.Foote.L56Comm
public import CFSG.CGT.PushingUpLit.LIT.Foote.Top

public section

namespace CFSG.CGT.PushingUpLit.LIT.Foote

open CFSG CFSG.ABGLocalTools CFSG.ComponentClassification.AschbacherTightEmbedding
open CFSG.ComponentClassification.AschbacherTheorem3 (Frame)
open scoped commutatorElement

variable {G : Type} [Group G] [Finite G]

omit [Finite G] in
theorem rightConjugate_subgroupOf' (A H : Subgroup G) (y : ↥H) :
    rightConjugate (A.subgroupOf H) y = (rightConjugate A (y : G)).subgroupOf H := by
  ext z
  rw [mem_rightConjugate_iff, Subgroup.mem_subgroupOf, Subgroup.mem_subgroupOf,
    mem_rightConjugate_iff]
  rfl

omit [Finite G] in
theorem subgroupOf_mono' {H A B : Subgroup G} (h : A ≤ B) : A.subgroupOf H ≤ B.subgroupOf H :=
  fun _ hx => Subgroup.mem_subgroupOf.2 (h (Subgroup.mem_subgroupOf.1 hx))

theorem commutator_le_of_weakly_closed_sub {H J T S O W : Subgroup G} (hJH : J ≤ H)
    (hTH : T ≤ H) (hSH : S ≤ H) (hOJ : O ≤ J) (hOS : O ≤ S)
    (hON : H ≤ Subgroup.normalizer (O : Set G)) (hTN : T ≤ Subgroup.normalizer (J : Set G))
    (hTJ : T ⊓ J = ⊥) (hT2 : IsPGroup 2 T) (htop : J ⊔ T = H) (hS : ABGLocalTools.IsSylowOf 2 S H)
    (hTS : T ≤ S) (hTW : T ≤ W) (hWS : W ≤ S) (hWTO : W ≤ T ⊔ O)
    (hwc : ∀ y ∈ J, rightConjugate W y ≤ S → rightConjugate W y = W)
    [(O.subgroupOf H).Normal]
    (hq : CFSG.IsQuasisimple ↥((J.subgroupOf H).map (QuotientGroup.mk' (O.subgroupOf H)))) :
    ⁅J, T⁆ ≤ O := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hOH : O ≤ H := hOJ.trans hJH
  have hWH : W ≤ H := hWS.trans hSH
  have hF : Frame (J.subgroupOf H) (T.subgroupOf H) :=
    { le_normalizer := by
        intro t ht
        rw [Subgroup.mem_normalizer_iff]
        intro h
        rw [Subgroup.mem_subgroupOf, Subgroup.mem_subgroupOf]
        exact Subgroup.mem_normalizer_iff.1 (hTN (Subgroup.mem_subgroupOf.1 ht)) (h : G)
      inf_eq_bot := by
        rw [eq_bot_iff]
        rintro x ⟨hxT, hxJ⟩
        have hx : (x : G) ∈ T ⊓ J := ⟨Subgroup.mem_subgroupOf.1 hxT, Subgroup.mem_subgroupOf.1 hxJ⟩
        rw [hTJ, Subgroup.mem_bot] at hx
        exact Subgroup.mem_bot.2 (Subtype.ext hx)
      isPGroup := hT2.comap_subtype }
  have htop' : J.subgroupOf H ⊔ T.subgroupOf H = ⊤ := by
    rw [← Subgroup.subgroupOf_sup hJH hTH, htop, Subgroup.subgroupOf_self]
  have hS' : ABGLocalTools.IsSylowOf 2 (S.subgroupOf H) (J.subgroupOf H ⊔ T.subgroupOf H) := by
    rw [htop', isSylowOf_iff]
    obtain ⟨-, hS2, hdvd⟩ := isSylowOf_iff.1 hS
    refine ⟨le_top, hS2.comap_subtype, ?_⟩
    rw [Subgroup.relIndex_top_right]
    exact hdvd
  have hwc' : ∀ y ∈ J.subgroupOf H, rightConjugate (W.subgroupOf H) y ≤ S.subgroupOf H →
      rightConjugate (W.subgroupOf H) y = W.subgroupOf H := by
    intro y hy hle
    have hyJ : (y : G) ∈ J := Subgroup.mem_subgroupOf.1 hy
    rw [rightConjugate_subgroupOf'] at hle ⊢
    have h1 : rightConjugate W (y : G) ≤ S := by
      intro z hz
      have hzH : z ∈ H := by
        have hz' := (mem_rightConjugate_iff W (y : G) z).1 hz
        have e : (y : G)⁻¹ * ((y : G) * z * (y : G)⁻¹) * (y : G) = z := by group
        have := H.mul_mem (H.mul_mem (H.inv_mem y.2) (hWH hz')) y.2
        rwa [e] at this
      exact Subgroup.mem_subgroupOf.1
        (hle (show (⟨z, hzH⟩ : ↥H) ∈ (rightConjugate W (y : G)).subgroupOf H from hz))
    rw [hwc (y : G) hyJ h1]
  have hWTO' : W.subgroupOf H ≤ T.subgroupOf H ⊔ O.subgroupOf H := by
    intro x hx
    obtain ⟨t, ht, o, ho, hto⟩ :=
      exists_mul_of_mem_sup (hTH.trans hON) (hWTO (Subgroup.mem_subgroupOf.1 hx))
    have e : x = (⟨t, hTH ht⟩ : ↥H) * ⟨o, hOH ho⟩ := Subtype.ext hto.symm
    rw [e]
    exact Subgroup.mul_mem_sup ht ho
  have key := commutator_le_of_weakly_closed (J := J.subgroupOf H) (T := T.subgroupOf H)
    (S := S.subgroupOf H) (O := O.subgroupOf H) (W := W.subgroupOf H) hF htop' hS'
    (subgroupOf_mono' hTS) (subgroupOf_mono' hOJ) (subgroupOf_mono' hOS)
    (subgroupOf_mono' hTW) (subgroupOf_mono' hWS) hWTO' hwc' hq
  rw [← commutator_subgroupOf hJH hTH] at key
  intro x hx
  have hxH : x ∈ H := commutator_le_of_le hJH hTH hx
  exact Subgroup.mem_subgroupOf.1 (key (show (⟨x, hxH⟩ : ↥H) ∈ (⁅J, T⁆).subgroupOf H from hx))

theorem isQuasisimple_image {H J : Subgroup G} (hJ : QBlock J) (hJH : J ≤ H)
    [((oTwoIn J).subgroupOf H).Normal] :
    CFSG.IsQuasisimple ↥((J.subgroupOf H).map
      (QuotientGroup.mk' ((oTwoIn J).subgroupOf H))) := by
  let ψ : ↥J →* ↥H ⧸ (oTwoIn J).subgroupOf H :=
    (QuotientGroup.mk' ((oTwoIn J).subgroupOf H)).comp (Subgroup.inclusion hJH)
  have hrange : ψ.range = (J.subgroupOf H).map (QuotientGroup.mk' ((oTwoIn J).subgroupOf H)) := by
    ext z
    constructor
    · rintro ⟨j, rfl⟩
      exact ⟨Subgroup.inclusion hJH j, j.2, rfl⟩
    · rintro ⟨y, hy, rfl⟩
      exact ⟨⟨(y : G), hy⟩, rfl⟩
  have hker : ψ.ker = pCore 2 ↥J := by
    ext j
    rw [MonoidHom.mem_ker]
    show QuotientGroup.mk' _ (Subgroup.inclusion hJH j) = 1 ↔ j ∈ pCore 2 ↥J
    rw [QuotientGroup.mk'_apply, QuotientGroup.eq_one_iff, Subgroup.mem_subgroupOf]
    exact QBlock.mem_oTwoIn_iff j.2
  let eqv : (↥J ⧸ pCore 2 ↥J) ≃*
      ↥((J.subgroupOf H).map (QuotientGroup.mk' ((oTwoIn J).subgroupOf H))) :=
    ((QuotientGroup.quotientMulEquivOfEq hker.symm).trans
      (QuotientGroup.quotientKerEquivRange ψ)).trans (MulEquiv.subgroupCongr hrange)
  refine LocalCores.isQuasisimple_of_surjective hJ.quasisimple eqv.toMonoidHom eqv.surjective ?_
  rw [(MonoidHom.ker_eq_bot_iff _).2 eqv.injective]
  exact bot_le

end CFSG.CGT.PushingUpLit.LIT.Foote
