module

public import CFSG.LocalAnalysis.AGLEmbeddingD2.Wilson.NormalizerAction.Sec217Global
public import CFSG.LocalAnalysis.AGLEmbeddingD2.Wilson.NormalizerAction.J3FrameInvariant
public import CFSG.LocalAnalysis.AGLEmbeddingD2.Wilson.NormalizerAction.J3CoverConsumers
public import CFSG.RankThree.Classical2.SLnRootPermutingFixedGroups
public import CFSG.RankThree.PartTwo.Sec13.Item13SetupAt

public section

namespace CFSG.AGLEmbeddingD2.Wilson.NormalizerAction

open Subgroup CFSG CFSG.RankThree CFSG.RankThree.LocalRank CFSG.RankThree.PartTwo
  CFSG.RankThree.PartTwo.Sec21 CFSG.Blueprint

variable {G : Type} [Group G] [Finite G]

theorem Cover217.isQuasisimple_lBar {A E U : Subgroup G} {c : G} {L : Subgroup G}
    (h : Cover217 A E U c L) : IsQuasisimple (lBar L) := by
  have hpairs := mem_lThreeStarPairs_iff.mp h.pair.mem_pair
  have hLc : L ∈ thetaComponentsAt 3 c := (lZeroStarAt_subset A c) hpairs.2.2.1
  obtain ⟨L', hL', hLL'⟩ := hLc
  rw [← hLL']
  exact LocalCores.isQuasisimple_of_mulEquiv (Sec13.thetaQuotEquivSub _ L') hL'.2.2

noncomputable def lBarEquivOfTheta {L : Subgroup G} (hθ : aschbacherSolvableCore 3 L = ⊥) :
    lBar L ≃* ↥L :=
  (QuotientGroup.quotientMulEquivOfEq hθ).trans QuotientGroup.quotientBot

theorem Cover217.quasi_card_center {A E U : Subgroup G} {c : G} {L : Subgroup G}
    (h : Cover217 A E U c L) (hθ : aschbacherSolvableCore 3 L = ⊥) :
    IsQuasisimple ↥L ∧ Nat.card (Subgroup.center ↥L) = 3 := by
  refine ⟨LocalCores.isQuasisimple_of_mulEquiv (lBarEquivOfTheta hθ) h.isQuasisimple_lBar, ?_⟩
  rw [← CFSG.RankThree.Classical2.natCard_center_eq_of_mulEquiv (lBarEquivOfTheta hθ)]
  exact h.cover.1

theorem Cover217.orderOf_c {A E U : Subgroup G} {c : G} {L : Subgroup G}
    (h : Cover217 A E U c L) : orderOf c = 3 := by
  have hpairs := mem_lThreeStarPairs_iff.mp h.pair.mem_pair
  have h3 : c ^ 3 = 1 := h.isElemAbelian_A.2 c h.c_mem_A
  exact orderOf_eq_prime h3 hpairs.2.1

theorem Cover217.center_eq {A E U : Subgroup G} {c : G} {L : Subgroup G}
    (h : Cover217 A E U c L) (hθ : aschbacherSolvableCore 3 L = ⊥) :
    Subgroup.center ↥L = Subgroup.zpowers (⟨c, h.mem⟩ : ↥L) := by
  have hZ3 := h.quasi_card_center hθ |>.2
  have hle : Subgroup.zpowers (⟨c, h.mem⟩ : ↥L) ≤ Subgroup.center ↥L := by
    rw [Subgroup.zpowers_le, Subgroup.mem_center_iff]
    intro x
    exact Subtype.ext (h.c_comm x x.2).symm
  have hord : orderOf (⟨c, h.mem⟩ : ↥L) = 3 := by
    rw [← Subgroup.orderOf_coe]
    exact h.orderOf_c
  symm
  refine Subgroup.eq_of_le_of_card_ge hle ?_
  rw [hZ3, Nat.card_zpowers, hord]

theorem Cover217.map_center {A E U : Subgroup G} {c : G} {L : Subgroup G}
    (h : Cover217 A E U c L) (hθ : aschbacherSolvableCore 3 L = ⊥) :
    (Subgroup.center ↥L).map L.subtype = Subgroup.zpowers c := by
  rw [h.center_eq hθ, MonoidHom.map_zpowers]
  rfl

section Main

set_option linter.unusedSectionVars false

theorem mem_normalizer_subgroupOf_iff {A L : Subgroup G} (hAL : A ≤ L) (y : ↥L) :
    y ∈ Subgroup.normalizer ((A.subgroupOf L : Subgroup ↥L) : Set ↥L) ↔
      (y : G) ∈ Subgroup.normalizer (A : Set G) := by
  constructor
  · intro hy
    rw [Subgroup.mem_normalizer_iff]
    intro z
    constructor
    · intro hz
      have := (Subgroup.mem_normalizer_iff.1 hy ⟨z, hAL hz⟩).1 (Subgroup.mem_subgroupOf.2 hz)
      exact Subgroup.mem_subgroupOf.1 this
    · intro hz
      have hzL : z ∈ L := by
        have h1 : (y : G) * z * (y : G)⁻¹ ∈ L := hAL hz
        have := L.mul_mem (L.mul_mem (L.inv_mem y.2) h1) y.2
        simpa [mul_assoc] using this
      have h2 := (Subgroup.mem_normalizer_iff.1 hy ⟨z, hzL⟩).2 (Subgroup.mem_subgroupOf.2 hz)
      exact Subgroup.mem_subgroupOf.1 h2
  · intro hy
    rw [Subgroup.mem_normalizer_iff]
    intro z
    constructor
    · intro hz
      exact Subgroup.mem_subgroupOf.2 ((Subgroup.mem_normalizer_iff.1 hy z).1
        (Subgroup.mem_subgroupOf.1 hz))
    · intro hz
      exact Subgroup.mem_subgroupOf.2 ((Subgroup.mem_normalizer_iff.1 hy z).2
        (Subgroup.mem_subgroupOf.1 hz))

theorem Cover217.invariant_subgroups {A E U : Subgroup G} {c : G} {L : Subgroup G}
    (h : Cover217 A E U c L) (hθ : aschbacherSolvableCore 3 L = ⊥) (hAL : A ≤ L) :
    ∃ F₁ : Subgroup G, F₁ ≤ A ∧ Nat.card F₁ = 27 ∧
      (∀ y ∈ L ⊓ Subgroup.normalizer (A : Set G), F₁.map (MulAut.conj y).toMonoidHom = F₁) ∧
      ∀ S : Subgroup G, S ≤ A →
        (∀ x ∈ L ⊓ Subgroup.normalizer (A : Set G), S.map (MulAut.conj x).toMonoidHom = S) →
        S = ⊥ ∨ S = Subgroup.zpowers c ∨ S = F₁ ∨ S = A := by
  obtain ⟨hq, hZ3⟩ := h.quasi_card_center hθ
  obtain ⟨e⟩ := h.quot
  set F : Subgroup ↥L := A.subgroupOf L with hF
  have hFmap : F.map L.subtype = A := Subgroup.map_subgroupOf_eq_of_le hAL
  have hF81 : Nat.card F = 81 := by
    rw [hF, Nat.card_congr (Subgroup.subgroupOfEquivOfLe hAL).toEquiv, h.card]
    norm_num
  have hZF : Subgroup.center ↥L ≤ F := by
    rw [h.center_eq hθ, Subgroup.zpowers_le]
    exact Subgroup.mem_subgroupOf.2 h.c_mem_A
  have hab := h.isElemAbelian_A
  haveI : IsMulCommutative A := hab.1
  have hFel : CFSG.IsElementaryAbelian 3 (F.map (QuotientGroup.mk' (Subgroup.center ↥L))) := by
    have hFE : CFSG.IsElementaryAbelian 3 F := by
      rw [← isElemAbelian_iff_isElementaryAbelian]
      refine ⟨⟨⟨fun a b => ?_⟩⟩, fun x hx => ?_⟩
      · apply Subtype.ext
        apply Subtype.ext
        have hc := mul_comm' (⟨((a : ↥L) : G), Subgroup.mem_subgroupOf.1 a.2⟩ : A)
          ⟨((b : ↥L) : G), Subgroup.mem_subgroupOf.1 b.2⟩
        have := congrArg Subtype.val hc
        exact this
      · exact Subtype.ext (hab.2 (x : G) (Subgroup.mem_subgroupOf.1 hx))
    exact CFSG.RankThree.Asc83Table.IsElementaryAbelian.map_hom _ hFE
  obtain ⟨F₁, hZF₁, hF₁F, hF₁27, hF₁inv, hall⟩ :=
    frame_invariant_subgroups gammaWordFacts_holds hq hZ3 e hFel hZF hF81
  have hnorm : ∀ y ∈ Subgroup.normalizer (F : Set ↥L),
      (y : G) ∈ L ⊓ Subgroup.normalizer (A : Set G) := fun y hy =>
    ⟨y.2, (mem_normalizer_subgroupOf_iff hAL y).1 hy⟩
  refine ⟨F₁.map L.subtype, ?_, ?_, ?_, ?_⟩
  · rw [← hFmap]; exact Subgroup.map_mono hF₁F
  · rw [Subgroup.card_map_of_injective L.subtype_injective, hF₁27]
  · intro y hy
    have hy' : (⟨y, hy.1⟩ : ↥L) ∈ Subgroup.normalizer (F : Set ↥L) :=
      (mem_normalizer_subgroupOf_iff hAL ⟨y, hy.1⟩).2 hy.2
    have hle : (F₁.map L.subtype).map (MulAut.conj y).toMonoidHom ≤ F₁.map L.subtype := by
      rintro _ ⟨_, ⟨f, hf, rfl⟩, rfl⟩
      exact ⟨⟨y, hy.1⟩ * f * ⟨y, hy.1⟩⁻¹, hF₁inv _ hy' f hf, rfl⟩
    refine Subgroup.eq_of_le_of_card_ge hle ?_
    rw [Subgroup.card_map_of_injective (f := (MulAut.conj y).toMonoidHom)
      (MulAut.conj y).injective]
  · intro S hSA hinv
    have hSL : S ≤ L := hSA.trans hAL
    have hS' := hall (S.subgroupOf L) (by
        intro x hx
        exact Subgroup.mem_subgroupOf.2 (hSA (Subgroup.mem_subgroupOf.1 hx))) (by
        intro y hy s hs
        have h1 : (s : G) ∈ S := Subgroup.mem_subgroupOf.1 hs
        have h2 : (y : G) * s * (y : G)⁻¹ ∈ S.map (MulAut.conj (y : G)).toMonoidHom :=
          ⟨s, h1, rfl⟩
        rw [hinv (y : G) (hnorm y hy)] at h2
        exact Subgroup.mem_subgroupOf.2 h2)
    have hSeq : (S.subgroupOf L).map L.subtype = S := Subgroup.map_subgroupOf_eq_of_le hSL
    rcases hS' with h0 | h0 | h0 | h0
    · left; rw [← hSeq, h0, Subgroup.map_bot]
    · right; left; rw [← hSeq, h0, h.map_center hθ]
    · right; right; left; rw [← hSeq, h0]
    · right; right; right; rw [← hSeq, h0, hFmap]

end Main

end CFSG.AGLEmbeddingD2.Wilson.NormalizerAction
