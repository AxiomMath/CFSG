module

public import CFSG.LocalAnalysis.ComponentClassification.AschbacherTheorem3NineOdd

public section

namespace CFSG.ComponentClassification.AschbacherTheorem3

open CFSG.ComponentClassification.AschbacherTightEmbedding
open CFSG.ABGLocalTools
open CFSG.Open

variable {X : Type} [Group X] [Finite X]

omit [Finite X] in
theorem isSubnormal_subgroupOf {A G : Subgroup X} (h : IsSubnormal A G) :
    A ≤ G ∧ IsSubnormal (A.subgroupOf G) ⊤ :=
  ⟨h.le, CFSG.Open.IsSubnormal.of_mathlib h.subgroupOf⟩

theorem le_normalizer_of_isComponentOf {G A : Subgroup X} (hG : Layer.subgroup G = ⊤)
    (hA : IsComponentOf A G) : G ≤ Subgroup.normalizer (A : Set X) := by
  obtain ⟨hAG, hsub, hq⟩ := hA
  have hcomp : IsComponentOf (A.subgroupOf G) ⊤ :=
    ⟨le_top, (isSubnormal_subgroupOf hsub).2,
      Components.quasisimple_of_equiv (Subgroup.subgroupOfEquivOfLe hAG) hq⟩
  have hn := Layer.normal_component hcomp
  rw [hG] at hn
  have hn' : (A.subgroupOf G).Normal :=
    Subgroup.normalizer_eq_top_iff.mp
      (top_le_iff.mp ((Subgroup.normal_subgroupOf_iff_le_normalizer le_top).mp hn))
  exact (Subgroup.normal_subgroupOf_iff_le_normalizer hAG).mp hn'

theorem pRank_le_of_isSylowOf {T Q : Subgroup X} (h : IsSylowOf 2 T Q) :
    pRank 2 Q ≤ pRank 2 T := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  obtain ⟨E, hEQ, hE, hcard⟩ := CFSG.SectionRank.exists_pRank one_lt_two Q
  have hE2 : IsPGroup 2 E := fun x => ⟨1, Subtype.ext (by
    rw [Subgroup.coe_pow, pow_one, Subgroup.coe_one]; exact hE.2 _ x.2)⟩
  obtain ⟨c, -, hle⟩ := exists_rightConjugate_le_of_isSylowOf h hE2 hEQ
  refine CFSG.SectionRank.le_pRank one_lt_two hle
    (CFSG.SectionRank.isElemAbelian_map hE (MulAut.conj c⁻¹).toMonoidHom) ?_
  rw [rightConjugate_card, hcard]

theorem pre49_subgroupOf {A T S Q H : Subgroup X} (hS : SylowFrame A T S)
    (h43 : Hyp43 A T Q H) (hq : IsQuasisimple A) (hm : 1 < pRank 2 T) (hAH : ¬ A ≤ H)
    (hrank : pRank 2 (centerOf A ⊓ Subgroup.centralizer (T : Set X)) ≤ pRank 2 T)
    (hnone : ∀ a ∈ A, (∃ k : ℕ, a ^ (2 ^ k) = 1) → a ∈ Subgroup.centralizer (T : Set X) →
      a ∈ centerOf A) :
    Pre49 (A.subgroupOf (A ⊔ T)) (T.subgroupOf (A ⊔ T)) (S.subgroupOf (A ⊔ T))
      (Q.subgroupOf (A ⊔ T)) (H.subgroupOf (A ⊔ T)) := by
  set L := A ⊔ T
  have hAL : A ≤ L := le_sup_left
  have hTL : T ≤ L := le_sup_right
  have hTmap : (T.subgroupOf L).map L.subtype = T := by
    rw [Subgroup.subgroupOf_map_subtype, inf_eq_left.mpr hTL]
  have hT := pRank_map_eq L.subtype L.subtype_injective (T.subgroupOf L)
  rw [hTmap] at hT
  refine
    { sylowFrame := hS.subgroupOf
      hyp43 := h43.subgroupOf
      top := sup_subgroupOf_eq_top A T
      quasisimple := Components.quasisimple_of_equiv (Subgroup.subgroupOfEquivOfLe hAL) hq
      pRank_lt := hT ▸ hm
      not_le := fun hle => hAH fun a ha =>
        hle (show (⟨a, hAL ha⟩ : L) ∈ A.subgroupOf L from ha)
      rank := ?_
      none := ?_ }
  · have h1 := pRank_map_eq L.subtype L.subtype_injective (centerOf (A.subgroupOf L) ⊓
      Subgroup.centralizer ((T.subgroupOf L : Subgroup L) : Set L))
    rw [← h1, ← hT]
    refine (CFSG.SectionRank.pRank_mono one_lt_two ?_).trans hrank
    rintro _ ⟨x, ⟨⟨hxA, hxCA⟩, hxCT⟩, rfl⟩
    refine ⟨⟨hxA, Subgroup.mem_centralizer_iff.mpr fun a ha => ?_⟩,
      Subgroup.mem_centralizer_iff.mpr fun t ht => ?_⟩
    · exact congrArg Subtype.val (Subgroup.mem_centralizer_iff.mp hxCA ⟨a, hAL ha⟩ ha)
    · exact congrArg Subtype.val (Subgroup.mem_centralizer_iff.mp hxCT ⟨t, hTL ht⟩ ht)
  · rintro a ha ⟨k, hk⟩ haC
    have hC : (a : X) ∈ Subgroup.centralizer (T : Set X) :=
      Subgroup.mem_centralizer_iff.mpr fun t ht =>
        congrArg Subtype.val (Subgroup.mem_centralizer_iff.mp haC ⟨t, hTL ht⟩ ht)
    have hZ := hnone a ha ⟨k, congrArg Subtype.val hk⟩ hC
    refine ⟨ha, Subgroup.mem_centralizer_iff.mpr fun b hb => Subtype.ext ?_⟩
    exact Subgroup.mem_centralizer_iff.mp hZ.2 b hb

theorem lemma_4_9_of_theorem_4_8 (h48 : Theorem48Statement) : Lemma49Statement := by
  intro X _ _ G T S Q H A hS h43 _ _ hlayer hcomp hTA hmQ hAH hrank
  by_contra hcon
  have hnone : ∀ a ∈ A, (∃ k : ℕ, a ^ (2 ^ k) = 1) → a ∈ Subgroup.centralizer (T : Set X) →
      a ∈ centerOf A := fun a ha h2 hC => by
    by_contra hZ
    exact hcon ⟨a, ha, h2, hC, hZ⟩
  have hAG : A ≤ G := hcomp.1
  have hGA : G ≤ Subgroup.normalizer (A : Set X) := le_normalizer_of_isComponentOf hlayer hcomp
  have hS' := hS.restrict hAG (sup_le hGA hTA)
  have h43' := h43.restrict hAG
  have hmT : 1 < pRank 2 T := hmQ.trans_le (pRank_le_of_isSylowOf h43.sylow)
  have hAH' : ¬ A ≤ H ⊓ (A ⊔ T) := fun h => hAH (h.trans inf_le_left)
  exact (pre49_subgroupOf hS' h43' hcomp.2.2 hmT hAH' hrank hnone).false h48

end CFSG.ComponentClassification.AschbacherTheorem3
