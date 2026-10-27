module

public import CFSG.LocalAnalysis.OddStandard.SwapPartner.StrayOuter
public import CFSG.LocalAnalysis.OddStandard.SwapPartner.StrayQuot
public import CFSG.Foundations.QuasisimpleMulEquiv

public section

namespace CFSG.OddStandard.AltStdSec.SwapPartner

open Subgroup

theorem four_le_card_inf_centralizer_of_normal (hF : DihedralOuterInvolutionFact) {Y : Type}
    [Group Y] [Finite Y] {J : Subgroup Y} [J.Normal] (hJ : CFSG.IsQuasisimple ↥J) {t : Y}
    (ht : t ^ 2 = 1) : 4 ≤ Nat.card ↥(J ⊓ centralizer ({t} : Set Y)) := by
  have hsimple : IsSimpleGroup ↥(J.map (QuotientGroup.mk' (strayCenterIn J))) :=
    isSimpleGroup_map_strayCenterIn hJ
  have hnab : ∃ x y : ↥(J.map (QuotientGroup.mk' (strayCenterIn J))), x * y ≠ y * x :=
    exists_noncomm_map_strayCenterIn hJ
  have hLn : (J.map (QuotientGroup.mk' (strayCenterIn J))).Normal := normal_map_strayCenterIn J
  have ha : (QuotientGroup.mk t : Y ⧸ strayCenterIn J) ^ 2 = 1 := by
    have h2 : (QuotientGroup.mk' (strayCenterIn J) t) ^ 2 = 1 := by
      calc (QuotientGroup.mk' (strayCenterIn J) t) ^ 2
          = QuotientGroup.mk' (strayCenterIn J) (t ^ 2) := (map_pow _ t 2).symm
        _ = QuotientGroup.mk' (strayCenterIn J) 1 := by rw [ht]
        _ = 1 := map_one _
    simpa using h2
  have haN : (QuotientGroup.mk t : Y ⧸ strayCenterIn J) ∈
      normalizer ((J.map (QuotientGroup.mk' (strayCenterIn J))) : Set (Y ⧸ strayCenterIn J)) := by
    rw [Subgroup.normalizer_eq_top_iff.mpr hLn]
    trivial
  exact le_trans
    (four_le_card_inf_centralizer_of_simple hF hsimple hnab ha haN)
    (card_inf_centralizer_map_le J t)

theorem four_le_card_inf_centralizer_of_normalizer (hF : DihedralOuterInvolutionFact) {X : Type}
    [Group X] [Finite X] {J : Subgroup X} (hJ : CFSG.IsQuasisimple ↥J) {t : X} (ht : t ^ 2 = 1)
    (htN : t ∈ normalizer (J : Set X)) : 4 ≤ Nat.card ↥(J ⊓ centralizer ({t} : Set X)) := by
  let R : Subgroup X := normalizer (J : Set X)
  let t' : R := ⟨t, htN⟩
  have hJ' : CFSG.IsQuasisimple ↥(J.subgroupOf R) :=
    CFSG.IsQuasisimple.of_mulEquiv
      (Subgroup.subgroupOfEquivOfLe (Subgroup.le_normalizer (H := J))) hJ
  have ht' : t' ^ 2 = 1 := by
    apply Subtype.ext
    simpa [t'] using ht
  have h1 := four_le_card_inf_centralizer_of_normal hF (Y := R) (J := J.subgroupOf R) hJ' ht'
  have hset : (J.subgroupOf R) ⊓ centralizer ({t'} : Set R) =
      (J ⊓ centralizer ({t} : Set X)).subgroupOf R := by
    ext y
    simp only [Subgroup.mem_inf, Subgroup.mem_subgroupOf,
      Subgroup.mem_centralizer_singleton_iff]
    constructor
    · rintro ⟨hyJ, hyC⟩
      exact ⟨hyJ, congrArg Subtype.val hyC⟩
    · rintro ⟨hyJ, hyC⟩
      exact ⟨hyJ, Subtype.ext hyC⟩
  have hcard : Nat.card ↥((J.subgroupOf R) ⊓ centralizer ({t'} : Set R)) =
      Nat.card ↥(J ⊓ centralizer ({t} : Set X)) := by
    rw [hset]
    exact Nat.card_congr (Subgroup.subgroupOfEquivOfLe
      (inf_le_left.trans (Subgroup.le_normalizer (H := J)))).toEquiv
  rw [hcard] at h1
  exact h1

end CFSG.OddStandard.AltStdSec.SwapPartner
