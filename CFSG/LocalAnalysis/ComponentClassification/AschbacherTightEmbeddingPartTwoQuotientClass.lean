module

public import CFSG.LocalAnalysis.ComponentClassification.AschbacherTightEmbeddingPartTwoOddKernelRank
public import CFSG.LocalAnalysis.ComponentClassification.AschbacherTightEmbeddingPartTwoLocalHypotheses

public section

namespace CFSG.ComponentClassification.AschbacherTightEmbedding

open CFSG.Open CFSG.ShultStronglyClosedTI CFSG.BenderSuzuki
open CFSG.BenderSuzuki.PFAppendixIII

variable {G : Type*} [Group G] [Finite G]

theorem normal_hull_point_class_mem_iff (Q : Subgroup G)
    (hodd : OddNormalizerOverlaps Q) (hnormal : ¬ Q.Normal)
    (z : G) (hzQ : z ∈ Q) (hz : orderOf z = 2)
    (w : Subgroup.normalClosure (Q : Set G)) :
    let J := Subgroup.normalClosure (Q : Set G)
    let zJ : J := ⟨z, Subgroup.le_normalClosure hzQ⟩
    w ∈ involutionPointClass zJ ↔ (w : G) ∈ involutionPointClass z := by
  let J := Subgroup.normalClosure (Q : Set G)
  let zJ : J := ⟨z, Subgroup.le_normalClosure hzQ⟩
  have himage := normal_hull_point_class_image Q hodd hnormal z hzQ hz
  change w ∈ involutionPointClass zJ ↔ (w : G) ∈ involutionPointClass z
  rw [← himage]
  constructor
  · intro hw
    exact ⟨w, hw, rfl⟩
  · rintro ⟨v, hv, heq⟩
    exact (J.subtype_injective heq) ▸ hv

theorem normal_hull_odd_quotient_point_class_mem_iff (Q : Subgroup G)
    (hodd : OddNormalizerOverlaps Q) (hnormal : ¬ Q.Normal)
    (z : G) (hzQ : z ∈ Q) (hz : orderOf z = 2)
    (w : Subgroup.normalClosure (Q : Set G)) (hw : orderOf w = 2) :
    let J := Subgroup.normalClosure (Q : Set G)
    let zJ : J := ⟨z, Subgroup.le_normalClosure hzQ⟩
    let q := QuotientGroup.mk' (oddCore J)
    q w ∈ involutionPointClass (q zJ) ↔ (w : G) ∈ involutionPointClass z := by
  let J := Subgroup.normalClosure (Q : Set G)
  let zJ : J := ⟨z, Subgroup.le_normalClosure hzQ⟩
  let q := QuotientGroup.mk' (oddCore J)
  have hzJ : orderOf zJ = 2 := (Subgroup.orderOf_coe zJ).symm.trans hz
  have hzI : IsInvolution zJ :=
    ⟨(orderOf_eq_prime_iff.mp hzJ).2, (orderOf_eq_prime_iff.mp hzJ).1⟩
  have hwI : IsInvolution w :=
    ⟨(orderOf_eq_prime_iff.mp hw).2, (orderOf_eq_prime_iff.mp hw).1⟩
  exact (CFSG.ProperTwoGeneratedCore.involution_point_class_image_iff q
    (normal_hull_odd_quotient_surjective Q) (normal_hull_odd_quotient_ker_odd Q)
    hzI hwI).trans (normal_hull_point_class_mem_iff Q hodd hnormal z hzQ hz w)

theorem normal_hull_odd_quotient_involution_centralizer_map (Q : Subgroup G)
    (z : Subgroup.normalClosure (Q : Set G)) (hz : orderOf z = 2) :
    let J := Subgroup.normalClosure (Q : Set G)
    let q := QuotientGroup.mk' (oddCore J)
    (Subgroup.centralizer ({z} : Set J)).map q =
      Subgroup.centralizer ({q z} : Set (J ⧸ oddCore J)) := by
  have hzI : IsInvolution z :=
    ⟨(orderOf_eq_prime_iff.mp hz).2, (orderOf_eq_prime_iff.mp hz).1⟩
  exact CFSG.ProperTwoGeneratedCore.involution_centralizer_image
    (QuotientGroup.mk' (oddCore (Subgroup.normalClosure (Q : Set G))))
    (normal_hull_odd_quotient_surjective Q) (normal_hull_odd_quotient_ker_odd Q) hzI

theorem normal_hull_odd_quotient_commuting_class_lift (Q : Subgroup G)
    (hodd : OddNormalizerOverlaps Q) (hnormal : ¬ Q.Normal)
    (z : G) (hzQ : z ∈ Q) (hz : orderOf z = 2) :
    let J := Subgroup.normalClosure (Q : Set G)
    let zJ : J := ⟨z, Subgroup.le_normalClosure hzQ⟩
    let q := QuotientGroup.mk' (oddCore J)
    ∀ t ∈ involutionPointClass (q zJ), q zJ ≠ t → Commute (q zJ) t →
      ∃ w : J, orderOf w = 2 ∧ q w = t ∧ (w : G) ∈ Q ∧
        (w : G) ∈ involutionPointClass z ∧ z ≠ (w : G) ∧ Commute z (w : G) := by
  dsimp only
  let J := Subgroup.normalClosure (Q : Set G)
  let zJ : J := ⟨z, Subgroup.le_normalClosure hzQ⟩
  let q := QuotientGroup.mk' (oddCore J)
  have hzJ : orderOf zJ = 2 := (Subgroup.orderOf_coe zJ).symm.trans hz
  have hzI : IsInvolution zJ :=
    ⟨(orderOf_eq_prime_iff.mp hzJ).2, (orderOf_eq_prime_iff.mp hzJ).1⟩
  have hqzI := CFSG.ProperTwoGeneratedCore.involution_image_of_odd_kernel q
    (normal_hull_odd_quotient_ker_odd Q) hzI
  intro t ht hne hcomm
  have htorder : orderOf t = 2 := order_two_of_mem_pointClass
    (orderOf_eq_prime hqzI.sq_eq_one hqzI.ne_one) ht
  have htI : IsInvolution t :=
    ⟨(orderOf_eq_prime_iff.mp htorder).2, (orderOf_eq_prime_iff.mp htorder).1⟩
  obtain ⟨w, hwI, hqw, hwcomm⟩ :=
    CFSG.ProperTwoGeneratedCore.commuting_involution_lift_of_odd_kernel q
      (normal_hull_odd_quotient_surjective Q) (normal_hull_odd_quotient_ker_odd Q)
      hzI htI hcomm.symm
  have hw : orderOf w = 2 := orderOf_eq_prime hwI.sq_eq_one hwI.ne_one
  have hwclass : (w : G) ∈ involutionPointClass z :=
    (normal_hull_odd_quotient_point_class_mem_iff Q hodd hnormal z hzQ hz w hw).mp
      (hqw.symm ▸ ht)
  have hzw : z ≠ (w : G) := by
    intro heq
    exact hne ((congrArg q (Subtype.ext heq : zJ = w)).trans hqw)
  have hcommG : Commute z (w : G) := hwcomm.symm.map J.subtype
  have hprod := (point_class_commuting_product_mem_Q Q hodd z hzQ hz
    w hwclass hzw hcommG).1
  have hwQ : (w : G) ∈ Q := by
    have hmem := Q.mul_mem (Q.inv_mem hzQ) hprod
    simpa only [inv_mul_cancel_left] using hmem
  exact ⟨w, hw, hqw, hwQ, hwclass, hzw, hcommG⟩

theorem normal_hull_odd_quotient_commuting_product_centralizer_le (Q : Subgroup G)
    (hodd : OddNormalizerOverlaps Q) (hnormal : ¬ Q.Normal)
    (z : G) (hzQ : z ∈ Q) (hz : orderOf z = 2) :
    let J := Subgroup.normalClosure (Q : Set G)
    let zJ : J := ⟨z, Subgroup.le_normalClosure hzQ⟩
    let q := QuotientGroup.mk' (oddCore J)
    ∀ t ∈ involutionPointClass (q zJ), q zJ ≠ t → Commute (q zJ) t →
      Subgroup.centralizer ({q zJ * t} : Set (J ⧸ oddCore J)) ≤
        ((Subgroup.normalizer (Q : Set G)).subgroupOf J).map q := by
  dsimp only
  let J := Subgroup.normalClosure (Q : Set G)
  let zJ : J := ⟨z, Subgroup.le_normalClosure hzQ⟩
  let q := QuotientGroup.mk' (oddCore J)
  intro t ht hne hcomm
  obtain ⟨w, _, hqw, _, hwclass, hzw, hcommG⟩ :=
    normal_hull_odd_quotient_commuting_class_lift Q hodd hnormal z hzQ hz t ht hne hcomm
  have hprod : orderOf (zJ * w) = 2 := by
    rw [← Subgroup.orderOf_coe]
    exact (point_class_commuting_product_mem_Q Q hodd z hzQ hz
      w hwclass hzw hcommG).2
  have hcent : Subgroup.centralizer ({zJ * w} : Set J) ≤
      (Subgroup.normalizer (Q : Set G)).subgroupOf J := by
    intro a ha
    apply point_class_commuting_product_centralizer_le Q hodd z hzQ hz
      w hwclass hzw hcommG
    exact Subgroup.mem_centralizer_singleton_iff.mpr
      ((show Commute a (zJ * w) from
        Subgroup.mem_centralizer_singleton_iff.mp ha).map J.subtype)
  rw [← hqw, ← map_mul, ← normal_hull_odd_quotient_involution_centralizer_map Q
    (zJ * w) hprod]
  exact Subgroup.map_mono hcent

theorem theorem_three_three_normal_hull_odd_quotient_hypotheses (Q : Subgroup G)
    (htight : TightlyEmbedded Q) (hodd : OddNormalizerOverlaps Q)
    (hnormal : ¬ Q.Normal) (hrank : 2 ≤ twoRank Q) :
    let J := Subgroup.normalClosure (Q : Set G)
    let q := QuotientGroup.mk' (oddCore J)
    let H := Subgroup.normalizer ((Q.subgroupOf J).map q : Set (J ⧸ oddCore J))
    ∃ (P : Sylow 2 (J ⧸ oddCore J)) (z : J),
      H ≠ ⊤ ∧ (z : G) ∈ Q ∧ orderOf z = 2 ∧
      q z ∈ (Subgroup.center (P : Subgroup (J ⧸ oddCore J))).map
        (P : Subgroup (J ⧸ oddCore J)).subtype ∧
      (∀ g : J ⧸ oddCore J, q z ∈ rightConjugate H g ↔ g ∈ H) ∧
      (∀ t ∈ involutionPointClass (q z), q z ≠ t → Commute (q z) t →
        ∀ g : J ⧸ oddCore J, g⁻¹ * (q z * t) * g ∈ H ↔ g ∈ H) ∧
      (∀ t ∈ involutionPointClass (q z), q z ≠ t → Commute (q z) t →
        Subgroup.centralizer ({q z * t} : Set (J ⧸ oddCore J)) ≤ H) ∧
      Group.IsPerfect (involutionPointHull (q z)) ∧
      (∀ w : J, orderOf w = 2 →
        (q w ∈ involutionPointClass (q z) ↔ (w : G) ∈ involutionPointClass (z : G))) := by
  dsimp only
  let J := Subgroup.normalClosure (Q : Set G)
  let q := QuotientGroup.mk' (oddCore J)
  let R := (Q.subgroupOf J).map q
  obtain ⟨P, y, hproper, hyR, hy, hycenter, hunique, hproduct, hcentralizer⟩ :=
    theorem_three_three_original_hypotheses R
      (normal_hull_odd_quotient_Q_tightly_embedded Q htight hodd hrank)
      (normal_hull_odd_quotient_Q_odd_normalizer_overlaps Q htight hodd hrank)
      (normal_hull_odd_quotient_Q_nonnormal Q htight hodd hrank hnormal)
  have hyI : IsInvolution y :=
    ⟨(orderOf_eq_prime_iff.mp hy).2, (orderOf_eq_prime_iff.mp hy).1⟩
  obtain ⟨z, hzQ, hzI, hqz⟩ :=
    CFSG.ProperTwoGeneratedCore.involution_lift_in_subgroup_of_odd_kernel q
      (normal_hull_odd_quotient_ker_odd Q) (Q.subgroupOf J) hyI hyR
  have hz : orderOf z = 2 := orderOf_eq_prime hzI.sq_eq_one hzI.ne_one
  have hzG : orderOf (z : G) = 2 := (Subgroup.orderOf_coe z).trans hz
  refine ⟨P, z, hproper, hzQ, hz, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · simpa only [← hqz] using hycenter
  · simpa only [← hqz] using hunique
  · simpa only [← hqz] using hproduct
  · simpa only [← hqz] using hcentralizer
  · exact normal_hull_odd_quotient_point_hull_perfect Q hodd hnormal hrank z hzQ hzG
  · intro w hw
    exact normal_hull_odd_quotient_point_class_mem_iff Q hodd hnormal z hzQ hzG w hw

end CFSG.ComponentClassification.AschbacherTightEmbedding
