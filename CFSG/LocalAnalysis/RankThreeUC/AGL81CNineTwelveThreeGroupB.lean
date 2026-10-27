module

import CFSG.LocalAnalysis.SectionRank.AmbientRank
public import CFSG.CGT.PushingUpLit.Transport
public import CFSG.Fischer.Classification.Recognition.PSU6
public import CFSG.LocalAnalysis.AGLEmbeddingD2.Ambient
public import CFSG.LocalAnalysis.ComponentClassification.ClassicalModelStatedBridge
public import CFSG.LocalAnalysis.RankTwoShapes.UnitaryFour.Bridge
public import CFSG.LocalAnalysis.SectionRank.Ccomm.PowerMap
public import CFSG.LocalAnalysis.SectionRank.PRank
public import CFSG.RankThree.PartTwo.ExponentPrimeSmallRank

public section

namespace CFSG.LocalAnalysis.RankThreeUC.AGL81C

open Subgroup
open scoped commutatorElement

variable {R : Type} [Group R] [Finite R]

theorem mem_of_pow_three_eq_one_of_le_center (hR : IsPGroup 3 R)
    (hrk : CFSG.Open.pRank 3 (⊤ : Subgroup R) ≤ 3) {D : Subgroup R} (hDexp : ∀ x ∈ D, x ^ 3 = 1)
    (hDc : D ≤ center R) (hD : Nat.card D = 27) {x : R} (hx : x ^ 3 = 1) : x ∈ D := by
  by_contra hxD
  let S : Set R := (D : Set R) ∪ {x}
  let E : Subgroup R := closure S
  have hDle : D ≤ E := fun _ hy => Subgroup.subset_closure (Or.inl hy)
  have hxE : x ∈ E := Subgroup.subset_closure (Or.inr (by simp))
  have hDE : D < E := lt_iff_le_not_ge.mpr ⟨hDle, fun h => hxD (h hxE)⟩
  have hcardDE : Nat.card D < Nat.card E := Subgroup.card_lt_of_lt hDE
  haveI : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  have hpair : S.Pairwise Commute := by
    intro a ha b hb _
    rcases ha with haD | hax
    · exact (Subgroup.mem_center_iff.mp (hDc haD) b).symm
    · rw [Set.mem_singleton_iff] at hax
      rw [hax]
      rcases hb with hbD | hbx
      · exact Subgroup.mem_center_iff.mp (hDc hbD) x
      · rw [Set.mem_singleton_iff] at hbx
        exact hbx ▸ Commute.refl x
  haveI hEcomm : IsMulCommutative ↥E := isMulCommutative_closure hpair
  have hEexp : ∀ y ∈ E, y ^ 3 = 1 := by
    intro y hy
    refine Subgroup.closure_induction (p := fun z _ => z ^ 3 = 1) ?_ ?_ ?_ ?_ hy
    · intro z hz
      rcases hz with hzD | hzx
      · exact hDexp z hzD
      · rw [Set.mem_singleton_iff] at hzx
        rw [hzx]
        exact hx
    · exact one_pow 3
    · intro a b ha hb iha ihb
      have hab : Commute a b := congrArg Subtype.val (mul_comm' (⟨a, ha⟩ : ↥E) ⟨b, hb⟩)
      rw [Commute.mul_pow hab 3, iha, ihb, mul_one]
    · intro a _ iha
      rw [inv_pow, iha, inv_one]
  have hEelem : CFSG.Open.IsElemAbelian 3 E := ⟨hEcomm, hEexp⟩
  obtain ⟨j, hj⟩ := (IsPGroup.iff_card (p := 3) (G := ↥E)).mp (hR.to_subgroup E)
  have hj4 : 4 ≤ j := by
    by_contra h
    push Not at h
    have hle : 3 ^ j ≤ 27 := by
      calc 3 ^ j ≤ 3 ^ 3 := Nat.pow_le_pow_right (by norm_num) (by omega)
        _ = 27 := by norm_num
    omega
  have hle3 : j ≤ 3 := by
    have h := CFSG.SectionRank.le_pRank (p := 3) (H := ⊤) (E := E) (by norm_num : 1 < 3)
      le_top hEelem hj
    exact h.trans hrk
  omega

theorem mem_of_pow_three_eq_one_of_extraspecial (hR : IsPGroup 3 R)
    (hrk : CFSG.Open.pRank 3 (⊤ : Subgroup R) ≤ 3) {D : Subgroup R} [D.Normal]
    (hDexp : ∀ x ∈ D, x ^ 3 = 1)
    (hDcomm : ⁅D, (⊤ : Subgroup R)⁆ ≤ D ⊓ centralizer (D : Set R))
    (hD : CFSG.IsExtraspecialPGroup 3 ↥D) (hcard : Nat.card D = 3 ^ 5) {x : R}
    (hx : x ^ 3 = 1) : x ∈ D := by
  haveI : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  by_contra hxD
  let S : Set R := (D : Set R) ∪ {x}
  let E : Subgroup R := closure S
  let Z : Subgroup R := D ⊓ centralizer (D : Set R)
  have hDle : D ≤ E := fun _ hy => Subgroup.subset_closure (Or.inl hy)
  have hxE : x ∈ E := Subgroup.subset_closure (Or.inr (by simp))
  have hDE : D < E := lt_iff_le_not_ge.mpr ⟨hDle, fun h => hxD (h hxE)⟩
  have hcardDE : Nat.card D < Nat.card E := Subgroup.card_lt_of_lt hDE
  haveI hZn : Z.Normal := by
    change (D ⊓ centralizer (D : Set R)).Normal
    infer_instance
  have hZeq : (Subgroup.center ↥D).map D.subtype = Z := by
    ext z
    constructor
    · intro hz
      obtain ⟨y, hy, rfl⟩ := Subgroup.mem_map.1 hz
      refine ⟨y.2, ?_⟩
      exact Submonoid.mem_centralizer_iff.mpr fun w hw =>
        congrArg Subtype.val (Subgroup.mem_center_iff.mp hy ⟨w, hw⟩)
    · rintro ⟨hzD, hzC⟩
      refine Subgroup.mem_map.2 ⟨⟨z, hzD⟩, ?_, rfl⟩
      rw [Subgroup.mem_center_iff]
      intro g
      apply Subtype.ext
      exact Submonoid.mem_centralizer_iff.mp hzC g g.2
  have hZcard : Nat.card Z = 3 := by
    rw [← hZeq, Subgroup.card_map_of_injective D.subtype_injective, hD.2.2.2]
  haveI hnil : Group.IsNilpotent R := hR.isNilpotent
  have hZleC : Z ≤ Subgroup.center R := by
    have hZne : Z ≠ ⊥ := by
      intro h
      rw [h, Subgroup.card_bot] at hZcard
      norm_num at hZcard
    have hWne : Z ⊓ Subgroup.center R ≠ ⊥ :=
      Group.IsNilpotent.inf_center_ne_bot_of_normal hZne
    have hdvd : Nat.card ↥(Z ⊓ Subgroup.center R) ∣ Nat.card Z := by
      have h := Subgroup.card_subgroup_dvd_card ((Z ⊓ Subgroup.center R).subgroupOf Z)
      rwa [Nat.card_congr (Subgroup.subgroupOfEquivOfLe inf_le_left).toEquiv] at h
    have hWcard : Nat.card ↥(Z ⊓ Subgroup.center R) = 3 := by
      have h3 : Nat.card ↥(Z ⊓ Subgroup.center R) ∣ 3 := by rwa [hZcard] at hdvd
      rcases (Nat.dvd_prime Nat.prime_three).mp h3 with h1 | h3'
      · exact absurd ((Subgroup.eq_bot_iff_card (Z ⊓ Subgroup.center R)).mpr h1) hWne
      · exact h3'
    have hEq : Z ⊓ Subgroup.center R = Z :=
      Subgroup.eq_of_le_of_card_ge inf_le_left (by rw [hWcard, hZcard])
    exact inf_eq_left.mp hEq
  have hcommS : ∀ a ∈ S, ∀ b ∈ S, ⁅a, b⁆ ∈ Z := by
    intro a ha b hb
    rcases ha with haD | hax
    · rcases hb with _ | hbx
      · exact hDcomm (Subgroup.commutator_mem_commutator haD (Subgroup.mem_top b))
      · rw [Set.mem_singleton_iff] at hbx
        rw [hbx]
        exact hDcomm (Subgroup.commutator_mem_commutator haD (Subgroup.mem_top x))
    · rw [Set.mem_singleton_iff] at hax
      rw [hax]
      rcases hb with hbD | hbx
      · rw [← commutatorElement_inv]
        exact Z.inv_mem (hDcomm (Subgroup.commutator_mem_commutator hbD (Subgroup.mem_top x)))
      · rw [Set.mem_singleton_iff] at hbx
        rw [hbx]
        rw [commutatorElement_self]
        exact Z.one_mem
  let π : R →* R ⧸ Z := QuotientGroup.mk' Z
  have hpair : (π '' S).Pairwise Commute := by
    intro u hu v hv _
    obtain ⟨a, haS, rfl⟩ := hu
    obtain ⟨b, hbS, rfl⟩ := hv
    refine commutatorElement_eq_one_iff_mul_comm.mp ?_
    rw [← map_commutatorElement, QuotientGroup.mk'_apply, QuotientGroup.eq_one_iff]
    exact hcommS a haS b hbS
  have hmapcomm : IsMulCommutative ↥(E.map π) := by
    change IsMulCommutative ↥((closure S).map π)
    rw [MonoidHom.map_closure]
    exact isMulCommutative_closure hpair
  have hcommE : ∀ a ∈ E, ∀ b ∈ E, ⁅a, b⁆ ∈ Z := by
    intro a ha b hb
    have h1 : ⁅π a, π b⁆ = 1 := by
      haveI := hmapcomm
      exact commutatorElement_eq_one_iff_mul_comm.mpr
        (congrArg Subtype.val (mul_comm' (⟨π a, Subgroup.mem_map_of_mem π ha⟩ : ↥(E.map π))
          (⟨π b, Subgroup.mem_map_of_mem π hb⟩ : ↥(E.map π))))
    rw [← map_commutatorElement] at h1
    exact (QuotientGroup.eq_one_iff ⁅a, b⁆).mp h1
  have hclass : commutator ↥E ≤ Subgroup.center ↥E := by
    rw [_root_.commutator_def, Subgroup.commutator_le]
    intro a _ b _
    rw [Subgroup.mem_center_iff]
    intro g
    apply Subtype.ext
    change (g : R) * E.subtype ⁅a, b⁆ = E.subtype ⁅a, b⁆ * (g : R)
    rw [map_commutatorElement]
    exact Subgroup.mem_center_iff.mp (hZleC (hcommE (a : R) a.2 (b : R) b.2)) (g : R)
  have hEexp : ∀ y ∈ E, y ^ 3 = 1 := by
    intro y hy
    refine Subgroup.closure_induction (p := fun z _ => z ^ 3 = 1) ?_ ?_ ?_ ?_ hy
    · intro z hz
      rcases hz with hzD | hzx
      · exact hDexp z hzD
      · rw [Set.mem_singleton_iff] at hzx
        rw [hzx]
        exact hx
    · exact one_pow 3
    · intro a b ha hb iha ihb
      have hcZ : ⁅b, a⁆ ∈ Z := hcommE b hb a ha
      have hca : Commute a ⁅b, a⁆ := Subgroup.mem_center_iff.mp (hZleC hcZ) a
      have hcb : Commute b ⁅b, a⁆ := Subgroup.mem_center_iff.mp (hZleC hcZ) b
      rw [CFSG.SectionRank.Ccomm.mul_pow_prime_eq_of_commute (p := 3) Nat.prime_three
        (by norm_num) hca hcb (hDexp ⁅b, a⁆ hcZ.1), iha, ihb, mul_one]
    · intro a _ iha
      rw [inv_pow, iha, inv_one]
  have hexp : ∀ y : ↥E, y ^ 3 = 1 := by
    intro y
    apply Subtype.ext
    simpa using hEexp (y : R) y.2
  have hrkE : CFSG.pRank 3 ↥E ≤ 3 := by
    rw [CFSG.SectionRank.pRank_coe_eq_openPRank]
    exact (CFSG.SectionRank.pRank_mono (p := 3) (by norm_num) (le_top : E ≤ ⊤)).trans hrk
  have hbounds := CFSG.RankThree.PartTwo.class_two_small_rank_order_bounds (p := 3) (P := ↥E)
    (hR.to_subgroup E) hexp hclass
  have hquot : CFSG.pRank 3 (↥E ⧸ commutator ↥E) ≤ 4 := hbounds.2.2 hrkE
  haveI hCnorm : (commutator ↥E).Normal := by
    rw [_root_.commutator_def]
    infer_instance
  have hCmap : (commutator ↥E).map E.subtype ≤ Z := by
    rw [Subgroup.map_le_iff_le_comap]
    rw [_root_.commutator_def]
    refine Subgroup.commutator_le.mpr ?_
    intro a _ b _
    rw [Subgroup.mem_comap, map_commutatorElement]
    exact hcommE (a : R) a.2 (b : R) b.2
  have hCcard_le : Nat.card (commutator ↥E) ≤ 3 := by
    have h1 : Nat.card ((commutator ↥E).map E.subtype) = Nat.card (commutator ↥E) :=
      Subgroup.card_map_of_injective (K := commutator ↥E) E.subtype_injective
    rw [← h1, ← hZcard]
    exact Subgroup.card_le_of_le hCmap
  obtain ⟨m, hm⟩ := (IsPGroup.iff_card (p := 3) (G := ↥E)).mp (hR.to_subgroup E)
  obtain ⟨j, hj⟩ := (IsPGroup.iff_card (p := 3) (G := ↥E ⧸ commutator ↥E)).mp
    ((hR.to_subgroup E).to_quotient (commutator ↥E))
  have hm6 : 6 ≤ m := by
    have h : 3 ^ 5 < 3 ^ m := by
      rw [← hcard, ← hm]
      exact hcardDE
    have : 5 < m := (Nat.pow_lt_pow_iff_right (by norm_num : 1 < 3)).mp h
    omega
  have hj5 : 5 ≤ j := by
    have h1 : 3 ^ m = 3 ^ j * Nat.card (commutator ↥E) := by
      rw [← hm, ← hj]
      exact Subgroup.card_eq_card_quotient_mul_card_subgroup (commutator ↥E)
    have h2 : 3 ^ m ≤ 3 ^ (j + 1) := by
      rw [h1, pow_succ]
      exact Nat.mul_le_mul_left _ hCcard_le
    have h3 : m ≤ j + 1 := (Nat.pow_le_pow_iff_right (by norm_num : 1 < 3)).mp h2
    omega
  have hrankj : CFSG.pRank 3 (↥E ⧸ commutator ↥E) = j :=
    (CFSG.RankThree.PartTwo.quotient_commutator_rank (p := 3) (P := ↥E)
      Nat.prime_three hexp hj).2
  omega

end CFSG.LocalAnalysis.RankThreeUC.AGL81C
