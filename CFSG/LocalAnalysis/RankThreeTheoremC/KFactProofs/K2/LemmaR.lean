module

public import CFSG.LocalAnalysis.RankThreeTheoremC.KFactProofs.K2.Defs
public import CFSG.LocalAnalysis.SectionRank.PRank
public import CFSG.GroupTheory.ElemAbelianClosure
public import CFSG.GroupTheory.ABGLocalTools.Basic

public section

namespace CFSG.LocalAnalysis.RankThreeTheoremC.KFactProofs.K2

open CFSG.Open CFSG.RankThreeCoreUniqueness.Helpers Subgroup
open scoped MatrixGroups

section Cards

variable {G : Type} [Group G] [Finite G] {Y Q : Subgroup G}

theorem lr_exists_orderOf_three {X : Type*} [Group X] [Finite X] {A : Subgroup X}
    (hA : IsPGroup 3 A) (hne : A ≠ ⊥) : ∃ a ∈ A, orderOf a = 3 := by
  haveI : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  have hdvd : 3 ∣ Nat.card A :=
    hA.card_eq_or_dvd.resolve_left fun h => hne (Subgroup.card_eq_one.mp h)
  obtain ⟨x, hx⟩ := exists_prime_orderOf_dvd_card' 3 hdvd
  exact ⟨x, x.2, (Subgroup.orderOf_coe x).trans hx⟩

theorem lr_one_le_pRank {X : Type*} [Group X] [Finite X] {S : Subgroup X}
    (hS : IsPGroup 3 S) (hne : S ≠ ⊥) : 1 ≤ CFSG.Open.pRank 3 S := by
  obtain ⟨a, ha, hord⟩ := lr_exists_orderOf_three hS hne
  refine CFSG.SectionRank.le_pRank (by norm_num) (Subgroup.zpowers_le.mpr ha)
    (isElemAbelian_zpowers (hord ▸ pow_orderOf_eq_one a)) ?_
  rw [Nat.card_zpowers, hord, pow_one]

theorem lr_lt_pRank_of_card {X : Type*} [Group X] [Finite X] {E H : Subgroup X}
    (hE : IsElemAbelian 3 E) (hEH : E ≤ H) {k : ℕ} (hk : 3 ^ k < Nat.card E) :
    k + 1 ≤ CFSG.Open.pRank 3 H := by
  haveI : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  obtain ⟨m, hm⟩ := hE.isPGroup.exists_card_eq
  have hkm : k < m := by
    rw [hm] at hk
    exact (Nat.pow_lt_pow_iff_right (by norm_num)).mp hk
  exact hkm.trans_le (CFSG.SectionRank.le_pRank (by norm_num) hEH hE hm)

theorem lr_exists_central (hQ : IsPGroup 3 Q) {T : Subgroup G} (hTQ : T ≤ Q)
    (hTn : Q ≤ normalizer (T : Set G)) (hT : T ≠ ⊥) :
    ∃ z ∈ T, orderOf z = 3 ∧ ∀ q ∈ Q, q * z = z * q := by
  haveI : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  haveI : Group.IsNilpotent Q := hQ.isNilpotent
  haveI hnorm : (T.subgroupOf Q).Normal :=
    (Subgroup.normal_subgroupOf_iff_le_normalizer hTQ).mpr hTn
  have hne : T.subgroupOf Q ≠ ⊥ := by
    intro hbot
    apply hT
    rw [Subgroup.eq_bot_iff_forall]
    intro t ht
    have h1 : (⟨t, hTQ ht⟩ : Q) ∈ T.subgroupOf Q := ht
    rw [hbot, Subgroup.mem_bot] at h1
    exact congrArg Subtype.val h1
  have hne2 : T.subgroupOf Q ⊓ Subgroup.center Q ≠ ⊥ :=
    Group.IsNilpotent.inf_center_ne_bot_of_normal hne
  obtain ⟨a, ha, ha3⟩ := lr_exists_orderOf_three
    (hQ.to_subgroup (T.subgroupOf Q ⊓ Subgroup.center Q)) hne2
  refine ⟨(a : G), ha.1, (Subgroup.orderOf_coe a).trans ha3, fun q hq => ?_⟩
  have hc := Subgroup.mem_center_iff.mp ha.2 ⟨q, hq⟩
  exact congrArg Subtype.val hc

theorem K2Setup.normalizer_le_of_normal (h : K2Setup G Y Q) {T : Subgroup G} (hTQ : T ≤ Q)
    (hTn : Q ≤ normalizer (T : Set G)) (hT : T ≠ ⊥) : normalizer (T : Set G) ≤ Y := by
  haveI : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  by_cases h2 : 2 ≤ CFSG.Open.pRank 3 T
  · exact h.y1 T hTQ h2
  obtain ⟨z, hzT, hz3, hzc⟩ := lr_exists_central h.pgroup hTQ hTn hT
  have hzQ : z ∈ Q := hTQ hzT
  have hz1 : z ^ 3 = 1 := hz3 ▸ pow_orderOf_eq_one z
  have huniq : ∀ w ∈ T, orderOf w = 3 → w ∈ zpowers z := by
    intro w hwT hw3
    by_contra hwz
    have hw1 : w ^ 3 = 1 := hw3 ▸ pow_orderOf_eq_one w
    have hzw : Commute z w := (hzc w (hTQ hwT)).symm
    have hE : IsElemAbelian 3 (zpowers z ⊔ zpowers w) := by
      refine (isElemAbelian_zpowers hz1).sup_of_commute (isElemAbelian_zpowers hw1) ?_
      intro a ha b hb
      obtain ⟨i, rfl⟩ := Subgroup.mem_zpowers_iff.mp ha
      obtain ⟨j, rfl⟩ := Subgroup.mem_zpowers_iff.mp hb
      exact (hzw.zpow_zpow i j).eq
    have hlt : zpowers z < zpowers z ⊔ zpowers w := by
      refine lt_of_le_of_ne le_sup_left fun heq => hwz ?_
      have hw : w ∈ zpowers z ⊔ zpowers w := Subgroup.mem_sup_right (Subgroup.mem_zpowers w)
      rwa [← heq] at hw
    have hcard : 3 ^ 1 < Nat.card (zpowers z ⊔ zpowers w : Subgroup G) := by
      have := Subgroup.card_lt_of_lt hlt
      rwa [Nat.card_zpowers, hz3] at this
    have hle : zpowers z ⊔ zpowers w ≤ T :=
      sup_le (Subgroup.zpowers_le.mpr hzT) (Subgroup.zpowers_le.mpr hwT)
    exact h2 (lr_lt_pRank_of_card hE hle hcard)
  have hnorm : normalizer (T : Set G) ≤ normalizer ((zpowers z : Subgroup G) : Set G) := by
    intro n hn
    apply Subgroup.mem_normalizer_fintype
    intro x hx
    obtain ⟨i, rfl⟩ := Subgroup.mem_zpowers_iff.mp hx
    have hnzT : n * z * n⁻¹ ∈ T := (Subgroup.mem_normalizer_iff.mp hn z).mp hzT
    have hnz3 : orderOf (n * z * n⁻¹) = 3 := by
      have := MulEquiv.orderOf_eq (MulAut.conj n) z
      rwa [MulAut.conj_apply, hz3] at this
    have hnz : n * z * n⁻¹ ∈ zpowers z := huniq _ hnzT hnz3
    rw [← conj_zpow]
    exact Subgroup.zpow_mem _ hnz i
  obtain ⟨A, hAQ, hA, hAcard⟩ := CFSG.SectionRank.exists_pRank (p := 3) (by norm_num) Q
  have hzA : z ∈ A := by
    by_contra hzA
    have hsup : IsElemAbelian 3 (A ⊔ zpowers z) := by
      refine hA.sup_of_commute (isElemAbelian_zpowers hz1) ?_
      intro a ha b hb
      obtain ⟨j, rfl⟩ := Subgroup.mem_zpowers_iff.mp hb
      exact (Commute.zpow_right (hzc a (hAQ ha)) j).eq
    have hlt : A < A ⊔ zpowers z := by
      refine lt_of_le_of_ne le_sup_left fun heq => hzA ?_
      have hz : z ∈ A ⊔ zpowers z := Subgroup.mem_sup_right (Subgroup.mem_zpowers z)
      rwa [← heq] at hz
    have hcard : 3 ^ CFSG.Open.pRank 3 Q < Nat.card (A ⊔ zpowers z : Subgroup G) := by
      have := Subgroup.card_lt_of_lt hlt
      rwa [hAcard] at this
    have hle : A ⊔ zpowers z ≤ Q := sup_le hAQ (Subgroup.zpowers_le.mpr hzQ)
    have := lr_lt_pRank_of_card hsup hle hcard
    omega
  obtain ⟨E, hEcard, hzE, hEA⟩ := Sylow.exists_subgroup_card_pow_prime_le_le
    (G := G) (p := 3) Nat.prime_three (n := 3) (H := zpowers z) (L := A)
    (by rw [Nat.card_zpowers, hz3]; norm_num)
    (by rw [hAcard]; exact pow_dvd_pow 3 h.rank) (Subgroup.zpowers_le.mpr hzA)
  have hrank1 : 1 ≤ CFSG.Open.pRank 3 (zpowers z) := by
    refine CFSG.SectionRank.le_pRank (by norm_num) le_rfl (isElemAbelian_zpowers hz1) ?_
    rw [Nat.card_zpowers, hz3, pow_one]
  exact hnorm.trans (h.y2 E (hEA.trans hAQ) (hA.mono hEA) (by rw [hEcard]; norm_num)
    (zpowers z) hzE hrank1)

theorem K2Setup.not_normal_le (h : K2Setup G Y Q) {N : Subgroup G} (hN : N.Normal)
    (h3 : 3 ∣ Nat.card N) (hNY : N ≤ Y) : False := by
  haveI : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  have hQtop : CFSG.ABGLocalTools.IsSylowOf 3 Q ⊤ := by
    rw [CFSG.ABGLocalTools.isSylowOf_iff]
    refine ⟨le_top, h.pgroup, ?_⟩
    rw [Subgroup.relIndex_top_right]
    exact h.index
  have hT : CFSG.ABGLocalTools.IsSylowOf 3 (Q ⊓ N) N :=
    hQtop.inf_of_le_normalizer le_top (Subgroup.le_normalizer_of_normal (H := N) (K := ⊤))
  have hTne : Q ⊓ N ≠ ⊥ := by
    intro hbot
    rw [CFSG.ABGLocalTools.isSylowOf_iff] at hT
    obtain ⟨_, _, hdvd⟩ := hT
    apply hdvd
    rw [hbot, Subgroup.relIndex_bot_left]
    exact h3
  have hTn : Q ≤ normalizer ((Q ⊓ N : Subgroup G) : Set G) := by
    have := (Subgroup.normal_subgroupOf_iff_le_normalizer_inf (H := N) (K := Q)).mp
      (hN.subgroupOf Q)
    rwa [inf_comm] at this
  have hR := h.normalizer_le_of_normal inf_le_left hTn hTne
  obtain ⟨S, hS⟩ := hT
  haveI := hN
  have hfrat := Sylow.normalizer_sup_eq_top S
  rw [hS] at hfrat
  have hle : (⊤ : Subgroup G) ≤ Y := by
    rw [← hfrat]
    exact sup_le hR hNY
  exact h.proper (top_le_iff.mp hle)

theorem K2Setup.gammaQ_le (h : K2Setup G Y Q) : gammaQ Q ≤ Y := by
  unfold gammaQ
  refine sup_le (iSup₂_le fun S hS => h.y1 S hS.1 hS.2) (iSup₂_le fun S hS => ?_)
  obtain ⟨E, hEQ, hE, hE27, hSE, hS0⟩ := hS
  exact h.y2 E hEQ hE hE27 S hSE (lr_one_le_pRank (h.pgroup.to_le (hSE.trans hEQ)) hS0)

end Cards

end CFSG.LocalAnalysis.RankThreeTheoremC.KFactProofs.K2
