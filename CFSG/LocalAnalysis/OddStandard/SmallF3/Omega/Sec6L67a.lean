module

public import CFSG.LocalAnalysis.OddStandard.SmallF3.Omega.Sec6Statements
public import CFSG.LocalAnalysis.SectionRank.PRank
import CFSG.GroupTheory.ElemAbelianClosure
import CFSG.ThirdParty.QiuzhenCFSG.GorensteinWalter.CardSupOfDisjointNormalizer
import CFSG.LocalAnalysis.OddStandard.SmallF3.Omega.Sec3L310Conj
public import CFSG.LocalAnalysis.OddStandard.SmallF3.Omega.Sec3Trans

public section

attribute [-instance] instAddCommGroupOfIsSimpleAddGroupOfIsNilpotent
  instCommGroupOfIsSimpleGroupOfIsNilpotent

namespace CFSG.OddStandard.SmallF3.Omega

open Subgroup CFSG.Blueprint

variable {G : Type} [Group G]

theorem sec67_card_sup_zpowers [Finite G] {E : Subgroup G} (hE : CFSG.Open.IsElemAbelian 2 E)
    {x : G} (hx2 : orderOf x = 2) (hxE : x ∉ E) (hcomm : ∀ e ∈ E, e * x = x * e) :
    CFSG.Open.IsElemAbelian 2 (E ⊔ Subgroup.zpowers x) ∧
      Nat.card ↥(E ⊔ Subgroup.zpowers x) = 2 * Nat.card ↥E := by
  have hx1 : x ^ 2 = 1 := by
    have h := pow_orderOf_eq_one x
    rw [hx2] at h
    simpa using h
  have hxz : CFSG.Open.IsElemAbelian 2 (Subgroup.zpowers x) :=
    CFSG.Open.isElemAbelian_zpowers hx1
  have hcomm' : ∀ a ∈ E, ∀ b ∈ Subgroup.zpowers x, a * b = b * a := by
    intro a ha b hb
    obtain ⟨k, hk⟩ := Subgroup.mem_zpowers_iff.mp hb
    rw [← hk]
    have hcx : Commute a x := hcomm a ha
    exact hcx.zpow_right k
  have hEA : CFSG.Open.IsElemAbelian 2 (E ⊔ Subgroup.zpowers x) :=
    CFSG.Open.IsElemAbelian.sup_of_commute hE hxz hcomm'
  have hdisj : Disjoint E (Subgroup.zpowers x) := by
    rw [disjoint_iff, eq_bot_iff]
    intro u hu
    rw [Subgroup.mem_bot]
    obtain ⟨k, hk⟩ := Subgroup.mem_zpowers_iff.mp hu.2
    have hux : u = x ^ k := hk.symm
    have hmod : x ^ k = x ^ (k % 2) := by
      rw [← zpow_mod_orderOf x k, show (orderOf x : ℤ) = 2 by rw [hx2]; norm_num]
    have hxkE : x ^ k ∈ E := hux ▸ hu.1
    have hxmodE : x ^ (k % 2) ∈ E := hmod ▸ hxkE
    rcases Int.emod_two_eq_zero_or_one k with h | h
    · rw [hux, hmod, h, zpow_zero]
    · rw [h, zpow_one] at hxmodE
      exact absurd hxmodE hxE
  have hnormal : Subgroup.zpowers x ≤ Subgroup.normalizer (E : Set G) :=
    (Subgroup.zpowers_le.mpr (Subgroup.mem_centralizer_iff.mpr hcomm)).trans
      (Subgroup.centralizer_le_normalizer (E : Set G))
  refine ⟨hEA, ?_⟩
  rw [CFSG.GorensteinWalter.card_sup_eq_mul_of_disjoint_of_le_normalizer E _ hnormal hdisj,
    Nat.card_zpowers, hx2, mul_comm]

theorem sec67_pRank_succ [Finite G] {x : G} (hx2 : orderOf x = 2) {D : Subgroup G}
    (hD : D ≤ centralizer ({x} : Set G)) (hxD : x ∉ D) :
    CFSG.Open.pRank 2 D + 1 ≤ CFSG.Open.pRank 2 (centralizer ({x} : Set G)) := by
  obtain ⟨E, hED, hEel, hEcard⟩ := CFSG.SectionRank.exists_pRank (by norm_num : 1 < 2) D
  have hxE : x ∉ E := fun h => hxD (hED h)
  have hcomm : ∀ e ∈ E, e * x = x * e := fun e he =>
    Subgroup.mem_centralizer_singleton_iff.mp (hD (hED he))
  obtain ⟨hEel', hEcard'⟩ := sec67_card_sup_zpowers hEel hx2 hxE hcomm
  have hle : E ⊔ Subgroup.zpowers x ≤ centralizer ({x} : Set G) :=
    sup_le (hED.trans hD)
      (Subgroup.zpowers_le.mpr (Subgroup.mem_centralizer_singleton_iff.mpr rfl))
  have hcard : Nat.card ↥(E ⊔ Subgroup.zpowers x) = 2 ^ (CFSG.Open.pRank 2 D + 1) := by
    rw [hEcard', hEcard, pow_succ, mul_comm]
  exact CFSG.SectionRank.le_pRank (by norm_num : 1 < 2) hle hEel' hcard

theorem sec67_cent_le_normalizer [Finite G] (h63 : Asc82Lemma63) {t : G} {L : Subgroup G}
    (hS : Sec3SettingLB G t L) (hHyp : Asc82Hyp62 G) {x : G} (hx2 : orderOf x = 2)
    {K : Subgroup G} (hK : IsComponentIn K (centralizer ({x} : Set G))) (hKF : InFStar K) :
    centralizer ({x} : Set G) ≤ normalizer (K : Set G) := by
  intro c hc
  have hK' : IsComponentIn (CFSG.conjugate K c) (centralizer ({x} : Set G)) :=
    hK.conjugate hc
  have hKF' : InFStar (CFSG.conjugate K c) := hKF.conjugate c
  have hEq : K = CFSG.conjugate K c :=
    h63 G t L hS hHyp x hx2 K (CFSG.conjugate K c) hK hKF hK' hKF'
  exact mem_normalizer_of_conjugate_eq hEq.symm

theorem asc82Lemma67a_of (h63 : Asc82Lemma63) (h65 : Asc82Lemma65) : Asc82Lemma67a := by
  intro G _ _ t L hS hL6 hHyp E hE x hx2 h6 K hK hKF
  obtain ⟨hEel, hEcard⟩ := hE
  have hCN : centralizer ({x} : Set G) ≤ normalizer (K : Set G) :=
    sec67_cent_le_normalizer h63 hS hHyp hx2 hK hKF
  have hInC : InC K := ⟨x, hx2, hK⟩
  have h65' : CFSG.Open.pRank 2 (normalizer (K : Set G)) ≤ 6 :=
    h65 G t L hS hHyp K hInC hKF
  have hle : CFSG.Open.pRank 2 (centralizer ({x} : Set G)) ≤ 6 :=
    (CFSG.SectionRank.pRank_mono (by norm_num : 1 < 2) hCN).trans h65'
  by_cases hxE : x ∈ E
  · have hEle : E ≤ centralizer ({x} : Set G) := fun e he =>
      Subgroup.mem_centralizer_singleton_iff.mpr (hEel.comm he hxE)
    have h8 : 8 ≤ CFSG.Open.pRank 2 (centralizer ({x} : Set G)) :=
      CFSG.SectionRank.le_pRank (by norm_num : 1 < 2) hEle hEel hEcard
    omega
  · have hD : E ⊓ centralizer ({x} : Set G) ≤ centralizer ({x} : Set G) := inf_le_right
    have hxD : x ∉ E ⊓ centralizer ({x} : Set G) := fun h => hxE h.1
    have hsucc := sec67_pRank_succ hx2 hD hxD
    omega

end CFSG.OddStandard.SmallF3.Omega
