module

public import CFSG.LocalAnalysis.EvenSporadicStandard.HNRecog.Section3.LocalGz
import CFSG.LocalAnalysis.EvenSporadicStandard.HNRecog.Section3.GzClass.CBridgeB
import CFSG.LocalAnalysis.EvenSporadicStandard.HNRecog.Section3.QzConj

public section

namespace CFSG.EvenSporadicStandard.HNRecog.Section3

open CFSG.EvenSporadicStandard.HNRecog

variable {G : Type} [Group G]

theorem gzNo_Qz_le (z : G) : Qz z ≤ Gx z :=
  Subgroup.map_subtype_le _

theorem gzNo_conj_mem_Qz {z g q : G} (hg : g ∈ Gx z) (hq : q ∈ Qz z) : g * q * g⁻¹ ∈ Qz z := by
  have h1 := Qz_conj_mem g hq
  rwa [← mem_Gx.mp hg, mul_inv_cancel_right] at h1

theorem gzNo_mem_zpowers_iff {z : G} (hz : orderOf z = 2) {q : G} :
    q ∈ Subgroup.zpowers z ↔ q = 1 ∨ q = z := by
  constructor
  · intro hq
    obtain ⟨k, rfl⟩ := Subgroup.mem_zpowers_iff.mp hq
    have hmod := zpow_mod_orderOf z k
    rw [hz, Nat.cast_ofNat] at hmod
    rw [← hmod]
    rcases Int.emod_two_eq_zero_or_one k with h0 | h1
    · left
      rw [h0, zpow_zero]
    · right
      rw [h1, zpow_one]
  · rintro (rfl | rfl)
    · exact Subgroup.one_mem _
    · exact Subgroup.mem_zpowers _

private theorem sq_mem_centerOf {K : Type*} [Group K] {Q : Subgroup K}
    (hQ : IsPlusExtraspecial 4 Q) {q : K} (hq : q ∈ Q) : q ^ 2 ∈ centerOf Q := by
  haveI : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  let qQ : ↥Q := ⟨q, hq⟩
  haveI : CFSG.IsElementaryAbelian 2 (↥Q ⧸ Subgroup.center ↥Q) :=
    hQ.1.quotient_elementary_abelian
  have hExp : Monoid.exponent (↥Q ⧸ Subgroup.center ↥Q) ∣ 2 :=
    CFSG.IsElementaryAbelian.exponent_dvd_p 2 (↥Q ⧸ Subgroup.center ↥Q)
  have hpow : ((qQ : ↥Q ⧸ Subgroup.center ↥Q)) ^ 2 = 1 :=
    Monoid.exponent_dvd_iff_forall_pow_eq_one.mp hExp (qQ : ↥Q ⧸ Subgroup.center ↥Q)
  have hq2center : qQ ^ 2 ∈ Subgroup.center ↥Q :=
    (QuotientGroup.eq_one_iff (qQ ^ 2)).mp (by rw [QuotientGroup.mk_pow]; exact hpow)
  rw [centerOf, Subgroup.mem_inf]
  refine ⟨pow_mem hq 2, ?_⟩
  rw [Subgroup.mem_centralizer_iff]
  intro y hy
  have hyQ : (⟨y, hy⟩ : ↥Q) * qQ ^ 2 = qQ ^ 2 * ⟨y, hy⟩ :=
    (Subgroup.mem_center_iff.mp hq2center) ⟨y, hy⟩
  have hcoe := congrArg (fun w : ↥Q => (w : K)) hyQ
  simpa [qQ, Subgroup.coe_pow] using hcoe

theorem gzNo_sq_mem_zpowers {a z : G} (h : IsF5Type a z) {q : G} (hq : q ∈ Qz z) :
    q ^ 2 ∈ Subgroup.zpowers z := by
  have hQ := isExtraspecialPlusByA5WrTwoWith_pCore h.cent_z
  obtain ⟨y, hy, rfl⟩ := Subgroup.mem_map.mp hq
  have h1 := sq_mem_centerOf hQ.plus hy
  rw [centerOf_eq_zpowers h.orderOf_z hQ] at h1
  obtain ⟨k, hk⟩ := Subgroup.mem_zpowers_iff.mp h1
  refine Subgroup.mem_zpowers_iff.mpr ⟨k, ?_⟩
  have h2 := congrArg Subtype.val hk
  simpa [Subgroup.coe_zpow, Subgroup.coe_pow, GxSelf] using h2

theorem gzNo_commute_of_mem_inf {a z x d t : G} (h : IsF5Type a z) (hd : d ∈ Qz z ⊓ Gx x)
    (ht : t ∈ Qz z ⊓ Qz x) (hzx : z ∉ Qz x) : d * t = t * d := by
  rw [Subgroup.mem_inf] at hd ht
  rcases (gzNo_mem_zpowers_iff h.orderOf_z).mp
      (commutatorElement_mem_zpowers_of_mem_Qz h hd.1 ht.1) with h2 | h2
  · exact commutatorElement_eq_one_iff_mul_comm.mp h2
  · refine absurd ?_ hzx
    rw [← h2, commutatorElement_def]
    exact mul_mem (gzNo_conj_mem_Qz hd.2 ht.2) (inv_mem ht.2)

theorem gzNo_cbarCent_mul {z : G} (x q : ↥(Gx z)) (hq : (q : G) ∈ Qz z) :
    CbarCent z (x * q) = CbarCent z x := by
  have hq1 : barOf z q = 1 := (barOf_eq_one_iff q).mpr hq
  have h1 : barOf z (x * q) = barOf z x := by
    have h2 : barOf z (x * q) = barOf z x * barOf z q := rfl
    rw [h2, hq1, mul_one]
  show Subgroup.centralizer ({barOf z (x * q)} : Set (Gbar z)) =
    Subgroup.centralizer ({barOf z x} : Set (Gbar z))
  rw [h1]

end CFSG.EvenSporadicStandard.HNRecog.Section3
