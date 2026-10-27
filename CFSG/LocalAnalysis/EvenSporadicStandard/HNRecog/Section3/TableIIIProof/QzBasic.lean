module

public import CFSG.LocalAnalysis.EvenSporadicStandard.HNRecog.Section3.QzConj
public import CFSG.LocalAnalysis.EvenSporadicStandard.HNRecog.Section3.Fusion1.NotConj
public import CFSG.LocalAnalysis.EvenSporadicStandard.HNRecog.Section3.GzOrbit.CIrrCard
public import CFSG.LocalAnalysis.EvenSporadicStandard.HNRecog.Section3.GzClass.CBridgeA
public import CFSG.LocalAnalysis.EvenSporadicStandard.HNRecog.Section3.HSide.XFusion

public section

namespace CFSG.EvenSporadicStandard.HNRecog.Section3

open CFSG.EvenSporadicStandard.HNRecog

variable {G : Type} [Group G]

private theorem t3_orderOf_eq_of_isConj {G : Type} [Group G] {a b : G} (h : IsConj a b) :
    orderOf a = orderOf b := by
  obtain ⟨c, hc⟩ := isConj_iff.mp h
  rw [← hc]
  simpa [MulAut.conj_apply] using (MulEquiv.orderOf_eq (MulAut.conj c) a).symm

private theorem t3_eq_one_or_eq_of_mem_zpowers {G : Type} [Group G] {z q : G}
    (hz : orderOf z = 2) (hq : q ∈ Subgroup.zpowers z) : q = 1 ∨ q = z := by
  obtain ⟨n, rfl⟩ := Subgroup.mem_zpowers_iff.mp hq
  rw [← zpow_mod_orderOf, hz]
  have hn : n % ((2 : ℕ) : ℤ) = 0 ∨ n % ((2 : ℕ) : ℤ) = 1 := by omega
  rcases hn with hn | hn
  · left; rw [hn]; simp
  · right; rw [hn]; simp

private theorem t3_pow_two_mem_centerOf {K : Type*} [Group K] {Q : Subgroup K}
    (hQ : IsPlusExtraspecial 4 Q) {q : K} (hq : q ∈ Q) : q ^ 2 ∈ centerOf Q := by
  haveI : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  let qQ : ↥Q := ⟨q, hq⟩
  haveI : CFSG.IsElementaryAbelian 2 (↥Q ⧸ Subgroup.center ↥Q) :=
    hQ.1.quotient_elementary_abelian
  have hExp : Monoid.exponent (↥Q ⧸ Subgroup.center ↥Q) ∣ 2 :=
    CFSG.IsElementaryAbelian.exponent_dvd_p 2 (↥Q ⧸ Subgroup.center ↥Q)
  have hpow : ((qQ : ↥Q ⧸ Subgroup.center ↥Q)) ^ 2 = 1 :=
    Monoid.exponent_dvd_iff_forall_pow_eq_one.mp hExp (qQ : ↥Q ⧸ Subgroup.center ↥Q)
  have hq2center : qQ ^ 2 ∈ Subgroup.center ↥Q := by
    exact (QuotientGroup.eq_one_iff (qQ ^ 2)).mp (by
      rw [QuotientGroup.mk_pow]
      exact hpow)
  rw [centerOf, Subgroup.mem_inf]
  refine ⟨pow_mem hq 2, ?_⟩
  rw [Subgroup.mem_centralizer_iff]
  intro y hy
  have hyQ : (⟨y, hy⟩ : ↥Q) * qQ ^ 2 = qQ ^ 2 * ⟨y, hy⟩ :=
    (Subgroup.mem_center_iff.mp hq2center) ⟨y, hy⟩
  have hcoe := congrArg (fun z : ↥Q => (z : K)) hyQ
  simpa [qQ, Subgroup.coe_pow] using hcoe

theorem tableIII_Qz_le (z : G) : Qz z ≤ Gx z :=
  Subgroup.map_subtype_le _

theorem tableIII_conj_mem_Qz {z g q : G} (hg : g ∈ Gx z) (hq : q ∈ Qz z) :
    g * q * g⁻¹ ∈ Qz z := by
  have hgz : g * z * g⁻¹ = z := by
    rw [mem_Gx] at hg
    calc g * z * g⁻¹ = z * g * g⁻¹ := by rw [← hg]
      _ = z := by group
  have h := Qz_conj_mem (x := z) g hq
  rwa [hgz] at h

theorem tableIII_isPGroup_Qz (z : G) : IsPGroup 2 ↥(Qz z) :=
  (CFSG.pCore_isPGroup (p := 2) (G := ↥(Gx z))).map (Gx z).subtype

theorem tableIII_mem_zpowers_iff {a z : G} (h : IsF5Type a z) {x : G} :
    x ∈ Subgroup.zpowers z ↔ x = 1 ∨ x = z := by
  constructor
  · intro hx
    exact t3_eq_one_or_eq_of_mem_zpowers h.orderOf_z hx
  · rintro (rfl | hx)
    · exact Subgroup.one_mem _
    · rw [hx]; exact Subgroup.mem_zpowers z

theorem tableIII_sq_mem_zpowers {a z : G} (h : IsF5Type a z) {q : G} (hq : q ∈ Qz z) :
    q ^ 2 ∈ Subgroup.zpowers z := by
  let q' : ↥(Gx z) := ⟨q, tableIII_Qz_le z hq⟩
  have hQz : Qz z = (CFSG.pCore 2 ↥(Gx z)).map (Gx z).subtype := rfl
  have hq'Q : q' ∈ CFSG.pCore 2 ↥(Gx z) := by
    obtain ⟨y, hy, hyq⟩ := Subgroup.mem_map.mp (hQz ▸ hq)
    rwa [show y = q' from Subtype.ext (by simpa [q'] using hyq)] at hy
  have hQ := isExtraspecialPlusByA5WrTwoWith_pCore (z := z) h.cent_z
  have hsq : q' ^ 2 ∈ centerOf (CFSG.pCore 2 ↥(Gx z)) :=
    t3_pow_two_mem_centerOf hQ.plus hq'Q
  rw [centerOf_eq_zpowers h.orderOf_z hQ] at hsq
  have hmap : (Subgroup.zpowers (GxSelf z)).map (Gx z).subtype = Subgroup.zpowers z := by
    rw [MonoidHom.map_zpowers]; rfl
  have hmem : ((q' ^ 2 : ↥(Gx z)) : G) ∈ Subgroup.zpowers z := by
    rw [← hmap]
    exact Subgroup.mem_map_of_mem (Gx z).subtype hsq
  simpa [q', Subgroup.coe_pow] using hmem

theorem tableIII_card_Qz_inf_Gx {a z : G} (h : IsF5Type a z) {q : G} (hq : q ∈ Qz z)
    (hq1 : q ≠ 1) (hqz : q ≠ z) : Nat.card ↥(Qz z ⊓ Gx q) = 2 ^ 8 := by
  let q' : ↥(Gx z) := ⟨q, tableIII_Qz_le z hq⟩
  let Q := CFSG.pCore 2 ↥(Gx z)
  have hQ := isExtraspecialPlusByA5WrTwoWith_pCore (z := z) h.cent_z
  have hQz : Qz z = Q.map (Gx z).subtype := rfl
  have hq'Q : q' ∈ Q := by
    obtain ⟨y, hy, hyq⟩ := Subgroup.mem_map.mp (hQz ▸ hq)
    rwa [show y = q' from Subtype.ext (by simpa [q'] using hyq)] at hy
  have hq'cent : q' ∉ centerOf Q := by
    intro hc
    rw [centerOf_eq_zpowers h.orderOf_z hQ] at hc
    have hmap : (Subgroup.zpowers (GxSelf z)).map (Gx z).subtype = Subgroup.zpowers z := by
      rw [MonoidHom.map_zpowers]; rfl
    have hmem : q ∈ Subgroup.zpowers z := by
      have h1 : ((q' : ↥(Gx z)) : G) ∈ Subgroup.zpowers z := by
        rw [← hmap]
        exact Subgroup.mem_map_of_mem (Gx z).subtype hc
      simpa [q'] using h1
    rcases (tableIII_mem_zpowers_iff h).mp hmem with h1 | hz
    · exact hq1 h1
    · exact hqz hz
  have hcard := card_inf_centralizer_of_isPlusExtraspecial hQ.plus hq'Q hq'cent
  have hEq : Qz z ⊓ Gx q =
      (Q ⊓ Subgroup.centralizer ({q'} : Set ↥(Gx z))).map (Gx z).subtype := by
    rw [hQz]
    ext g
    constructor
    · intro hg
      obtain ⟨hgQ, hgGq⟩ := Subgroup.mem_inf.mp hg
      obtain ⟨y, hyQ, hyg⟩ := Subgroup.mem_map.mp hgQ
      have hyG : (y : G) = g := hyg
      refine Subgroup.mem_map.mpr ⟨y, Subgroup.mem_inf.mpr ⟨hyQ, ?_⟩, hyg⟩
      rw [Subgroup.mem_centralizer_singleton_iff]
      apply Subtype.ext
      rw [Subgroup.coe_mul, Subgroup.coe_mul]
      show (y : G) * q = q * (y : G)
      rw [hyG]
      exact (mem_Gx.mp hgGq).symm
    · intro hg
      obtain ⟨y, ⟨hyQ, hycent⟩, hyg⟩ := Subgroup.mem_map.mp hg
      have hyG : (y : G) = g := hyg
      refine Subgroup.mem_inf.mpr ⟨Subgroup.mem_map.mpr ⟨y, hyQ, hyg⟩, ?_⟩
      rw [mem_Gx]
      have hy' : (y : G) * q = q * (y : G) := by
        have h := congrArg (fun t : ↥(Gx z) => (t : G))
          (Subgroup.mem_centralizer_singleton_iff.mp hycent)
        simpa [q', Subgroup.coe_mul] using h
      rw [← hyG]
      exact hy'.symm
  rw [hEq, Subgroup.card_map_of_injective (Gx z).subtype_injective]
  exact hcard

theorem tableIII_basic (hI : TwoHSInterface) {a z a' : G} (h : IsF5Type a z)
    (ha'Q : a' ∈ Qz z) (ha' : IsConj a a') :
    a' ^ 2 = 1 ∧ a' ≠ 1 ∧ a' ≠ z ∧ a' * z = z * a' ∧ z ^ 2 = 1 ∧ z ≠ 1 ∧
      a' * z ∈ Qz z ∧ IsConj a (a' * z) := by
  have ha'2 : orderOf a' = 2 := (t3_orderOf_eq_of_isConj ha').symm.trans h.orderOf_a
  have ha'pow : a' ^ 2 = 1 := by rw [← ha'2]; exact pow_orderOf_eq_one a'
  have ha'1 : a' ≠ 1 := by
    intro h1
    have h2 := ha'2
    rw [h1, orderOf_one] at h2
    omega
  have haz : a' ≠ z := by
    intro h1
    exact not_isConj_of_isF5Type hI h (h1 ▸ ha')
  have hcomm : a' * z = z * a' := (mem_Gx.mp (tableIII_Qz_le z ha'Q)).symm
  have hz2 : z ^ 2 = 1 := by rw [← h.orderOf_z]; exact pow_orderOf_eq_one z
  have hz1 : z ≠ 1 := by
    intro h1
    have h2 := h.orderOf_z
    rw [h1, orderOf_one] at h2
    omega
  have hzQ : z ∈ Qz z := self_mem_Qz hz2
  have hconj' : IsConj a' (a' * z) :=
    isConj_mul_of_mem_Qz h.cent_z h.orderOf_z ha'2 haz ha'Q
  exact ⟨ha'pow, ha'1, haz, hcomm, hz2, hz1, Subgroup.mul_mem _ ha'Q hzQ, ha'.trans hconj'⟩

end CFSG.EvenSporadicStandard.HNRecog.Section3
