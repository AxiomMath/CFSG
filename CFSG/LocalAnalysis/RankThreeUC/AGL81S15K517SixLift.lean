module

public import CFSG.LocalAnalysis.AGLEmbeddingD2.Tits.S3AmalgamBound.RankTwoCoverLift
public import CFSG.LocalAnalysis.SectionRank.PRank
public import CFSG.LieType.SeitzGeneration.ExcPlanePair

public section

namespace CFSG.LocalAnalysis.RankThreeUC.S15.K517Six

open CFSG.AGLEmbeddingD2.Tits.S3AmalgamBound

section Lift

variable {G X : Type*} [Group G] [Group X]

theorem exists_threeLift_of_inverted [Finite G] (q : G →* X) (hq : q.ker ≤ Subgroup.center G)
    {x b : G} (hw : orderOf (q x) = 3) (hinv : q b * q x * (q b)⁻¹ = (q x)⁻¹) :
    ∃ v : G, v ∈ Subgroup.closure {x, b} ∧ q v = q x ∧ v ^ 3 = 1 ∧ b * v * b⁻¹ = v⁻¹ := by
  have hw0 : orderOf x ≠ 0 := (orderOf_pos _).ne'
  obtain ⟨v₀, hv₀mem, hv₀q, s, hs⟩ :=
    exists_pElement_lift q Nat.prime_three (x := x) (k := 1) (by simpa using hw) hw0
  have hwmem : x ∈ Subgroup.closure {x, b} := Subgroup.subset_closure (by simp)
  have hv₀cl : v₀ ∈ Subgroup.closure {x, b} := by
    obtain ⟨m, rfl⟩ := Subgroup.mem_zpowers_iff.1 hv₀mem
    exact Subgroup.zpow_mem _ hwmem m
  have hbcl : b ∈ Subgroup.closure {x, b} := Subgroup.subset_closure (by simp)
  have e1 : q b * q x * (q b)⁻¹ = (q x)⁻¹ := hinv
  set z : G := v₀ * (b * v₀ * b⁻¹) with hz
  have hzq : q z = 1 := by
    rw [hz, map_mul, map_mul, map_mul, map_inv, hv₀q, e1]
    simp
  have hzc : z ∈ Subgroup.center G := hq (MonoidHom.mem_ker.2 hzq)
  have hzcl : z ∈ Subgroup.closure {x, b} :=
    Subgroup.mul_mem _ hv₀cl (Subgroup.mul_mem _ (Subgroup.mul_mem _ hbcl hv₀cl)
      (Subgroup.inv_mem _ hbcl))
  have hconj : b * v₀ * b⁻¹ = v₀⁻¹ * z := by rw [hz]; group
  have hv₀s : v₀ ^ (3 ^ s) = 1 := by rw [← hs]; exact pow_orderOf_eq_one _
  have hzs : z ^ (3 ^ s) = 1 := by
    have hcm : Commute v₀ (b * v₀ * b⁻¹) := by
      rw [hconj]
      exact (Commute.refl v₀).inv_right.mul_right (Subgroup.mem_center_iff.1 hzc v₀)
    rw [hz, hcm.mul_pow, hv₀s, one_mul]
    have : (b * v₀ * b⁻¹) ^ (3 ^ s) = b * v₀ ^ (3 ^ s) * b⁻¹ := by
      rw [conj_pow]
    rw [this, hv₀s]
    simp
  have hodd : Odd (3 ^ s) := Odd.pow (by decide)
  set t : ℕ := (3 ^ s - 1) / 2 with ht
  have h2t : 2 * t + 1 = 3 ^ s := by
    obtain ⟨c, hc⟩ := hodd
    rw [ht, hc]; omega
  set z₁ : G := z ^ t with hz₁
  have hz₁c : z₁ ∈ Subgroup.center G := Subgroup.pow_mem _ hzc t
  have hz₁q : q z₁ = 1 := by rw [hz₁, map_pow, hzq, one_pow]
  have hqv : q (v₀ * z₁) = q x := by rw [map_mul, hz₁q, mul_one, hv₀q]
  have hbz₁ : b * z₁ * b⁻¹ = z₁ := by
    rw [(Subgroup.mem_center_iff.1 hz₁c b), mul_assoc, mul_inv_cancel, mul_one]
  have hkey : z * z₁ * z₁ = 1 := by
    rw [hz₁, ← pow_succ', ← pow_add, show t + 1 + t = 3 ^ s by omega, hzs]
  have hzz : z * z₁ = z₁⁻¹ := eq_inv_of_mul_eq_one_left hkey
  have hc : z₁⁻¹ * v₀⁻¹ = v₀⁻¹ * z₁⁻¹ :=
    (Subgroup.mem_center_iff.1 (Subgroup.inv_mem _ hz₁c) v₀⁻¹).symm
  have hconjv : b * (v₀ * z₁) * b⁻¹ = (v₀ * z₁)⁻¹ := by
    have : b * (v₀ * z₁) * b⁻¹ = (b * v₀ * b⁻¹) * (b * z₁ * b⁻¹) := by group
    rw [this, hconj, hbz₁, mul_inv_rev, hc, mul_assoc, hzz]
  have hvs : (v₀ * z₁) ^ (3 ^ s) = 1 := by
    have hcm : Commute v₀ z₁ := Subgroup.mem_center_iff.1 hz₁c v₀
    rw [hcm.mul_pow, hv₀s, one_mul, hz₁, ← pow_mul, mul_comm, pow_mul, hzs, one_pow]
  have hv3 : (v₀ * z₁) ^ 3 = 1 := by
    set v := v₀ * z₁ with hv
    have hq3 : q (v ^ 3) = 1 := by
      rw [map_pow, hqv]
      exact hw ▸ pow_orderOf_eq_one _
    have hv3c : v ^ 3 ∈ Subgroup.center G := hq (MonoidHom.mem_ker.2 hq3)
    have h1 : b * v ^ 3 * b⁻¹ = (v ^ 3)⁻¹ := by
      have : b * v ^ 3 * b⁻¹ = (b * v * b⁻¹) ^ 3 := by rw [conj_pow]
      rw [this, hconjv, inv_pow]
    have h2 : b * v ^ 3 * b⁻¹ = v ^ 3 := by
      rw [(Subgroup.mem_center_iff.1 hv3c b), mul_assoc, mul_inv_cancel, mul_one]
    have h3 : v ^ 3 * v ^ 3 = 1 := by
      rw [h2] at h1
      exact mul_eq_one_iff_eq_inv.2 h1
    have h6 : orderOf v ∣ 6 :=
      orderOf_dvd_of_pow_eq_one (by rw [show 6 = 3 + 3 by rfl, pow_add]; exact h3)
    have hs' : orderOf v ∣ 3 ^ s := orderOf_dvd_of_pow_eq_one hvs
    have hcop : Nat.Coprime (orderOf v) 2 :=
      Nat.Coprime.coprime_dvd_left hs' (Nat.Coprime.pow_left s (by norm_num))
    have h3' : orderOf v ∣ 3 := hcop.dvd_of_dvd_mul_left (by simpa using h6)
    exact orderOf_dvd_iff_pow_eq_one.1 h3'
  exact ⟨v₀ * z₁, Subgroup.mul_mem _ hv₀cl (Subgroup.pow_mem _ hzcl t), hqv, hv3, hconjv⟩

end Lift

section Rank

variable {G Q : Type*} [Group G] [Finite G] [Group Q]

theorem not_mem_zpowers_of_inverted {a b m : Q} (ha3 : a ^ 3 = 1) (ha1 : a ≠ 1)
    (hma : m * a * m⁻¹ = a⁻¹) (hmb : m * b = b * m) : a ∉ Subgroup.zpowers b := by
  intro ha
  obtain ⟨k, hk⟩ := Subgroup.mem_zpowers_iff.1 ha
  have hmb' : m * b * m⁻¹ = b := by
    rw [mul_inv_eq_iff_eq_mul]
    exact hmb
  have h1 : m * a * m⁻¹ = a := by
    rw [← hk, ← conj_zpow, hmb']
  have h3 : a = a⁻¹ := h1.symm.trans hma
  have h4 : a ^ 2 = 1 := by
    rw [sq]
    nth_rewrite 1 [h3]
    exact inv_mul_cancel _
  have h6 : a = 1 := by
    have : a = a ^ 3 * (a ^ 2)⁻¹ := by group
    rw [this, ha3, h4]
    simp
  exact ha1 h6

theorem two_le_pRank_three_of_commuting_images {q : G →* Q} (hq : q.ker ≤ Subgroup.center G)
    {H : Subgroup G} {a b m : Q} (ha : a ∈ H.map q) (hb : b ∈ H.map q) (hm : m ∈ H.map q)
    (ha3 : a ^ 3 = 1) (ha1 : a ≠ 1) (hb3 : b ^ 3 = 1) (hb1 : b ≠ 1)
    (hma : m * a * m⁻¹ = a⁻¹) (hab : a * b = b * a) (hmb : m * b = b * m) :
    2 ≤ CFSG.Open.pRank 3 H := by
  classical
  haveI : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  obtain ⟨xa, hxa, rfl⟩ := ha
  obtain ⟨xb, hxb, rfl⟩ := hb
  obtain ⟨xm, hxm, rfl⟩ := hm
  have hoa : orderOf (q xa) = 3 := orderOf_eq_prime ha3 ha1
  have hob : orderOf (q xb) = 3 := orderOf_eq_prime hb3 hb1
  obtain ⟨v, hvcl, hvq, hv3, hmv⟩ := exists_threeLift_of_inverted q hq (x := xa) (b := xm) hoa hma
  have hvH : v ∈ H := by
    refine ((Subgroup.closure_le H).2 ?_) hvcl
    intro y hy
    rcases hy with rfl | rfl
    · exact hxa
    · exact hxm
  have hv1 : v ≠ 1 := fun h => ha1 (by rw [← hvq, h, map_one])
  have hvo : orderOf v = 3 := orderOf_eq_prime hv3 hv1
  obtain ⟨u, hu, huq, s, hs⟩ := exists_pElement_lift q Nat.prime_three (x := xb) (k := 1)
    (by simpa using hob) (orderOf_pos _).ne'
  have huH : u ∈ H := by
    obtain ⟨n, rfl⟩ := Subgroup.mem_zpowers_iff.1 hu
    exact Subgroup.zpow_mem _ hxb n
  have hucomm : u * v = v * u :=
    commute_of_inverted q hq hv3 hmv (by rw [map_mul, map_mul, huq, hvq]; exact hab.symm)
      (by rw [map_mul, map_mul, huq]; exact hmb)
  have hs1 : 1 ≤ s := by
    by_contra h
    have hs0 : s = 0 := by omega
    rw [hs0, pow_zero, orderOf_eq_one_iff] at hs
    rw [hs, map_one] at huq
    exact hb1 huq.symm
  set w : G := u ^ 3 ^ (s - 1) with hw
  have hwo : orderOf w = 3 := by
    have hdvd : 3 ^ (s - 1) ∣ orderOf u := by
      rw [hs]
      exact pow_dvd_pow 3 (by omega)
    rw [hw, orderOf_pow_of_dvd (by positivity) hdvd, hs, Nat.pow_div (by omega) (by norm_num)]
    rw [show s - (s - 1) = 1 by omega, pow_one]
  have hwH : w ∈ H := Subgroup.pow_mem _ huH _
  have hcomm : Commute w v := (Commute.pow_left (show Commute u v from hucomm) _)
  have hind : v ∉ Subgroup.zpowers w := by
    intro hvw
    obtain ⟨k, hk⟩ := Subgroup.mem_zpowers_iff.1 hvw
    have hqw : q w = (q xb) ^ 3 ^ (s - 1) := by rw [hw, map_pow, huq]
    have hqv : q v = (q w) ^ k := by rw [← hk, map_zpow]
    rw [hvq] at hqv
    rcases Nat.eq_or_lt_of_le hs1 with hs1' | hs2
    ·
      have hsub : s - 1 = 0 := by omega
      rw [hsub, pow_zero, pow_one] at hqw
      rw [hqw] at hqv
      exact not_mem_zpowers_of_inverted ha3 ha1 hma hmb (hqv ▸ Subgroup.zpow_mem_zpowers _ k)
    ·
      have hqw1 : q w = 1 := by
        have h3 : 3 ∣ 3 ^ (s - 1) := dvd_pow_self 3 (by omega)
        obtain ⟨c, hc⟩ := h3
        rw [hqw, hc, pow_mul, hb3, one_pow]
      rw [hqw1, one_zpow] at hqv
      exact ha1 hqv
  have hcard : Nat.card (Subgroup.closure ({w, v} : Set G)) = 3 ^ 2 :=
    CFSG.LieType.SeitzGeneration.card_closure_pair_sq Nat.prime_three hcomm hwo hvo hind
  have hE : CFSG.Open.IsElemAbelian 3 (Subgroup.closure ({w, v} : Set G)) :=
    CFSG.LieType.SeitzGeneration.isElemAbelian_closure_pair hcomm
      (by rw [← hwo]; exact pow_orderOf_eq_one w) hv3
  have hEH : Subgroup.closure ({w, v} : Set G) ≤ H := by
    refine (Subgroup.closure_le H).2 ?_
    intro y hy
    rcases hy with rfl | rfl
    · exact hwH
    · exact hvH
  exact CFSG.SectionRank.le_pRank (by norm_num) hEH hE hcard

end Rank

end CFSG.LocalAnalysis.RankThreeUC.S15.K517Six
