module

public import CFSG.LocalAnalysis.OddStandard.SmallF3.Omega.Sec5OPNorm
public import CFSG.LocalAnalysis.OddStandard.SmallF3.Omega.Sec5OPW
public import CFSG.LocalAnalysis.OddStandard.SmallF3.Omega.Sec5OPGen

public section

attribute [-instance] instAddCommGroupOfIsSimpleAddGroupOfIsNilpotent
  instCommGroupOfIsSimpleGroupOfIsNilpotent

namespace CFSG.OddStandard.SmallF3.Omega

open Subgroup CFSG.Blueprint

theorem sec5op_Q_inf_centerIn {G : Type} [Group G] {L : Subgroup G} {z : G} {Q₁ Q₂ : Subgroup G}
    (h : Sec510Q G L z Q₁ Q₂) (hz2 : z * z = 1) : (Q₁ ⊔ Q₂) ⊓ centerIn L = ⊥ := by
  refine le_antisymm ?_ bot_le
  intro c hc
  rw [Subgroup.mem_inf] at hc
  obtain ⟨hcQ, hcZ⟩ := hc
  have hcL : c ∈ L := (sup_le h.le₁ h.le₂) hcQ
  have hcQcent : c ∈ centerIn (Q₁ ⊔ Q₂) := by
    rw [sec5_mem_centerIn_iff]
    exact ⟨hcQ, fun x hx => (sec5_mem_centerIn_iff.mp hcZ).2 x
      ((sup_le h.le₁ h.le₂) hx)⟩
  rw [h.center] at hcQcent
  have hzfin : IsOfFinOrder z :=
    isOfFinOrder_iff_pow_eq_one.mpr ⟨2, by norm_num, by simpa [pow_two] using hz2⟩
  have hc_pow : c ∈ Submonoid.powers z :=
    (hzfin.mem_powers_iff_mem_zpowers).mpr hcQcent
  obtain ⟨n, hn⟩ := (Submonoid.mem_powers_iff c z).mp hc_pow
  have hzn : z ^ n = 1 ∨ z ^ n = z := by
    rcases Nat.even_or_odd' n with ⟨k, hk | hk⟩
    · left
      rw [hk, pow_mul, pow_two, hz2, one_pow]
    · right
      rw [hk, pow_succ, pow_mul, pow_two, hz2, one_pow, one_mul]
  rw [← hn] at hcZ ⊢
  rcases hzn with h1 | hz
  · simpa using h1
  · exfalso
    exact h.not_central (hz ▸ hcZ)

variable {G : Type} [Group G] [Finite G] {t : G} {L S : Subgroup G} {z r ρ : G}
  {B A : Subgroup G} {φ : (Fin 6 → ZMod 2) → G} {K₁ K₂ : Subgroup G} {a b : G}
  {X : Type} [Group X] {π : ↥(centralizer ({z} : Set G)) →* X}

theorem sec5op_odd_cent_L (hy : Sec5B59Hyp) (hU : Asc82FactPocketsUniq6) (hF1 : Asc82FactQCent6)
    (h : Sec510Ctx G t L S z r ρ B A φ) (hs : Sec510Stage1 G t L S z φ A K₁ K₂ a b)
    (hyp : Sec5OPHyp t z (sec5p510_T t z (sec5p510_R S (twoCoreIn K₁) (twoCoreIn K₂))) π)
    (hQ : twoCoreIn K₁ ⊔ twoCoreIn K₂ ≤
      sec5op_kerG z (sec5p510_T t z (sec5p510_R S (twoCoreIn K₁) (twoCoreIn K₂))) π)
    {y : G} (hyY : y ∈ sec5op_Y t z) (hyt : y * t = t * y) (hyodd : Odd (orderOf y)) :
    y ∈ centralizer (L : Set G) := by
  have hz2 : z * z = 1 := by
    rw [← pow_two, ← hyp.hz, pow_orderOf_eq_one]
  have hyH : y ∈ centralizer ({z} : Set G) := sec5op_Y_le hyp.tH hyY
  have hyt' : y ∈ centralizer ({t} : Set G) :=
    Subgroup.mem_centralizer_singleton_iff.mpr hyt
  have hyt_inv : y⁻¹ ∈ centralizer ({t} : Set G) := Subgroup.inv_mem _ hyt'
  have hyH_inv : y⁻¹ ∈ centralizer ({z} : Set G) := Subgroup.inv_mem _ hyH
  have hyz_comm : y * z = z * y := Subgroup.mem_centralizer_singleton_iff.mp hyH
  have hcentQ : y ∈ centralizer ((twoCoreIn K₁ ⊔ twoCoreIn K₂ : Subgroup G) : Set G) := by
    rw [Subgroup.mem_centralizer_iff]
    intro q hq
    set Q : Subgroup G := twoCoreIn K₁ ⊔ twoCoreIn K₂ with hQdef
    have hyq : y⁻¹ * q * y ∈ Q :=
      sec5op_conj_Q_le hy hU h.toSec5Ctx hs.pk hyt' hyH hq
    have hyq' : y * q * y⁻¹ ∈ Q := by
      have h := sec5op_conj_Q_le hy hU h.toSec5Ctx hs.pk hyt_inv hyH_inv
        (y := y⁻¹) (x := q) hq
      simpa using h
    have hwQ : q * y * q⁻¹ * y⁻¹ ∈ Q := by
      have hinv : (y * q * y⁻¹)⁻¹ = y * q⁻¹ * y⁻¹ := by group
      have h1 : q * (y * q * y⁻¹)⁻¹ ∈ Q := Q.mul_mem hq (Q.inv_mem hyq')
      rw [hinv] at h1
      simpa [mul_assoc] using h1
    have hwW : q * y * q⁻¹ * y⁻¹ ∈ sec5op_W hyp :=
      sec5op_comm_mem_W hyp (hQ hq) hyY
    obtain ⟨e, n, hnN, hw_eq⟩ := sec5op_W_decomp hyp hwW
    have hzeQ : z ^ e ∈ Q := Q.pow_mem hs.pk.z_mem e
    have hnQ : n ∈ Q := by
      have hn_eq : n = (z ^ e)⁻¹ * (q * y * q⁻¹ * y⁻¹) := by
        rw [hw_eq]; group
      rw [hn_eq]
      exact Q.mul_mem (Q.inv_mem hzeQ) hwQ
    have hnOdd : Odd (orderOf n) :=
      odd_orderOf_of_mem_oddCoreIn (sec5op_N_le_oddCore hyp hnN)
    have hnS : n ∈ S := hs.pk.Q_le_S hnQ
    have h2pow : ∃ k, n ^ 2 ^ k = 1 := by
      obtain ⟨k, hk⟩ := h.syl.2.1 ⟨n, hnS⟩
      exact ⟨k, by simpa using congrArg Subtype.val hk⟩
    have hn1 : n = 1 := by
      obtain ⟨k, hk⟩ := h2pow
      have hdvd : orderOf n ∣ 2 ^ k := orderOf_dvd_iff_pow_eq_one.mpr hk
      obtain ⟨j, -, hord⟩ := (Nat.dvd_prime_pow Nat.prime_two).mp hdvd
      have hj0 : j = 0 := by
        rcases j with _ | j
        · rfl
        · exfalso
          have h2dvd : 2 ∣ 2 ^ (j + 1) := dvd_pow_self 2 (Nat.succ_ne_zero j)
          exact hnOdd.not_two_dvd_nat (hord.symm ▸ h2dvd)
      have h1 : orderOf n = 1 := by rw [hord, hj0, pow_zero]
      exact orderOf_eq_one_iff.mp h1
    have hwz : q * y * q⁻¹ * y⁻¹ = z ^ e := by
      simpa [hn1] using hw_eq
    have hcz : y * q * y⁻¹ * q⁻¹ = z ^ e := by
      have hinv : (q * y * q⁻¹ * y⁻¹)⁻¹ = (z ^ e)⁻¹ := by rw [hwz]
      have hLHS : (q * y * q⁻¹ * y⁻¹)⁻¹ = y * q * y⁻¹ * q⁻¹ := by group
      rw [hLHS] at hinv
      have hzsq : z ^ e * z ^ e = 1 := by
        rw [← Commute.mul_pow (Commute.refl z) e, hz2, one_pow]
      have hzinv : (z ^ e)⁻¹ = z ^ e := inv_eq_of_mul_eq_one_right hzsq
      rwa [hzinv] at hinv
    have htrick := sec5op_odd_comm_trick (N := (⊥ : Subgroup G)) hz2 hyz_comm
      (by intro n hn; rw [Subgroup.mem_bot.mp hn]; simp)
      (by intro n hn; rw [Subgroup.mem_bot.mp hn]; simp)
      (by
        have hN1 : Nat.card (⊥ : Subgroup G) = 1 :=
          Nat.card_eq_one_iff_unique.mpr ⟨inferInstance, ⟨1, by simp⟩⟩
        rw [hN1]
        exact ⟨0, rfl⟩)
      hyodd ⟨e, 1, Subgroup.mem_bot.mpr rfl, by simpa using hcz⟩
    have hcomm : y * q = q * y := by
      have h1 : y * q * y⁻¹ * q⁻¹ = 1 := Subgroup.mem_bot.mp htrick
      calc y * q = (y * q * y⁻¹ * q⁻¹) * (q * y) := by group
        _ = q * y := by rw [h1, one_mul]
    exact hcomm.symm
  have hYnorm : y ∈ normalizer (L : Set G) :=
    sec4_mem_normalizer hy.h36 h.toSec5Setting.toSec3SettingLB y hyt'
  have hOddY : Odd (Nat.card (zpowers y)) := by
    rw [Nat.card_zpowers]
    exact hyodd
  have hzpow_cent : zpowers y ≤
      centralizer ((twoCoreIn K₁ ⊔ twoCoreIn K₂ : Subgroup G) : Set G) := by
    intro x hx
    rw [Subgroup.mem_zpowers_iff] at hx
    obtain ⟨k, rfl⟩ := hx
    exact Subgroup.zpow_mem (K := centralizer
      ((twoCoreIn K₁ ⊔ twoCoreIn K₂ : Subgroup G) : Set G)) hcentQ k
  have hcentL : zpowers y ≤ centralizer (L : Set G) :=
    hF1 G L h.toSec5Ctx.toSec5Setting.isOm6Z2
      (twoCoreIn K₁) (twoCoreIn K₂) hs.pk.q.le₁ hs.pk.q.le₂ hs.pk.q.iso₁ hs.pk.q.iso₂
      hs.pk.q.comm hs.pk.q.card (sec5op_Q_inf_centerIn hs.pk.q hz2)
      (zpowers y) hOddY (Subgroup.zpowers_le.mpr hYnorm) hzpow_cent
  exact hcentL (Subgroup.mem_zpowers y)

end CFSG.OddStandard.SmallF3.Omega
