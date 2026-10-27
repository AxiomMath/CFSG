module

public import CFSG.LocalAnalysis.AGLEmbedding.Sp48NRank

public section

namespace CFSG.AGLEmbedding

open CFSG.Quasithin
open scoped Pointwise

variable {G : Type} [Group G] [Finite G]

theorem mul_comm_of_mem_homocyclic_nine {U : Subgroup G} {u v : G} (huU : u ∈ U) (hvU : v ∈ U)
    (hU : Nat.card U = 3 ^ 4) (hu : orderOf u = 9) (hv : orderOf v = 9) (huv : u * v = v * u)
    (hbot : Subgroup.zpowers u ⊓ Subgroup.zpowers v = ⊥) {x y : G} (hx : x ∈ U) (hy : y ∈ U) :
    x * y = y * x := by
  have hle : Subgroup.zpowers v ⊔ Subgroup.zpowers u ≤ U :=
    sup_le (Subgroup.zpowers_le.mpr hvU) (Subgroup.zpowers_le.mpr huU)
  have heq : Subgroup.zpowers v ⊔ Subgroup.zpowers u = U :=
    Subgroup.eq_of_le_of_card_ge hle
      (by rw [hU, card_zpowers_sup_zpowers_of_orderOf_eq_nine hu hv huv hbot]; norm_num)
  have hset := Subgroup.coe_mul_of_left_le_normalizer_right (Subgroup.zpowers u)
    (Subgroup.zpowers v) (zpowers_le_normalizer_zpowers_of_mul_comm huv)
  rw [sup_comm, heq] at hset
  have hx' : x ∈ ((Subgroup.zpowers u : Set G) * (Subgroup.zpowers v : Set G)) := by
    rw [← hset]; exact hx
  have hy' : y ∈ ((Subgroup.zpowers u : Set G) * (Subgroup.zpowers v : Set G)) := by
    rw [← hset]; exact hy
  obtain ⟨a, ha, b, hb, rfl⟩ := hx'
  obtain ⟨c, hc, d, hd, rfl⟩ := hy'
  obtain ⟨i, rfl⟩ := Subgroup.mem_zpowers_iff.mp ha
  obtain ⟨j, rfl⟩ := Subgroup.mem_zpowers_iff.mp hb
  obtain ⟨k, rfl⟩ := Subgroup.mem_zpowers_iff.mp hc
  obtain ⟨l, rfl⟩ := Subgroup.mem_zpowers_iff.mp hd
  have h1 : Commute u v := huv
  have huu : Commute (u ^ i) (u ^ k) := Commute.zpow_zpow_self u i k
  have hvv : Commute (v ^ j) (v ^ l) := Commute.zpow_zpow_self v j l
  have huv1 : Commute (u ^ i) (v ^ l) := h1.zpow_zpow i l
  have huv2 : Commute (v ^ j) (u ^ k) := (h1.zpow_zpow k j).symm
  exact ((huu.mul_right huv1).mul_left (huv2.mul_right hvv)).eq

theorem D1Sp48NData.exists_pow_three_eq_one_of_commute {P : Sylow 3 G}
    {M H R X U A V : Subgroup G} (hd : D1Sp48NData P M H R X U A V) :
    ∃ a ∈ R, a ^ 3 = 1 ∧ ∀ r ∈ R, r * a = a * r → r ^ 3 = 1 := by
  obtain ⟨u, v, huU, hvU, hu, hv, huv, hbot⟩ := hd.homocyclic
  have hcomm : ∀ x ∈ U, ∀ y ∈ U, x * y = y * x := fun x hx y hy =>
    mul_comm_of_mem_homocyclic_nine huU hvU hd.card_U hu hv huv hbot hx hy
  obtain ⟨a, haA, haU⟩ : ∃ a ∈ A, a ∉ U := by
    by_contra! hall
    have hle : A ≤ Subgroup.zpowers (u ^ 3) ⊔ Subgroup.zpowers (v ^ 3) := fun w hw =>
      mem_zpowers_cube_sup_of_pow_three_eq_one huU hvU hd.card_U hu hv huv hbot (hall w hw)
        (hd.elem_A.2 w hw)
    have := (Subgroup.card_le_of_le hle).trans (card_zpowers_cube_sup_le_nine hu hv huv)
    rw [hd.card_A] at this
    norm_num at this
  have haR : a ∈ R := hd.A_le haA
  have ha3 : a ^ 3 = 1 := hd.elem_A.2 a haA
  refine ⟨a, haR, ha3, fun r hr hra => ?_⟩
  have hidx : (U.subgroupOf R).index = 3 := by
    have h := Subgroup.card_mul_index (U.subgroupOf R)
    rw [Nat.card_congr (Subgroup.subgroupOfEquivOfLe hd.U_le).toEquiv, hd.card_U, hd.card_R]
      at h
    omega
  have hmin : (Nat.card R).minFac = 3 := by rw [hd.card_R]; norm_num
  have hUn : (U.subgroupOf R).Normal :=
    Subgroup.normal_of_index_eq_minFac_card (hidx.trans hmin.symm)
  have haN : Subgroup.zpowers a ≤ Subgroup.normalizer (U : Set G) := by
    rw [Subgroup.zpowers_le]
    exact (Subgroup.normal_subgroupOf_iff_le_normalizer hd.U_le).mp hUn haR
  have hsupR : Subgroup.zpowers a ⊔ U = R := by
    have hle : Subgroup.zpowers a ⊔ U ≤ R := sup_le (Subgroup.zpowers_le.mpr haR) hd.U_le
    have hlt : U < Subgroup.zpowers a ⊔ U :=
      lt_of_le_of_ne le_sup_right fun h => haU (h ▸ Subgroup.mem_sup_left (Subgroup.mem_zpowers a))
    have hd1 := Subgroup.card_dvd_of_le hle
    have hd2 := Subgroup.card_dvd_of_le hlt.le
    have hne : Nat.card U ≠ Nat.card (Subgroup.zpowers a ⊔ U : Subgroup G) := fun h =>
      hlt.ne (Subgroup.eq_of_le_of_card_ge hlt.le h.symm.le)
    rw [hd.card_R] at hd1
    rw [hd.card_U] at hd2 hne
    refine Subgroup.eq_of_le_of_card_ge hle ?_
    rw [hd.card_R]
    obtain ⟨c, hc⟩ := hd2
    have hc3 : c ∣ 3 := by
      have : 3 ^ 4 * c ∣ 3 ^ 4 * 3 := by rw [← hc]; simpa [pow_succ] using hd1
      exact Nat.dvd_of_mul_dvd_mul_left (by norm_num) this
    rcases (Nat.dvd_prime Nat.prime_three).mp hc3 with rfl | rfl
    · exact absurd (by rw [hc, mul_one]) hne
    · rw [hc]; norm_num
  have hset := Subgroup.coe_mul_of_left_le_normalizer_right (Subgroup.zpowers a) U haN
  rw [hsupR] at hset
  have hr' : r ∈ ((Subgroup.zpowers a : Set G) * (U : Set G)) := by rw [← hset]; exact hr
  obtain ⟨b, hb, w, hw, rfl⟩ := hr'
  obtain ⟨i, rfl⟩ := Subgroup.mem_zpowers_iff.mp hb
  have hai : Commute (a ^ i) a := Commute.zpow_self a i
  have hwa : w * a = a * w := by
    have h1 : a ^ i * (w * a) = a ^ i * (a * w) := by
      calc a ^ i * (w * a) = a ^ i * w * a := by group
        _ = a * (a ^ i * w) := hra
        _ = a ^ i * (a * w) := by rw [← mul_assoc, hai.eq.symm, mul_assoc]
    exact mul_left_cancel h1
  have hwZ : w ∈ centerOf R := by
    refine ⟨hd.U_le hw, Subgroup.mem_centralizer_iff.mpr fun x hx => ?_⟩
    have hx' : x ∈ ((Subgroup.zpowers a : Set G) * (U : Set G)) := by rw [← hset]; exact hx
    obtain ⟨c, hc, w', hw', rfl⟩ := hx'
    obtain ⟨j, rfl⟩ := Subgroup.mem_zpowers_iff.mp hc
    have h1 : Commute w (a ^ j) := (Commute.zpow_right (hwa : Commute w a) j)
    have h2 : Commute w w' := hcomm w hw w' hw'
    exact ((h1.mul_right h2).eq).symm
  have hwA : w ∈ A := hd.X_le_A (hd.center_le hwZ)
  exact hd.elem_A.2 _ (A.mul_mem (A.zpow_mem haA i) hwA)

end CFSG.AGLEmbedding
