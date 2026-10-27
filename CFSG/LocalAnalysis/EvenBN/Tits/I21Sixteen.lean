module

public import CFSG.LocalAnalysis.EvenBN.Tits.I21Two
public import CFSG.LocalAnalysis.EvenBN.Tits.I21Q8
public import CFSG.LocalAnalysis.EvenBN.Tits.I21Fusion

public section

namespace CFSG.LocalAnalysis.EvenBN.Tits.SecTwoHyp

open Subgroup CFSG.Open

variable {G : Type} [Group G] [Finite G] {t u : G}

theorem eq_of_mem_R_of_sq_eq_z (h : SecTwoHyp G t u) {r : G} (hr : r ∈ secTwoR t u)
    (hr2 : r ^ 2 = u ^ 2) : r = u ∨ r = u⁻¹ ∨ r = t * u ∨ r = t * u⁻¹ := by
  obtain ⟨a, b, rfl⟩ := h.exists_pow_of_mem_R hr
  have hu3 : u⁻¹ = u ^ 3 := by
    rw [inv_eq_iff_mul_eq_one, ← pow_succ', h.u_pow_four]
  rw [← pow_mod_orderOf t a, h.orderOf_t, ← pow_mod_orderOf u b, h.orderOf_u] at hr2 ⊢
  have hc := (h.commute_tu.pow_left (a % 2)).pow_right (b % 4)
  rw [hc.mul_pow, ← pow_mul, ← pow_mul, mul_comm (a % 2) 2, pow_mul, h.t_sq, one_pow,
    one_mul] at hr2
  have ha : a % 2 < 2 := Nat.mod_lt _ (by norm_num)
  have hb : b % 4 < 4 := Nat.mod_lt _ (by norm_num)
  have h4 : u ^ (2 * 2) = 1 := h.u_pow_four
  interval_cases (a % 2) <;> interval_cases (b % 4)
  · exfalso; apply h.z_ne_one; simpa using hr2.symm
  · left; simp
  · exfalso; apply h.z_ne_one; rw [h4] at hr2; exact hr2.symm
  · right; left; simp [hu3]
  · exfalso; apply h.z_ne_one; simpa using hr2.symm
  · right; right; left; simp
  · exfalso; apply h.z_ne_one; rw [h4] at hr2; exact hr2.symm
  · right; right; right; simp [hu3]

theorem exists_fixed_w (h : SecTwoHyp G t u) {y : G}
    (hyN : y ∈ normalizer (secTwoR t u : Set G)) (hyt : y * t * y⁻¹ = t * u ^ 2)
    (hy2 : y ^ 2 ∈ secTwoR t u) :
    ∃ w : G, (w = u ∨ w = t * u) ∧ w ^ 2 = u ^ 2 ∧ y * w * y⁻¹ = w := by
  have hu : u ∈ secTwoR t u := SecTwoHyp.u_mem_R
  have hxu : ∀ r ∈ secTwoR t u, ∀ s ∈ secTwoR t u, r * s = s * r :=
    fun r hr s hs => h.mul_comm_of_mem_R hr hs
  have hcu : t * u = u * t := h.commute
  set a := y * u * y⁻¹ with ha
  have haR : a ∈ secTwoR t u := (mem_normalizer_iff.mp hyN u).mp hu
  have ha2 : a ^ 2 = u ^ 2 := by
    rw [ha, conj_pow]; exact h.conj_z_of_normalizer hyN
  have hyyu : y * a * y⁻¹ = u := by
    have h1 : y * y * u = u * (y * y) := by rw [← sq]; exact hxu _ hy2 _ hu
    calc y * a * y⁻¹ = (y * y) * u * (y * y)⁻¹ := by rw [ha]; group
      _ = u := by rw [h1]; group
  have hu3 : u⁻¹ = u ^ 3 := by rw [inv_eq_iff_mul_eq_one, ← pow_succ', h.u_pow_four]
  have htt : t * t = 1 := h.t_mul_t
  have hcu2 : t * u ^ 2 = u ^ 2 * t := (h.commute_tu.pow_right 2).eq
  have hcontra : (t * u ^ 2) * (t * u) = u ^ 3 := by
    calc (t * u ^ 2) * (t * u) = t * (u ^ 2 * t) * u := by group
      _ = t * (t * u ^ 2) * u := by rw [hcu2]
      _ = (t * t) * u ^ 3 := by group
      _ = u ^ 3 := by rw [htt, one_mul]
  have hu31 : u ^ 3 ≠ u := by
    intro h31
    apply h.z_ne_one
    calc u ^ 2 = u ^ 3 * u⁻¹ := by group
      _ = 1 := by rw [h31]; group
  rcases h.eq_of_mem_R_of_sq_eq_z haR ha2 with h1 | h1 | h1 | h1
  · exact ⟨u, Or.inl rfl, rfl, h1⟩
  · refine ⟨t * u, Or.inr rfl, ?_, ?_⟩
    · rw [h.commute_tu.mul_pow, h.t_sq, one_mul]
    · calc y * (t * u) * y⁻¹ = (y * t * y⁻¹) * (y * u * y⁻¹) := by group
        _ = (t * u ^ 2) * u⁻¹ := by rw [hyt, ← ha, h1]
        _ = t * u := by group
  · exfalso
    apply hu31
    calc u ^ 3 = (t * u ^ 2) * (t * u) := hcontra.symm
      _ = (y * t * y⁻¹) * (y * u * y⁻¹) := by rw [hyt, ← ha, h1]
      _ = y * (t * u) * y⁻¹ := by group
      _ = y * a * y⁻¹ := by rw [h1]
      _ = u := hyyu
  · exfalso
    apply hu31
    have hinv : (t * u⁻¹)⁻¹ = u * t := by rw [mul_inv_rev, inv_inv, h.t_inv]
    have hcu3 : t * u ^ 3 = u ^ 3 * t := (h.commute_tu.pow_right 3).eq
    have hfin : (t * u ^ 2) * (u * t) = u ^ 3 := by
      calc (t * u ^ 2) * (u * t) = t * u ^ 3 * t := by group
        _ = u ^ 3 * t * t := by rw [hcu3]
        _ = u ^ 3 * (t * t) := by group
        _ = u ^ 3 := by rw [htt, mul_one]
    calc u ^ 3 = (t * u ^ 2) * (u * t) := hfin.symm
      _ = (y * t * y⁻¹) * (y * u * y⁻¹)⁻¹ := by rw [hyt, ← ha, h1, hinv]
      _ = y * (t * u⁻¹) * y⁻¹ := by group
      _ = y * a * y⁻¹ := by rw [h1]
      _ = u := hyyu

theorem exists_pow_t_w (h : SecTwoHyp G t u) {w : G} (hw : w = u ∨ w = t * u) {r : G}
    (hr : r ∈ secTwoR t u) : ∃ a b : ℕ, r = t ^ a * w ^ b := by
  obtain ⟨a, b, rfl⟩ := h.exists_pow_of_mem_R hr
  rcases hw with rfl | rfl
  · exact ⟨a, b, rfl⟩
  · refine ⟨a + b, b, ?_⟩
    have hu : u = t * (t * u) := by
      rw [← mul_assoc, h.t_mul_t, one_mul]
    have hc : Commute t (t * u) := (Commute.refl t).mul_right h.commute_tu
    conv_lhs => rw [hu, hc.mul_pow, ← mul_assoc, ← pow_add]

theorem exists_sq_eq_pow_w (h : SecTwoHyp G t u) {y w : G} (hyt : y * t * y⁻¹ = t * u ^ 2)
    (hw : w = u ∨ w = t * u) (hyw : y * w * y⁻¹ = w) (hy2 : y ^ 2 ∈ secTwoR t u) :
    ∃ b : ℕ, y ^ 2 = w ^ b := by
  obtain ⟨α, β, hαβ⟩ := h.exists_pow_t_w hw hy2
  have hcomm : y * y ^ 2 * y⁻¹ = y ^ 2 := by group
  have hc1 : Commute t (u ^ 2) := h.commute_tu.pow_right 2
  have hconj : y * (t ^ α * w ^ β) * y⁻¹ = (t * u ^ 2) ^ α * w ^ β := by
    calc y * (t ^ α * w ^ β) * y⁻¹ = (y * t * y⁻¹) ^ α * (y * w * y⁻¹) ^ β := by
          rw [conj_pow, conj_pow]; group
      _ = (t * u ^ 2) ^ α * w ^ β := by rw [hyt, hyw]
  have hz : (u ^ 2) ^ α = 1 := by
    have h1 : (t * u ^ 2) ^ α * w ^ β = t ^ α * w ^ β := by
      rw [← hconj, ← hαβ, hcomm]
    rw [hc1.mul_pow, mul_assoc] at h1
    have h2 := mul_left_cancel h1
    have h3 : (u ^ 2) ^ α * w ^ β = 1 * w ^ β := by rw [h2, one_mul]
    exact mul_right_cancel h3
  have hα : 2 ∣ α := by
    have h4 : u ^ (2 * α) = 1 := by rw [pow_mul]; exact hz
    have := orderOf_dvd_of_pow_eq_one h4
    rw [h.orderOf_u] at this
    omega
  obtain ⟨k, hk⟩ := hα
  refine ⟨β, ?_⟩
  rw [hαβ, hk, pow_mul, h.t_sq, one_pow, one_mul]

theorem z_pow_cases (h : SecTwoHyp G t u) (m : ℕ) :
    (u ^ 2) ^ m = 1 ∨ (u ^ 2) ^ m = u ^ 2 := by
  have hzz : (u ^ 2) ^ 2 = 1 := by rw [← pow_mul]; exact h.u_pow_four
  rcases Nat.even_or_odd m with ⟨k, rfl⟩ | ⟨k, rfl⟩
  · left; rw [← two_mul, pow_mul, hzz, one_pow]
  · right; rw [pow_succ, pow_mul, hzz, one_pow, one_mul]

theorem card_eq_sixteen (h : SecTwoHyp G t u) {S : Subgroup G} (hRS : secTwoR t u ≤ S)
    (hrel : (secTwoR t u).relIndex S = 2) : Nat.card S = 16 := by
  have := Subgroup.relIndex_mul_card (secTwoR t u) S
  rw [inf_of_le_left hRS, hrel, I21.card_R_eq h] at this
  omega

theorem exists_index_two_of_cyclic (h : SecTwoHyp G t u) {S : Subgroup G}
    (hRS : secTwoR t u ≤ S) (hrel : (secTwoR t u).relIndex S = 2) {y w : G} (hyS : y ∈ S)
    {β : ℕ} (hβ : Odd β) (hw2 : w ^ 2 = u ^ 2) (hyw : y ^ 2 = w ^ β) :
    ∃ U : Subgroup G, U ≤ S ∧ U.relIndex S = 2 ∧ ∀ e ∈ U, e ^ 2 = 1 → e = 1 ∨ e = u ^ 2 := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hzz : (u ^ 2) ^ 2 = 1 := by rw [← pow_mul]; exact h.u_pow_four
  have hy4 : y ^ 4 = u ^ 2 := by
    obtain ⟨m, rfl⟩ := hβ
    calc y ^ 4 = (y ^ 2) ^ 2 := by rw [← pow_mul]
      _ = (w ^ (2 * m + 1)) ^ 2 := by rw [hyw]
      _ = (w ^ 2) ^ (2 * m + 1) := by rw [← pow_mul, ← pow_mul, mul_comm]
      _ = (u ^ 2) ^ (2 * m + 1) := by rw [hw2]
      _ = u ^ 2 := by rw [pow_succ, pow_mul, hzz, one_pow, one_mul]
  have hord : orderOf y = 8 := by
    have h8 : orderOf y = 2 ^ (2 + 1) :=
      orderOf_eq_prime_pow (p := 2) (n := 2) (by norm_num; rw [hy4]; exact h.z_ne_one)
        (by
          rw [show (2 : ℕ) ^ (2 + 1) = 4 * 2 by norm_num, pow_mul, hy4]
          exact hzz)
    simpa using h8
  have hUS : zpowers y ≤ S := (zpowers_le).mpr hyS
  refine ⟨zpowers y, hUS, ?_, ?_⟩
  · have := Subgroup.relIndex_mul_card (zpowers y) S
    rw [inf_of_le_left hUS, Nat.card_zpowers, hord, h.card_eq_sixteen hRS hrel] at this
    omega
  · intro e he he2
    obtain ⟨n, hn⟩ := mem_powers_iff_mem_zpowers.mpr he
    have hn' : y ^ n = e := hn
    subst hn'
    have h1 : y ^ (n * 2) = 1 := by rw [pow_mul]; exact he2
    have h2 : 8 ∣ n * 2 := hord ▸ orderOf_dvd_of_pow_eq_one h1
    obtain ⟨m, hm⟩ : ∃ m, n = 4 * m := ⟨n / 4, by omega⟩
    rw [hm, pow_mul, hy4]
    exact h.z_pow_cases m

theorem exists_index_two_of_sq_eq_one (h : SecTwoHyp G t u) {S : Subgroup G}
    (hRS : secTwoR t u ≤ S) (hrel : (secTwoR t u).relIndex S = 2) {y w : G} (hyS : y ∈ S)
    (hyR : y ∉ secTwoR t u) (hyN : y ∈ normalizer (secTwoR t u : Set G))
    (hyt : y * t * y⁻¹ = t * u ^ 2) (hw : w = u ∨ w = t * u) (hw2 : w ^ 2 = u ^ 2)
    (hyw : y * w * y⁻¹ = w) (hy2 : y ^ 2 = 1) :
    ∃ U : Subgroup G, U ≤ S ∧ U.relIndex S = 2 ∧ ∀ e ∈ U, e ^ 2 = 1 → e = 1 ∨ e = u ^ 2 := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hzz : (u ^ 2) ^ 2 = 1 := by rw [← pow_mul]; exact h.u_pow_four
  have htR : t ∈ secTwoR t u := SecTwoHyp.t_mem_R
  have hwR : w ∈ secTwoR t u := by
    rcases hw with rfl | rfl
    · exact SecTwoHyp.u_mem_R
    · exact mul_mem htR SecTwoHyp.u_mem_R
  have hzR : u ^ 2 ∈ secTwoR t u := pow_mem SecTwoHyp.u_mem_R 2
  have hwt : w * t = t * w := h.mul_comm_of_mem_R hwR htR
  have hwz : w * u ^ 2 = u ^ 2 * w := h.mul_comm_of_mem_R hwR hzR
  have htz : t * u ^ 2 = u ^ 2 * t := h.mul_comm_of_mem_R htR hzR
  have hyz : y * u ^ 2 = u ^ 2 * y := by
    calc y * u ^ 2 = (y * u ^ 2 * y⁻¹) * y := by group
      _ = u ^ 2 * y := by rw [h.conj_z_of_normalizer hyN]
  have hyt' : y * t = t * u ^ 2 * y := by
    calc y * t = (y * t * y⁻¹) * y := by group
      _ = t * u ^ 2 * y := by rw [hyt]
  have hyw' : y * w = w * y := by
    calc y * w = (y * w * y⁻¹) * y := by group
      _ = w * y := by rw [hyw]
  have key : w * t * u ^ 2 * w = u ^ 2 * t * w * w := by
    calc w * t * u ^ 2 * w = t * w * u ^ 2 * w := by rw [hwt]
      _ = t * (w * u ^ 2) * w := by group
      _ = t * (u ^ 2 * w) * w := by rw [hwz]
      _ = (t * u ^ 2) * w * w := by group
      _ = (u ^ 2 * t) * w * w := by rw [htz]
  have hQ : I21.Q8Rel (u ^ 2) (t * w) (w * y) :=
    { z_sq := hzz
      z_ne_one := h.z_ne_one
      zp := ((show Commute (u ^ 2) t from htz.symm).mul_right
        (show Commute (u ^ 2) w from hwz.symm)).eq
      zq := ((show Commute (u ^ 2) w from hwz.symm).mul_right
        (show Commute (u ^ 2) y from hyz.symm)).eq
      p_sq := by
        rw [(show Commute t w from hwt.symm).mul_pow, h.t_sq, hw2, one_mul]
      q_sq := by
        rw [(show Commute w y from hyw'.symm).mul_pow, hw2, hy2, mul_one]
      qp := by
        calc (w * y) * (t * w) = w * (y * t) * w := by group
          _ = w * (t * u ^ 2 * y) * w := by rw [hyt']
          _ = (w * t * u ^ 2) * (y * w) := by group
          _ = (w * t * u ^ 2) * (w * y) := by rw [hyw']
          _ = (w * t * u ^ 2 * w) * y := by group
          _ = (u ^ 2 * t * w * w) * y := by rw [key]
          _ = u ^ 2 * ((t * w) * (w * y)) := by group }
  have hpR : t * w ∈ secTwoR t u := mul_mem htR hwR
  have hqS : w * y ∈ S := mul_mem (hRS hwR) hyS
  have hqR : w * y ∉ secTwoR t u := by
    intro hq
    apply hyR
    have := mul_mem (inv_mem hwR) hq
    simpa using this
  set U : Subgroup G := closure ({t * w, w * y} : Set G) with hU
  have hUS : U ≤ S := by
    rw [hU, closure_le]
    intro g hg
    rcases hg with rfl | rfl
    · exact hRS hpR
    · exact hqS
  have hpU : t * w ∈ U := subset_closure (by simp)
  have hqU : w * y ∈ U := subset_closure (by simp)
  have hUR : ¬ U ≤ secTwoR t u := fun hle => hqR (hle hqU)
  have hrelU : (secTwoR t u).relIndex U = 2 := by
    have hle : (secTwoR t u).relIndex U ≤ (secTwoR t u).relIndex S :=
      Subgroup.relIndex_le_of_le_right hUS (by rw [hrel]; norm_num)
    have hne1 : (secTwoR t u).relIndex U ≠ 1 := by
      rw [Ne, Subgroup.relIndex_eq_one]; exact hUR
    have hne0 : (secTwoR t u).relIndex U ≠ 0 := by
      intro h0
      have := Subgroup.relIndex_mul_card (secTwoR t u) U
      have hpos : 0 < Nat.card U := Nat.card_pos
      rw [h0, zero_mul] at this
      omega
    omega
  have hpord : orderOf (t * w) = 4 := by
    have h4 : orderOf (t * w) = 2 ^ (1 + 1) :=
      orderOf_eq_prime_pow (p := 2) (n := 1)
        (by rw [pow_one, show (2 : ℕ) = 2 from rfl, hQ.p_sq]; exact h.z_ne_one)
        (by
          rw [show (2 : ℕ) ^ (1 + 1) = 2 * 2 by norm_num, pow_mul, hQ.p_sq]
          exact hzz)
    simpa using h4
  have hge : 4 ≤ Nat.card (secTwoR t u ⊓ U : Subgroup G) := by
    have hle : zpowers (t * w) ≤ secTwoR t u ⊓ U :=
      le_inf ((zpowers_le).mpr hpR) ((zpowers_le).mpr hpU)
    have := Subgroup.card_le_of_le hle
    rwa [Nat.card_zpowers, hpord] at this
  have hcardU : Nat.card U = 8 := by
    have h1 := Subgroup.relIndex_mul_card (secTwoR t u) U
    have h2 : Nat.card U ≤ 8 := hQ.card_closure_le
    rw [hrelU] at h1
    omega
  refine ⟨U, hUS, ?_, fun e he he2 => hQ.eq_of_sq_eq_one he he2⟩
  have := Subgroup.relIndex_mul_card U S
  rw [inf_of_le_left hUS, hcardU, h.card_eq_sixteen hRS hrel] at this
  omega

theorem exists_index_two_unique_involution (h : SecTwoHyp G t u) {S : Subgroup G}
    (hS : IsPGroup 2 S) (hRS : secTwoR t u ≤ S) (hrel : (secTwoR t u).relIndex S = 2) :
    ∃ U : Subgroup G, U ≤ S ∧ U.relIndex S = 2 ∧ ∀ e ∈ U, e ^ 2 = 1 → e = 1 ∨ e = u ^ 2 := by
  have hne : secTwoR t u ≠ S := by
    intro heq
    rw [heq, Subgroup.relIndex_self] at hrel
    omega
  obtain ⟨y, hyS, hyR, hyN, hyt⟩ := h.exists_conj_t_eq hS hRS hne
  have hy2 : y ^ 2 ∈ secTwoR t u := by
    have hidx : ((secTwoR t u).subgroupOf S).index = 2 := hrel
    have h2 := Subgroup.sq_mem_of_index_two hidx ⟨y, hyS⟩
    simpa [Subgroup.mem_subgroupOf] using h2
  obtain ⟨w, hw, hw2, hyw⟩ := h.exists_fixed_w hyN hyt hy2
  obtain ⟨β, hβ⟩ := h.exists_sq_eq_pow_w hyt hw hyw hy2
  rcases Nat.even_or_odd β with ⟨γ, rfl⟩ | hodd
  · have hy2z : y ^ 2 = 1 ∨ y ^ 2 = u ^ 2 := by
      rw [hβ, ← two_mul, pow_mul, hw2]
      exact h.z_pow_cases γ
    rcases hy2z with h1 | h1
    · exact h.exists_index_two_of_sq_eq_one hRS hrel hyS hyR hyN hyt hw hw2 hyw h1
    · have htR : t ∈ secTwoR t u := SecTwoHyp.t_mem_R
      have hwR : w ∈ secTwoR t u := by
        rcases hw with rfl | rfl
        · exact SecTwoHyp.u_mem_R
        · exact mul_mem htR SecTwoHyp.u_mem_R
      have hwt : t * w * t⁻¹ = w := by
        rw [mul_inv_eq_iff_eq_mul]
        exact h.mul_comm_of_mem_R htR hwR
      refine h.exists_index_two_of_sq_eq_one (y := y * t) hRS hrel (mul_mem hyS (hRS htR)) ?_
        (mul_mem hyN (le_normalizer htR)) ?_ hw hw2 ?_ ?_
      · intro hyt'
        apply hyR
        have := mul_mem hyt' (inv_mem htR)
        simpa using this
      · calc y * t * t * (y * t)⁻¹ = y * t * y⁻¹ := by group
          _ = t * u ^ 2 := hyt
      · calc y * t * w * (y * t)⁻¹ = y * (t * w * t⁻¹) * y⁻¹ := by group
          _ = y * w * y⁻¹ := by rw [hwt]
          _ = w := hyw
      · calc (y * t) ^ 2 = (y * t) * (y * t) := pow_two _
          _ = (y * t * y⁻¹) * y ^ 2 * t := by group
          _ = (t * u ^ 2) * u ^ 2 * t := by rw [hyt, h1]
          _ = t * ((u ^ 2) * u ^ 2) * t := by group
          _ = t * t := by rw [← pow_add, show 2 + 2 = 4 from rfl, h.u_pow_four, mul_one]
          _ = 1 := h.t_mul_t
  · exact h.exists_index_two_of_cyclic hRS hrel hyS hodd hw2 hβ

end CFSG.LocalAnalysis.EvenBN.Tits.SecTwoHyp
