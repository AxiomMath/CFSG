module

public import CFSG.LocalAnalysis.OddStandard.SmallF3.Omega.Out1L12Calc
public import Mathlib.GroupTheory.PGroup

public section

namespace CFSG.OddStandard.SmallF3.Omega

variable {S : Type} [Group S]

private lemma aor_sq_eq_one_of_eq_inv {G : Type} [Group G] {a : G} (h : a = a⁻¹) :
    a ^ 2 = 1 := by
  rw [pow_two]
  nth_rewrite 2 [h]
  exact mul_inv_cancel a

private lemma aor_sq_eq_one_of_comm_inv {G : Type} [Group G] {a b : G} (hcomm : a * b = b * a)
    (hconj : a * b * a⁻¹ = b⁻¹) : b ^ 2 = 1 := by
  have hbinv : b⁻¹ = b := by
    rw [hcomm] at hconj
    rw [mul_assoc, mul_inv_cancel, mul_one] at hconj
    exact hconj.symm
  rw [pow_two]
  calc b * b = b⁻¹ * b := by rw [hbinv]
    _ = 1 := inv_mul_cancel b

private lemma aor_two_pow_pred_mul_two {k : ℕ} (hk : 1 ≤ k) : 2 ^ (k - 1) * 2 = 2 ^ k := by
  rw [← Nat.pow_succ 2 (k - 1), show (k - 1).succ = k by omega]

private lemma aor_two_pow_pred2_mul_two {k : ℕ} (hk : 2 ≤ k) :
    2 ^ (k - 2) * 2 = 2 ^ (k - 1) := by
  rw [← Nat.pow_succ 2 (k - 2), show (k - 2).succ = k - 1 by omega]

private lemma aor_two_pow_pred2_eq {k : ℕ} (hk : 3 ≤ k) : 2 ^ (k - 2) = 2 * 2 ^ (k - 3) := by
  rw [show k - 2 = k - 3 + 1 by omega, Nat.pow_succ']

private lemma aor_two_pow_not_dvd_pred {k : ℕ} (hk : 1 ≤ k) : ¬ (2 ^ k ∣ 2 ^ (k - 1)) := by
  intro hdvd
  have hle : k ≤ k - 1 := (Nat.pow_dvd_pow_iff_le_right (by norm_num : 1 < 2)).mp hdvd
  omega

private lemma aor_le_one_of_two_pow_dvd_two {k : ℕ} (h : 2 ^ k ∣ 2) : k ≤ 1 := by
  have h' : 2 ^ k ∣ 2 ^ 1 := by simpa using h
  exact (Nat.pow_dvd_pow_iff_le_right (by norm_num : 1 < 2)).mp h'

theorem aor_l12_cent_inv {t u : S} (h : L12Main S t u) (g y : S)
    (hy : y * (g * t * g⁻¹) = (g * t * g⁻¹) * y) (hy2 : y ^ 2 = 1) :
    y = 1 ∨ y = u ^ 2 ∨ y = g * t * g⁻¹ ∨ y = g * t * g⁻¹ * u ^ 2 := by
  have hy' : (g⁻¹ * y * g) * t = t * (g⁻¹ * y * g) := by
    calc (g⁻¹ * y * g) * t = g⁻¹ * (y * (g * t * g⁻¹)) * g := by group
      _ = g⁻¹ * ((g * t * g⁻¹) * y) * g := by rw [hy]
      _ = t * (g⁻¹ * y * g) := by group
  have hy'2 : (g⁻¹ * y * g) ^ 2 = 1 := by
    have h1 : g⁻¹ * y * g = g⁻¹ * y * (g⁻¹)⁻¹ := by rw [inv_inv]
    rw [h1, conj_pow, hy2]
    simp
  rcases h.coord.R_inv hy' hy'2 with h1 | h2 | h3 | h4
  · left
    calc y = g * (g⁻¹ * y * g) * g⁻¹ := by group
      _ = 1 := by rw [h1]; group
  · right; left
    have hz : g * u ^ 2 * g⁻¹ = u ^ 2 := by rw [h.z_central g]; group
    calc y = g * (g⁻¹ * y * g) * g⁻¹ := by group
      _ = g * u ^ 2 * g⁻¹ := by rw [h2]
      _ = u ^ 2 := hz
  · right; right; left
    calc y = g * (g⁻¹ * y * g) * g⁻¹ := by group
      _ = g * t * g⁻¹ := by rw [h3]
  · right; right; right
    have hz : g * u ^ 2 * g⁻¹ = u ^ 2 := by rw [h.z_central g]; group
    have hconv : g * (u ^ 2 * t) * g⁻¹ = (g * t * g⁻¹) * u ^ 2 := by
      rw [show g * (u ^ 2 * t) * g⁻¹ = (g * u ^ 2 * g⁻¹) * (g * t * g⁻¹) by group, hz,
        h.z_central (g * t * g⁻¹)]
    calc y = g * (g⁻¹ * y * g) * g⁻¹ := by group
      _ = g * (u ^ 2 * t) * g⁻¹ := by rw [h4]
      _ = (g * t * g⁻¹) * u ^ 2 := hconv

theorem aor_l12_LA [Finite S] (hS : IsPGroup 2 S) {t u : S} (h : L12Main S t u) (g : S)
    (hg : (g * t * g⁻¹) * u * (g * t * g⁻¹)⁻¹ ∈ Subgroup.zpowers u) :
    (g * t * g⁻¹) * u = u * (g * t * g⁻¹) := by
  let s : S := g * t * g⁻¹
  change s * u = u * s
  change s * u * s⁻¹ ∈ Subgroup.zpowers u at hg
  have ht2 : t ^ 2 = 1 := by rw [← h.coord.ord_t, pow_orderOf_eq_one]
  have ht_inv : t⁻¹ = t := by
    apply inv_eq_of_mul_eq_one_right
    rw [← pow_two, ht2]
  have hs_order : orderOf s = 2 := by
    have hconj : SemiconjBy g t s := by
      show g * t = (g * t * g⁻¹) * g
      group
    rw [← SemiconjBy.orderOf_eq g hconj, h.coord.ord_t]
  have hs2 : s ^ 2 = 1 := by rw [← hs_order, pow_orderOf_eq_one]
  have hs_inv : s⁻¹ = s := by
    apply inv_eq_of_mul_eq_one_right
    rw [← pow_two, hs2]
  have hv4 : orderOf (s * u * s⁻¹) = 4 := by
    have hconj : SemiconjBy s u (s * u * s⁻¹) := by
      show s * u = (s * u * s⁻¹) * s
      group
    rw [← SemiconjBy.orderOf_eq s hconj, h.coord.ord_u]
  rcases aor_l12_zpowers_four h.coord.ord_u hg hv4 with hv | hv
  · calc s * u = (s * u * s⁻¹) * s := by group
      _ = u * s := by rw [hv]
  · have hv_bad : s * u * s⁻¹ = u⁻¹ := hv
    let ρ : S := s * t
    have hρ : ρ = s * t := rfl
    have hsρ : s * ρ * s⁻¹ = ρ⁻¹ := by
      have hρinv : ρ⁻¹ = t * s := by rw [hρ, mul_inv_rev, ht_inv, hs_inv]
      rw [hρinv, hρ, hs_inv]
      calc s * (s * t) * s = s * s * t * s := by group
        _ = t * s := by rw [← pow_two, hs2, one_mul]
    have htρ : t * ρ * t⁻¹ = ρ⁻¹ := by
      have hρinv : ρ⁻¹ = t * s := by rw [hρ, mul_inv_rev, ht_inv, hs_inv]
      rw [hρinv, hρ, ht_inv]
      calc t * (s * t) * t = t * s * (t * t) := by group
        _ = t * s := by rw [← pow_two, ht2, mul_one]
    have htu : t * u * t⁻¹ = u := by rw [← h.coord.comm]; group
    have hρu : ρ * u * ρ⁻¹ = u⁻¹ := by
      rw [hρ]
      calc (s * t) * u * (s * t)⁻¹ = s * (t * u * t⁻¹) * s⁻¹ := by group
        _ = s * u * s⁻¹ := by rw [htu]
        _ = u⁻¹ := hv_bad
    have hconj2 : ρ ^ 2 * u * (ρ ^ 2)⁻¹ = u := by
      calc ρ ^ 2 * u * (ρ ^ 2)⁻¹ = ρ * (ρ * u * ρ⁻¹) * ρ⁻¹ := by
            rw [pow_two]; group
        _ = ρ * u⁻¹ * ρ⁻¹ := by rw [hρu]
        _ = (ρ * u * ρ⁻¹)⁻¹ := by rw [conj_inv]
        _ = u := by rw [hρu, inv_inv]
    have hρ2u_eq : ρ ^ 2 * u = u * ρ ^ 2 := by
      calc ρ ^ 2 * u = (ρ ^ 2 * u * (ρ ^ 2)⁻¹) * ρ ^ 2 := by
            rw [pow_two]; group
        _ = u * ρ ^ 2 := by rw [hconj2]
    have hρ2u : Commute (ρ ^ 2) u := hρ2u_eq
    obtain ⟨k, hk⟩ := hS.exists_orderOf_eq_pow ρ
    by_cases hk0 : k = 0
    · have hρ1 : ρ = 1 := by
        have : orderOf ρ = 1 := by rw [hk, hk0]; norm_num
        exact orderOf_eq_one_iff.mp this
      have hst1 : s * t = 1 := hρ1
      have hs_eq : s = t := by
        calc s = (s * t) * t⁻¹ := by group
          _ = 1 * t⁻¹ := by rw [hst1]
          _ = t := by rw [one_mul, ht_inv]
      rw [hs_eq]
      exact h.coord.comm.symm
    · by_cases hk1 : k = 1
      · have hk2' : orderOf ρ = 2 := by rw [hk, hk1]; norm_num
        have hρ2 : ρ ^ 2 = 1 := by rw [← hk2', pow_orderOf_eq_one]
        have hst : s * t = t * s := by
          have h1 : (s * t)⁻¹ = t * s := by rw [mul_inv_rev, hs_inv, ht_inv]
          have h2 : (s * t)⁻¹ = s * t := by
            apply inv_eq_of_mul_eq_one_right
            rw [← pow_two]
            exact hρ2
          rw [← h2, h1]
        exact h.coord.R_comm hst h.coord.comm
      · have hk2 : 2 ≤ k := by omega
        let w : S := ρ ^ (2 ^ (k - 1))
        have hw_def : w = ρ ^ (2 ^ (k - 1)) := rfl
        have hw2 : w ^ 2 = 1 := by
          rw [hw_def, ← pow_mul, aor_two_pow_pred_mul_two (by omega : 1 ≤ k), ← hk,
            pow_orderOf_eq_one]
        have hw_ne_one : w ≠ 1 := by
          intro hw1
          apply aor_two_pow_not_dvd_pred (by omega : 1 ≤ k)
          rw [← hk, orderOf_dvd_iff_pow_eq_one, ← hw_def]
          exact hw1
        have hwt : w * t = t * w := by
          have hconj : t * w * t⁻¹ = w⁻¹ := by
            change t * ρ ^ (2 ^ (k - 1)) * t⁻¹ = (ρ ^ (2 ^ (k - 1)))⁻¹
            rw [← conj_pow (a := t) (b := ρ) (i := 2 ^ (k - 1)), htρ, inv_pow]
          have hwinv : w⁻¹ = w := by
            apply inv_eq_of_mul_eq_one_right
            rw [← pow_two, hw2]
          rw [hwinv] at hconj
          have h1 : t * w = w * t := by
            have := congrArg (fun z => z * t) hconj
            simpa [mul_assoc] using this
          exact h1.symm
        have hwρ : w * ρ = ρ * w := by
          rw [hw_def]
          exact ((Commute.refl ρ).pow_left (2 ^ (k - 1))).eq
        have hu2ρ : u ^ 2 * ρ = ρ * u ^ 2 := (h.z_central ρ).symm
        have ht_not_comm : ¬ (t * ρ = ρ * t) := by
          intro hcomm
          have hρinv : ρ = ρ⁻¹ := by
            rw [← htρ, hcomm]
            group
          have hρ2 : ρ ^ 2 = 1 := aor_sq_eq_one_of_eq_inv hρinv
          have hdvd : 2 ^ k ∣ 2 := by
            rw [← hk, orderOf_dvd_iff_pow_eq_one]
            exact hρ2
          exact absurd (aor_le_one_of_two_pow_dvd_two hdvd) (by omega)
        have hW : w = u ^ 2 := by
          rcases h.coord.R_inv hwt hw2 with hw1 | hwz | hwt' | hwzt
          · exact absurd hw1 hw_ne_one
          · exact hwz
          · exfalso
            exact ht_not_comm (by rw [← hwt', hwρ])
          · exfalso
            have ht_eq : t = u ^ 2 * w := by
              rw [hwzt]
              rw [← mul_assoc, show u ^ 2 * u ^ 2 = 1 by rw [← pow_two, h.coord.z_sq],
                one_mul]
            apply ht_not_comm
            rw [ht_eq]
            calc u ^ 2 * w * ρ = u ^ 2 * (w * ρ) := by group
              _ = u ^ 2 * (ρ * w) := by rw [hwρ]
              _ = (u ^ 2 * ρ) * w := by group
              _ = (ρ * u ^ 2) * w := by rw [hu2ρ]
              _ = ρ * (u ^ 2 * w) := by group
        have hWrho : ρ ^ (2 ^ (k - 1)) = u ^ 2 := by
          rw [← hw_def]
          exact hW
        by_cases hk2eq : k = 2
        · have hρ2u2 : ρ ^ 2 = u ^ 2 := by
            have h1 : 2 ^ (k - 1) = 2 := by rw [hk2eq]; norm_num
            have h2 : ρ ^ (2 ^ (k - 1)) = u ^ 2 := hWrho
            rwa [h1] at h2
          have hsN : s ∈ L12N t := by
            apply h.mem_N
            have hstt : s * t * s⁻¹ * t⁻¹ = u ^ 2 := by
              rw [hs_inv, ht_inv]
              calc s * t * s * t = (s * t) * (s * t) := by group
                _ = u ^ 2 := by rw [← hρ, ← pow_two]; exact hρ2u2
            rw [hstt]
            exact Subgroup.npow_mem_zpowers u 2
          exact h.N_comm s hsN
        · have hk3 : 3 ≤ k := by omega
          let c : S := ρ ^ (2 ^ (k - 2))
          have hc2 : c ^ 2 = u ^ 2 := by
            change (ρ ^ (2 ^ (k - 2))) ^ 2 = u ^ 2
            rw [← pow_mul, aor_two_pow_pred2_mul_two hk2]
            exact hWrho
          have hcu_eq : c * u = u * c := by
            have hc_eq : c = (ρ ^ 2) ^ (2 ^ (k - 3)) := by
              change ρ ^ (2 ^ (k - 2)) = (ρ ^ 2) ^ (2 ^ (k - 3))
              rw [← pow_mul, aor_two_pow_pred2_eq hk3]
            rw [hc_eq]
            exact (hρ2u.pow_left (2 ^ (k - 3))).eq
          have hcu_comm : Commute c u := hcu_eq
          let e : S := c * u
          have he2 : e ^ 2 = 1 := by
            change (c * u) ^ 2 = 1
            rw [pow_two]
            calc (c * u) * (c * u) = c * (u * c) * u := by group
              _ = c * (c * u) * u := by rw [← hcu_eq]
              _ = (c * c) * (u * u) := by group
              _ = c ^ 2 * u ^ 2 := by rw [pow_two, pow_two]
              _ = u ^ 2 * u ^ 2 := by rw [hc2]
              _ = 1 := by rw [← pow_two, h.coord.z_sq]
          have he_inv : e⁻¹ = e := by
            apply inv_eq_of_mul_eq_one_right
            rw [← pow_two, he2]
          have hsc : s * c * s⁻¹ = c⁻¹ := by
            change s * ρ ^ (2 ^ (k - 2)) * s⁻¹ = (ρ ^ (2 ^ (k - 2)))⁻¹
            rw [← conj_pow (a := s) (b := ρ) (i := 2 ^ (k - 2)), hsρ, inv_pow]
          have hses : s * e * s⁻¹ = e := by
            change s * (c * u) * s⁻¹ = c * u
            calc s * (c * u) * s⁻¹ = (s * c * s⁻¹) * (s * u * s⁻¹) := by group
              _ = c⁻¹ * u⁻¹ := by rw [hsc, hv_bad]
              _ = (c * u)⁻¹ := by rw [hcu_eq, mul_inv_rev]
              _ = e⁻¹ := rfl
              _ = e := he_inv
          have hes : e * s = s * e := by
            calc e * s = (s * e * s⁻¹) * s := by rw [hses]
              _ = s * e := by group
          have htc_conj : t * c * t⁻¹ = c⁻¹ := by
            change t * ρ ^ (2 ^ (k - 2)) * t⁻¹ = (ρ ^ (2 ^ (k - 2)))⁻¹
            rw [← conj_pow (a := t) (b := ρ) (i := 2 ^ (k - 2)), htρ, inv_pow]
          have hut : Commute u t := h.coord.comm
          have he_comm : e * (g * t * g⁻¹) = (g * t * g⁻¹) * e := hes
          rcases aor_l12_cent_inv h g e he_comm he2 with he1 | hez | hes' | hesz
          · exfalso
            have hc_eq : c = u⁻¹ := by
              have hcu1 : c * u = 1 := he1
              rw [← inv_inv c, inv_eq_of_mul_eq_one_right hcu1]
            have htc : t * c = c * t := by
              rw [hc_eq]
              exact (hut.inv_left).symm
            have hc2one : c ^ 2 = 1 := aor_sq_eq_one_of_comm_inv htc htc_conj
            exact h.coord.z_ne_one (by rw [← hc2, hc2one])
          · exfalso
            have hc_eq : c = u := by
              have hcu1 : c * u = u ^ 2 := hez
              calc c = (c * u) * u⁻¹ := by group
                _ = u ^ 2 * u⁻¹ := by rw [hcu1]
                _ = u := by rw [pow_two]; group
            have htc : t * c = c * t := by
              rw [hc_eq]
              exact hut.symm
            have hc2one : c ^ 2 = 1 := aor_sq_eq_one_of_comm_inv htc htc_conj
            exact h.coord.z_ne_one (by rw [← hc2, hc2one])
          · exfalso
            have hs' : s = e := hes'.symm
            have hs_eq : s = c * u := by rw [hs']
            have hsc_comm : s * c = c * s := by
              rw [hs_eq]
              exact ((Commute.refl c).mul_left hcu_comm.symm).eq
            have hc2one : c ^ 2 = 1 := aor_sq_eq_one_of_comm_inv hsc_comm hsc
            exact h.coord.z_ne_one (by rw [← hc2, hc2one])
          · exfalso
            have hs_eq : s = c * u ^ 3 := by
              have hcu1 : c * u = s * u ^ 2 := hesz
              have hu2inv : (u ^ 2)⁻¹ = u ^ 2 := by
                apply inv_eq_of_mul_eq_one_right
                rw [← pow_two, h.coord.z_sq]
              calc s = (s * u ^ 2) * (u ^ 2)⁻¹ := by group
                _ = (c * u) * (u ^ 2)⁻¹ := by rw [← hcu1]
                _ = c * u * u ^ 2 := by rw [hu2inv]
                _ = c * u ^ 3 := by
                  rw [mul_assoc, show u * u ^ 2 = u ^ 3 by rw [← pow_succ']]
            have hsc_comm : s * c = c * s := by
              rw [hs_eq]
              exact ((Commute.refl c).mul_left ((hcu_comm.pow_right 3).symm)).eq
            have hc2one : c ^ 2 = 1 := aor_sq_eq_one_of_comm_inv hsc_comm hsc
            exact h.coord.z_ne_one (by rw [← hc2, hc2one])

end CFSG.OddStandard.SmallF3.Omega
