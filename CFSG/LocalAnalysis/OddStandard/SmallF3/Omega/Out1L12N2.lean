module

public import CFSG.LocalAnalysis.OddStandard.SmallF3.Omega.Out1L12N1

public section

namespace CFSG.OddStandard.SmallF3.Omega

variable {S : Type} [Group S]

private theorem aor_l12_coord_mul_t {t u : S} (h : L12Coord S t u) :
    L12Coord S t (u * t) := by
  have ht2 : t ^ 2 = 1 := h.t_sq
  have hu4 : u ^ 4 = 1 := h.u_pow_four
  have hcu : Commute u t := h.comm
  have hct : u * t = t * u := h.comm
  have ht4 : t ^ 4 = 1 := by
    rw [show (4 : ℕ) = 2 * 2 from rfl, pow_mul, ht2, one_pow]
  have h2 : (u * t) ^ 2 = u ^ 2 := by
    rw [hcu.mul_pow 2, ht2, mul_one]
  have h4 : (u * t) ^ 4 = 1 := by
    rw [hcu.mul_pow 4, hu4, ht4, mul_one]
  have hord : orderOf (u * t) = 4 := by
    have hp := orderOf_eq_prime_pow (p := 2) (n := 1) (x := u * t)
      (by rw [show (2 : ℕ) ^ 1 = 2 from rfl, h2]; exact h.z_ne_one)
      (by rw [show (2 : ℕ) ^ (1 + 1) = 4 from rfl]; exact h4)
    rwa [show (2 : ℕ) ^ (1 + 1) = 4 from rfl] at hp
  refine ⟨h.ord_t, hord, ?_, ?_, ?_, h.card⟩
  · have hL : (u * t) * t = u := by rw [mul_assoc, ← pow_two, ht2, mul_one]
    have hR : t * (u * t) = u := by
      rw [← mul_assoc, ← hct, mul_assoc, ← pow_two, ht2, mul_one]
    rw [hL, hR]
  · intro htmem
    have hu_mem : u ∈ Subgroup.zpowers (u * t) := by
      have h1 : (u * t) * t⁻¹ ∈ Subgroup.zpowers (u * t) :=
        Subgroup.mul_mem _ (Subgroup.mem_zpowers _) (Subgroup.inv_mem _ htmem)
      simpa [mul_assoc] using h1
    rcases aor_l12_zpowers_four (u := u * t) (v := u) hord hu_mem h.ord_u with hc | hc
    · exact h.t_ne_one (mul_left_cancel (a := u) (by simpa using hc.symm))
    · apply h.t_ne_z
      have huu : u * u = t := by
        nth_rewrite 1 [hc]
        rw [mul_inv_rev, mul_assoc, inv_mul_cancel, mul_one, h.t_inv]
      rw [← huu, pow_two]
  · intro x hx
    obtain ⟨i, j, hxij⟩ := h.cent x hx
    refine ⟨i, i + j, ?_⟩
    rw [hxij, hcu.mul_pow i, mul_assoc, ← pow_add]
    congr 1
    have he : i + (i + j) = 2 * i + j := by rw [← Nat.add_assoc, ← two_mul]
    rw [he, pow_add, pow_mul, ht2, one_pow, one_mul]

theorem aor_l12_main [Finite S] (hS : IsPGroup 2 S) {t u : S} (h : L12Coord S t u)
    (hnc : ¬ ∀ x : S, x * t = t * x) : ∃ u₀ : S, L12Main S t u₀ := by
  classical
  have hct : u * t = t * u := h.comm
  have hcu : Commute u t := h.comm
  have hz : ∀ x : S, x * u ^ 2 = u ^ 2 * x := aor_l12_z_central hS h hnc
  obtain ⟨n, hn, hnt⟩ := aor_l12_exists_N hS h hnc
  have hnt' : n * t * n⁻¹ = t * u ^ 2 := by
    rcases aor_l12_N_conj hS h hnc hn with h' | h'
    · exfalso
      apply hnt
      have := congrArg (· * n) h'
      rwa [mul_assoc, inv_mul_cancel, mul_one] at this
    · exact h'
  have hu_R : u ∈ L12R t := by
    change u ∈ Subgroup.centralizer ({t} : Set S)
    rw [Subgroup.mem_centralizer_iff]
    intro x hx
    rw [Set.mem_singleton_iff] at hx
    rw [hx]
    exact hct.symm
  set v : S := n * u * n⁻¹ with hv_def
  have hv_mem : v ∈ L12R t := by
    have h1 : n * u * n⁻¹ ∈ L12R t :=
      (Subgroup.mem_set_normalizer_iff.mp hn u).mp hu_R
    rwa [← hv_def] at h1
  have hv_comm : v * t = t * v := by
    have h1 := (Subgroup.mem_centralizer_iff.mp hv_mem) t (Set.mem_singleton t)
    exact h1.symm
  have hv_sq : v ^ 2 = u ^ 2 := by
    rw [hv_def]
    rw [show (n * u * n⁻¹) ^ 2 = n * u ^ 2 * n⁻¹ from conj_pow]
    rw [hz n, mul_assoc, mul_inv_cancel, mul_one]
  have hnn_conj : (n * n) * t * (n * n)⁻¹ = t := by
    calc (n * n) * t * (n * n)⁻¹
        = n * (n * t * n⁻¹) * n⁻¹ := by group
      _ = n * (t * u ^ 2) * n⁻¹ := by rw [hnt']
      _ = (n * t * n⁻¹) * (n * u ^ 2 * n⁻¹) := by group
      _ = (t * u ^ 2) * u ^ 2 := by
            rw [hnt']
            congr 1
            rw [hz n, mul_assoc, mul_inv_cancel, mul_one]
      _ = t := by
            rw [mul_assoc, ← pow_add, show (2 : ℕ) + 2 = 4 from rfl, h.u_pow_four, mul_one]
  have hnn_comm : (n * n) * t = t * (n * n) := by
    have := congrArg (· * (n * n)) hnn_conj
    simpa [mul_assoc, mul_inv_cancel, mul_one] using this
  have hnn_u : (n * n) * u = u * (n * n) := L12Coord.R_comm h hnn_comm h.comm
  have hnv : n * v * n⁻¹ = u := by
    calc n * v * n⁻¹ = n * (n * u * n⁻¹) * n⁻¹ := by rw [hv_def]
      _ = (n * n) * u * n⁻¹ * n⁻¹ := by group
      _ = (u * (n * n)) * n⁻¹ * n⁻¹ := by rw [hnn_u]
      _ = u := by group
  have hw_mem : v * u⁻¹ ∈ L12R t := (L12R t).mul_mem hv_mem ((L12R t).inv_mem hu_R)
  have hw_comm : (v * u⁻¹) * t = t * (v * u⁻¹) := by
    have h1 := (Subgroup.mem_centralizer_iff.mp hw_mem) t (Set.mem_singleton t)
    exact h1.symm
  have hw_sq : (v * u⁻¹) ^ 2 = 1 := by
    have hvu : Commute v u := L12Coord.R_comm h hv_comm h.comm
    rw [(hvu.inv_right).mul_pow 2, hv_sq]
    rw [show (u⁻¹) ^ 2 = (u ^ 2)⁻¹ from by rw [pow_two, pow_two, ← mul_inv_rev]]
    rw [mul_inv_cancel]
  have hw_cases := L12Coord.R_inv h hw_comm hw_sq
  have hv_cases : v = u ∨ v = u ^ 3 ∨ v = u * t ∨ v = u ^ 3 * t := by
    rcases hw_cases with h1 | h1 | h1 | h1
    · left
      have := congrArg (· * u) h1
      simpa [mul_assoc, inv_mul_cancel, mul_one] using this
    · right; left
      have := congrArg (· * u) h1
      have h2 : v = u ^ 2 * u := by simpa [mul_assoc, inv_mul_cancel, mul_one] using this
      rw [h2, ← pow_succ]
    · right; right; left
      have := congrArg (· * u) h1
      have h2 : v = t * u := by simpa [mul_assoc, inv_mul_cancel, mul_one] using this
      rw [h2, ← hct]
    · right; right; right
      have := congrArg (· * u) h1
      have h2 : v = u ^ 2 * t * u := by simpa [mul_assoc, inv_mul_cancel, mul_one] using this
      rw [h2, mul_assoc, ← hct, ← mul_assoc, ← pow_succ]
  have hu3_ne_u : u ^ 3 ≠ u := by
    intro h'
    apply h.z_ne_one
    apply mul_left_cancel (a := u)
    calc u * u ^ 2 = u ^ 3 := by rw [← pow_succ']
      _ = u := h'
      _ = u * 1 := by rw [mul_one]
  have hut_tu2 : (u * t) * (t * u ^ 2) = u ^ 3 := by
    rw [mul_assoc, ← mul_assoc t t (u ^ 2), show t * t = 1 from by rw [← pow_two, h.t_sq],
        one_mul, ← pow_succ']
  have hsq3 : (u ^ 3 * t) ^ 3 = u * t := by
    rw [(hcu.pow_left 3).mul_pow 3]
    rw [show (u ^ 3) ^ 3 = u from by
          rw [← pow_mul, show (3 : ℕ) * 3 = 8 + 1 from rfl, pow_succ,
              show (8 : ℕ) = 4 * 2 from rfl, pow_mul, h.u_pow_four, one_pow, one_mul]]
    rw [show t ^ 3 = t from by
          rw [show (3 : ℕ) = 2 + 1 from rfl, pow_succ, h.t_sq, one_mul]]
  have hv_final : v = u ∨ v = u ^ 3 := by
    rcases hv_cases with h1 | h1 | h1 | h1
    · exact Or.inl h1
    · exact Or.inr h1
    · exfalso
      have hconj : n * v * n⁻¹ = u ^ 3 := by
        calc n * v * n⁻¹ = n * (u * t) * n⁻¹ := by rw [h1]
          _ = (n * u * n⁻¹) * (n * t * n⁻¹) := by group
          _ = v * (t * u ^ 2) := by rw [hnt', ← hv_def]
          _ = (u * t) * (t * u ^ 2) := by rw [h1]
          _ = u ^ 3 := by rw [hut_tu2]
      have h2 : u = u ^ 3 := by
        calc u = n * v * n⁻¹ := hnv.symm
          _ = u ^ 3 := hconj
      exact h.z_ne_one (by
        apply mul_left_cancel (a := u)
        calc u * u ^ 2 = u ^ 3 := by rw [← pow_succ']
          _ = u := h2.symm
          _ = u * 1 := by rw [mul_one])
    · exfalso
      have hconj : n * v * n⁻¹ = u ^ 3 := by
        calc n * v * n⁻¹ = n * (u ^ 3 * t) * n⁻¹ := by rw [h1]
          _ = (n * u ^ 3 * n⁻¹) * (n * t * n⁻¹) := by group
          _ = (n * u * n⁻¹) ^ 3 * (t * u ^ 2) := by rw [hnt', ← conj_pow]
          _ = v ^ 3 * (t * u ^ 2) := by rw [← hv_def]
          _ = (u ^ 3 * t) ^ 3 * (t * u ^ 2) := by rw [h1]
          _ = (u * t) * (t * u ^ 2) := by rw [hsq3]
          _ = u ^ 3 := by rw [hut_tu2]
      have h2 : u = u ^ 3 := by
        calc u = n * v * n⁻¹ := hnv.symm
          _ = u ^ 3 := hconj
      exact h.z_ne_one (by
        apply mul_left_cancel (a := u)
        calc u * u ^ 2 = u ^ 3 := by rw [← pow_succ']
          _ = u := h2.symm
          _ = u * 1 := by rw [mul_one])
  have hcoord_ut : L12Coord S t (u * t) := aor_l12_coord_mul_t h
  let u₀ : S := if v = u then u else u * t
  have hu₀_cases : u₀ = u ∨ u₀ = u * t := by
    by_cases hvu : v = u
    · left
      change (if v = u then u else u * t) = u
      rw [if_pos hvu]
    · right
      change (if v = u then u else u * t) = u * t
      rw [if_neg hvu]
  have h₀ : L12Coord S t u₀ := by
    rcases hu₀_cases with hu | hu
    · rw [hu]; exact h
    · rw [hu]; exact hcoord_ut
  have hu₀_comm : u₀ * t = t * u₀ := by
    rcases hu₀_cases with hu | hu
    · rw [hu]; exact h.comm
    · rw [hu]; exact hcoord_ut.comm
  have hnu₀ : n * u₀ = u₀ * n := by
    by_cases hvu : v = u
    · have hu0 : u₀ = u := by
        change (if v = u then u else u * t) = u
        rw [if_pos hvu]
      rw [hu0]
      have hconj : n * u * n⁻¹ = u := by rw [← hv_def]; exact hvu
      have := congrArg (· * n) hconj
      simpa [mul_assoc, mul_inv_cancel, mul_one] using this
    · have hv3 : v = u ^ 3 := by
        rcases hv_final with hh | hh
        · exact absurd hh hvu
        · exact hh
      have hu0 : u₀ = u * t := by
        change (if v = u then u else u * t) = u * t
        rw [if_neg hvu]
      rw [hu0]
      have hconj : n * (u * t) * n⁻¹ = u * t := by
        calc n * (u * t) * n⁻¹
            = (n * u * n⁻¹) * (n * t * n⁻¹) := by group
          _ = v * (t * u ^ 2) := by rw [hnt', ← hv_def]
          _ = u ^ 3 * (t * u ^ 2) := by rw [hv3]
          _ = u * t := by
                rw [hz t, ← mul_assoc, ← pow_add, show (3 : ℕ) + 2 = 4 + 1 from rfl,
                    pow_succ, h.u_pow_four, one_mul]
      have := congrArg (· * n) hconj
      simpa [mul_assoc, mul_inv_cancel, mul_one] using this
  have hnu₀_conj : n * u₀ * n⁻¹ = u₀ := by
    rw [hnu₀, mul_assoc, mul_inv_cancel, mul_one]
  have hnu2_inv : n⁻¹ * u ^ 2 * n = u ^ 2 := by
    rw [hz n⁻¹, mul_assoc, inv_mul_cancel, mul_one]
  have hnt_inv : n⁻¹ * t * n = u ^ 2 * t := by
    have h1 : t = (n⁻¹ * t * n) * (n⁻¹ * u ^ 2 * n) := by
      calc t = n⁻¹ * (n * t * n⁻¹) * n := by group
        _ = n⁻¹ * (t * u ^ 2) * n := by rw [hnt']
        _ = (n⁻¹ * t * n) * (n⁻¹ * u ^ 2 * n) := by group
    have key : t = (n⁻¹ * t * n) * u ^ 2 :=
      h1.trans (congrArg (fun x => (n⁻¹ * t * n) * x) hnu2_inv)
    have h4 : ((n⁻¹ * t * n) * u ^ 2) * u ^ 2 = n⁻¹ * t * n := by
      have hzsq : (u ^ 2) * (u ^ 2) = 1 := by rw [← pow_two]; exact h.z_sq
      calc ((n⁻¹ * t * n) * u ^ 2) * u ^ 2
          = (n⁻¹ * t * n) * ((u ^ 2) * (u ^ 2)) := by rw [mul_assoc]
        _ = (n⁻¹ * t * n) * 1 := by rw [hzsq]
        _ = n⁻¹ * t * n := by rw [mul_one]
    have h3 : t * u ^ 2 = n⁻¹ * t * n := (congrArg (· * u ^ 2) key).trans h4
    rw [← h3, hz t]
  have hNcomm : ∀ m ∈ L12N t, m * u₀ = u₀ * m := by
    intro m hm
    by_cases hmt : m * t = t * m
    · exact L12Coord.R_comm h hmt hu₀_comm
    · have hmz : m * t * m⁻¹ = t * u ^ 2 := by
        rcases aor_l12_N_conj hS h hnc hm with h' | h'
        · exfalso; apply hmt
          have := congrArg (· * m) h'
          rwa [mul_assoc, inv_mul_cancel, mul_one] at this
        · exact h'
      have hr_comm : (n⁻¹ * m) * t = t * (n⁻¹ * m) := by
        have hconj : (n⁻¹ * m) * t * (n⁻¹ * m)⁻¹ = t := by
          calc (n⁻¹ * m) * t * (n⁻¹ * m)⁻¹
              = n⁻¹ * (m * t * m⁻¹) * n := by group
            _ = n⁻¹ * (t * u ^ 2) * n := by rw [hmz]
            _ = (n⁻¹ * t * n) * (n⁻¹ * u ^ 2 * n) := by group
            _ = (u ^ 2 * t) * u ^ 2 := by rw [hnt_inv, hnu2_inv]
            _ = t := by
                  rw [mul_assoc, hz t, ← mul_assoc, ← pow_add,
                      show (2 : ℕ) + 2 = 4 from rfl, h.u_pow_four, one_mul]
        have := congrArg (· * (n⁻¹ * m)) hconj
        simpa [mul_assoc, mul_inv_cancel, mul_one] using this
      have hr_u₀ : (n⁻¹ * m) * u₀ = u₀ * (n⁻¹ * m) :=
        L12Coord.R_comm h hr_comm hu₀_comm
      calc m * u₀ = n * (n⁻¹ * m) * u₀ := by group
        _ = n * ((n⁻¹ * m) * u₀) := by group
        _ = n * (u₀ * (n⁻¹ * m)) := by rw [hr_u₀]
        _ = (n * u₀) * (n⁻¹ * m) := by group
        _ = (u₀ * n) * (n⁻¹ * m) := by rw [hnu₀]
        _ = u₀ * m := by group
  have hcenter : ∀ w ∈ L12N t, (∀ m ∈ L12N t, m * w = w * m) →
      w ∈ Subgroup.zpowers u₀ := by
    intro w _ hcw
    have ht_R : t ∈ L12R t := by
      change t ∈ Subgroup.centralizer ({t} : Set S)
      rw [Subgroup.mem_centralizer_iff]
      intro x hx
      rw [Set.mem_singleton_iff] at hx
      rw [hx]
    have htN : t ∈ L12N t := Subgroup.le_normalizer ht_R
    have hwt : w * t = t * w := (hcw t htN).symm
    obtain ⟨i, j, hwij⟩ := h.cent w hwt
    have hex : ∃ m : ℕ, w = u₀ ^ i * t ^ m := by
      rcases hu₀_cases with hu | hu
      · exact ⟨j, by rw [hu, hwij]⟩
      · refine ⟨i + j, ?_⟩
        rw [hu, hwij, hcu.mul_pow i, mul_assoc, ← pow_add]
        congr 1
        have he : i + (i + j) = 2 * i + j := by rw [← Nat.add_assoc, ← two_mul]
        rw [he, pow_add, pow_mul, h.t_sq, one_pow, one_mul]
    obtain ⟨m, hwm⟩ := hex
    have hconj_w : n * w * n⁻¹ = w * (u ^ 2) ^ m := by
      rw [hwm]
      calc n * (u₀ ^ i * t ^ m) * n⁻¹
          = (n * u₀ ^ i * n⁻¹) * (n * t ^ m * n⁻¹) := by group
        _ = (n * u₀ * n⁻¹) ^ i * (n * t * n⁻¹) ^ m := by simp only [← conj_pow]
        _ = u₀ ^ i * (t * u ^ 2) ^ m := by rw [hnu₀_conj, hnt']
        _ = u₀ ^ i * (t ^ m * (u ^ 2) ^ m) := by
              rw [(show Commute t (u ^ 2) from hz t).mul_pow m]
        _ = u₀ ^ i * t ^ m * (u ^ 2) ^ m := by rw [mul_assoc]
    have hwm_eq : w * (u ^ 2) ^ m = w := by
      rw [← hconj_w, hcw n hn, mul_assoc, mul_inv_cancel, mul_one]
    have hzm : (u ^ 2) ^ m = 1 := by
      apply mul_left_cancel (a := w)
      rw [mul_one]
      exact hwm_eq
    have h2m : 2 ∣ m := by
      have hordz : orderOf (u ^ 2) = 2 := orderOf_eq_prime (p := 2) h.z_sq h.z_ne_one
      rw [← hordz]
      exact orderOf_dvd_iff_pow_eq_one.mpr hzm
    have htm : t ^ m = 1 := by
      rw [← orderOf_dvd_iff_pow_eq_one, h.ord_t]
      exact h2m
    have hwfin : w = u₀ ^ i := by rw [hwm, htm, mul_one]
    rw [hwfin]
    exact Subgroup.npow_mem_zpowers u₀ i
  refine ⟨u₀, h₀, aor_l12_z_central hS h₀ hnc, hNcomm, ?_, ?_,
    aor_l12_N_card hS h₀ hnc, hcenter⟩
  · intro m hm
    exact aor_l12_N_conj hS h₀ hnc hm
  · intro x hx
    exact aor_l12_mem_N h₀ (aor_l12_z_central hS h₀ hnc) hx

end CFSG.OddStandard.SmallF3.Omega
