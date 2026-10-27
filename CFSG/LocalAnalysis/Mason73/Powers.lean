module

public import CFSG.LocalAnalysis.Mason73.TableIII
public import Mathlib.GroupTheory.Commutator.Basic
import Mathlib.Tactic.LinearCombination

public section

namespace CFSG.LocalAnalysis.Mason73

open CFSG.CGT.Stroth77.L4Sylow CFSG.GH74.GLS.Stage1.Thm3.Sec8 Equiv Subgroup
open scoped commutatorElement

variable {n : ℕ}

local macro "lc2 " h:ident h':ident : tactic => `(tactic| first
  | ring1
  | linear_combination $h:ident | linear_combination -$h:ident
  | linear_combination 2 * $h:ident | linear_combination -2 * $h:ident
  | linear_combination $h':ident | linear_combination -$h':ident
  | linear_combination $h:ident + $h':ident | linear_combination $h:ident - $h':ident
  | linear_combination -$h:ident + $h':ident | linear_combination -$h:ident - $h':ident
  | linear_combination 2 * $h:ident + $h':ident | linear_combination 2 * $h:ident - $h':ident
  | linear_combination -2 * $h:ident + $h':ident | linear_combination -2 * $h:ident - $h':ident)

theorem piT_mul_self (g : L4Model n) : piT (g * g) = 1 ∨ piT (g * g) = zP := by
  rw [map_mul]
  generalize piT g = π
  revert π
  decide

theorem tT_mul_uT_mul_self (hn : 2 ≤ n) :
    tT (n := n) (by omega) * uT (by omega) * (tT (by omega) * uT (by omega)) =
      uvT (by omega) := by
  rw [tT, uT, uvT, el_hv_mul, el_hv_mul, el_hv_eq_el_hv_iff' hn]
  decide

theorem mul_self_ne_of_piT_s23 {μ : L4Model n} (hπ : piT μ = s23 ∨ piT μ = s01)
    (g : L4Model n) : g * g ≠ μ := by
  intro h
  have := piT_mul_self g
  rw [h] at this
  rcases hπ with h' | h' <;> rw [h'] at this <;> revert this <;> decide

theorem exists_mul_self_eq_x1T (hn : 3 ≤ n) :
    ∃ c ∈ centralizer {tT (n := n) (by omega)}, c * c = x1T (by omega) := by
  have hc : detSum (fun i => ss n * (![-1, 1, -1, 1] : Fin 4 → ZMod (2 ^ n)) i) 1 := by
    rw [detSum_one_iff, Fin.sum_univ_four]
    simp only [Matrix.cons_val]
    ring
  have h4 := four_mul_ss hn
  have hh2 := hh_add_hh (n := n) (by omega)
  refine ⟨el _ 1 hc, ?_, ?_⟩
  · rw [mem_centralizer_singleton_iff, tT]
    refine ((el_comm_diag_iff (by omega) _ hc).2 ?_).symm
    rw [pv_tP]
    refine isConst_of_eq_four 0 ?_ ?_ ?_ ?_ <;> simp only [Pi.sub_apply, Matrix.cons_val] <;>
      ring1
  · rw [el_mul, x1T, el_eq_el_iff (by omega)]
    refine ⟨mul_one _, isConst_of_eq_four (-(2 * ss n)) ?_ ?_ ?_ ?_⟩ <;>
      simp only [Pi.sub_apply, Pi.add_apply, OneMemClass.coe_one, pv_one, hv, Matrix.cons_val,
        Nat.cast_one, Nat.cast_zero, mul_one, mul_zero] <;>
      first | ring1 | linear_combination h4 + hh2 | linear_combination -h4 - hh2 |
        linear_combination h4 - hh2 | linear_combination -h4 + hh2

theorem exists_pow_four_eq_zT_of_piT_s23 (hn : 3 ≤ n) {μ : L4Model n}
    (hπ : piT μ = s23 ∨ piT μ = s01) : ∃ c ∈ centralizer {μ}, c ^ 4 = zT (by omega) := by
  obtain ⟨m, π, hm, rfl⟩ := exists_eq_el μ
  rw [piT_el] at hπ
  have h4 := four_mul_ss hn
  have hh2 := hh_add_hh (n := n) (by omega)
  rcases hπ with rfl | rfl
  · have hc : detSum (fun i => ss n * (![2, 0, -1, -1] : Fin 4 → ZMod (2 ^ n)) i) 1 := by
      rw [detSum_one_iff, Fin.sum_univ_four]
      simp only [Matrix.cons_val]
      ring
    refine ⟨el _ 1 hc, ?_, ?_⟩
    · rw [mem_centralizer_singleton_iff]
      refine ((el_comm_diag_iff (by omega) _ hc).2 ?_).symm
      rw [pv_s23]
      refine isConst_of_eq_four 0 ?_ ?_ ?_ ?_ <;> simp only [Pi.sub_apply, Matrix.cons_val] <;>
        ring1
    · rw [el_one_pow, zT, el_eq_el_iff (by omega)]
      refine ⟨rfl, isConst_of_eq_four (hh n) ?_ ?_ ?_ ?_⟩ <;>
        simp only [Pi.sub_apply, Pi.smul_apply, hv, Matrix.cons_val, nsmul_eq_mul, Pi.mul_apply,
          Pi.natCast_apply, Pi.ofNat_apply, Nat.cast_one, Nat.cast_zero, Nat.cast_ofNat, mul_one,
          mul_zero] <;>
        lc2 h4 hh2
  · have hc : detSum (fun i => ss n * (![1, 1, -2, 0] : Fin 4 → ZMod (2 ^ n)) i) 1 := by
      rw [detSum_one_iff, Fin.sum_univ_four]
      simp only [Matrix.cons_val]
      ring
    refine ⟨el _ 1 hc, ?_, ?_⟩
    · rw [mem_centralizer_singleton_iff]
      refine ((el_comm_diag_iff (by omega) _ hc).2 ?_).symm
      rw [pv_s01]
      refine isConst_of_eq_four 0 ?_ ?_ ?_ ?_ <;> simp only [Pi.sub_apply, Matrix.cons_val] <;>
        ring1
    · rw [el_one_pow, zT, el_eq_el_iff (by omega)]
      refine ⟨rfl, isConst_of_eq_four 0 ?_ ?_ ?_ ?_⟩ <;>
        simp only [Pi.sub_apply, Pi.smul_apply, hv, Matrix.cons_val, nsmul_eq_mul, Pi.mul_apply,
          Pi.natCast_apply, Pi.ofNat_apply, Nat.cast_one, Nat.cast_zero, Nat.cast_ofNat, mul_one,
          mul_zero] <;>
        lc2 h4 hh2

theorem R0_mul_self_cases : ∀ π : Fin81.R0, π * π = 1 →
    π = 1 ∨ π = s23 ∨ π = s01 ∨ π = zP ∨ π = tP ∨ π = tzP := by
  decide

theorem isConst_of_el_comm_zP (hn : 2 ≤ n) {d m : Fin 4 → ZMod (2 ^ n)} {σ : Fin81.R0}
    (hd : detSum d σ) (hm : detSum m zP) (hc : el d σ hd * el m zP hm = el m zP hm * el d σ hd) :
    IsConst ((m + pv (zP : Perm (Fin 4)) d) - (d + pv (σ : Perm (Fin 4)) m)) := by
  rw [el_mul, el_mul, el_eq_el_iff hn] at hc
  exact hc.2

theorem mul_self_ne_x1T_of_piT_zP (hn : 3 ≤ n) {μ c : L4Model n} (h2 : μ * μ = 1)
    (hπ : piT μ = zP) (hc : c ∈ centralizer {μ}) : c * c ≠ x1T (by omega) := by
  obtain ⟨m, π, hm, rfl⟩ := exists_eq_el μ
  rw [piT_el] at hπ
  subst hπ
  obtain ⟨d, σ, hd, rfl⟩ := exists_eq_el c
  rw [mem_centralizer_singleton_iff] at hc
  have M := (el_zP_mul_self (by omega) hm h2).1
  have hh0 := natCast_two_pow_ne_zero (n := n) (by omega)
  intro hsq
  rw [el_mul, x1T, el_eq_el_iff (by omega)] at hsq
  obtain ⟨hσ, hK⟩ := hsq
  rcases R0_mul_self_cases σ hσ with rfl | rfl | rfl | rfl | rfl | rfl
  · have K := (el_comm_diag_iff (by omega) hm hd).1 hc.symm
    rw [pv_zP] at K
    have K01 := K 0 1
    have hK01 := hK 0 1
    simp only [Pi.sub_apply, Pi.add_apply, OneMemClass.coe_one, pv_one, hv, Matrix.cons_val,
      Nat.cast_one, Nat.cast_zero, mul_one, mul_zero] at K01 hK01
    exact hh0 (by linear_combination hK01 - K01)
  · have hK23 := hK 2 3
    rw [pv_s23] at hK23
    simp only [Pi.sub_apply, Pi.add_apply, hv, Matrix.cons_val, Nat.cast_one, Nat.cast_zero,
      mul_one, mul_zero] at hK23
    exact hh0 (by linear_combination hK23)
  · have hK01 := hK 0 1
    rw [pv_s01] at hK01
    simp only [Pi.sub_apply, Pi.add_apply, hv, Matrix.cons_val, Nat.cast_one, Nat.cast_zero,
      mul_one, mul_zero] at hK01
    exact hh0 (by linear_combination hK01)
  · have hK01 := hK 0 1
    rw [pv_zP] at hK01
    simp only [Pi.sub_apply, Pi.add_apply, hv, Matrix.cons_val, Nat.cast_one, Nat.cast_zero,
      mul_one, mul_zero] at hK01
    exact hh0 (by linear_combination hK01)
  · have K := isConst_of_el_comm_zP (by omega) hd hm hc
    rw [pv_zP, pv_tP] at K
    have C01 := K 0 1
    have C02 := K 0 2
    have hK01 := hK 0 1
    rw [pv_tP] at hK01
    simp only [Pi.sub_apply, Pi.add_apply, hv, Matrix.cons_val, Nat.cast_one, Nat.cast_zero,
      mul_one, mul_zero] at C01 C02 hK01
    exact hh0 (by linear_combination hK01 - M - C01 + C02)
  · have hK12 := hK 1 2
    rw [pv_tzP] at hK12
    simp only [Pi.sub_apply, Pi.add_apply, hv, Matrix.cons_val, Nat.cast_one, Nat.cast_zero,
      mul_one, mul_zero] at hK12
    exact hh0 (by linear_combination -hK12)

theorem mul_self_ne_y1T_of_piT_zP (hn : 3 ≤ n) {μ c : L4Model n} (h2 : μ * μ = 1)
    (hπ : piT μ = zP) (hc : c ∈ centralizer {μ}) : c * c ≠ y1T (by omega) := by
  obtain ⟨m, π, hm, rfl⟩ := exists_eq_el μ
  rw [piT_el] at hπ
  subst hπ
  obtain ⟨d, σ, hd, rfl⟩ := exists_eq_el c
  rw [mem_centralizer_singleton_iff] at hc
  have M := (el_zP_mul_self (by omega) hm h2).1
  have hh0 := natCast_two_pow_ne_zero (n := n) (by omega)
  intro hsq
  rw [el_mul, y1T, el_eq_el_iff (by omega)] at hsq
  obtain ⟨hσ, hK⟩ := hsq
  rcases R0_mul_self_cases σ hσ with rfl | rfl | rfl | rfl | rfl | rfl
  · have K := (el_comm_diag_iff (by omega) hm hd).1 hc.symm
    rw [pv_zP] at K
    have K01 := K 0 1
    have hK01 := hK 0 1
    simp only [Pi.sub_apply, Pi.add_apply, OneMemClass.coe_one, pv_one, hv, Matrix.cons_val,
      Nat.cast_one, Nat.cast_zero, mul_one, mul_zero] at K01 hK01
    exact hh0 (by linear_combination hK01 - K01)
  · have hK23 := hK 2 3
    rw [pv_s23] at hK23
    simp only [Pi.sub_apply, Pi.add_apply, hv, Matrix.cons_val, Nat.cast_one, Nat.cast_zero,
      mul_one, mul_zero] at hK23
    exact hh0 (by linear_combination -hK23)
  · have hK01 := hK 0 1
    rw [pv_s01] at hK01
    simp only [Pi.sub_apply, Pi.add_apply, hv, Matrix.cons_val, Nat.cast_one, Nat.cast_zero,
      mul_one, mul_zero] at hK01
    exact hh0 (by linear_combination hK01)
  · have hK01 := hK 0 1
    rw [pv_zP] at hK01
    simp only [Pi.sub_apply, Pi.add_apply, hv, Matrix.cons_val, Nat.cast_one, Nat.cast_zero,
      mul_one, mul_zero] at hK01
    exact hh0 (by linear_combination hK01)
  · have hK02 := hK 0 2
    rw [pv_tP] at hK02
    simp only [Pi.sub_apply, Pi.add_apply, hv, Matrix.cons_val, Nat.cast_one, Nat.cast_zero,
      mul_one, mul_zero] at hK02
    exact hh0 (by linear_combination hK02)
  · have K := isConst_of_el_comm_zP (by omega) hd hm hc
    rw [pv_zP, pv_tzP] at K
    have C01 := K 0 1
    have C03 := K 0 3
    have hK01 := hK 0 1
    rw [pv_tzP] at hK01
    simp only [Pi.sub_apply, Pi.add_apply, hv, Matrix.cons_val, Nat.cast_one, Nat.cast_zero,
      mul_one, mul_zero] at C01 C03 hK01
    exact hh0 (by linear_combination hK01 - M - C01 + C03)

theorem patFix_zP_cases : ∀ p : Fin 2 × Fin 2 × Fin 2,
    PatFix ((zP : Fin81.R0) : Perm (Fin 4)) (pat p) →
      p = (0, 0, 0) ∨ p = (0, 1, 1) ∨ p = (1, 0, 1) ∨ p = (1, 1, 0) := by
  decide

theorem mul_self_eq_zT_of_piT_zP (hn : 3 ≤ n) {μ c : L4Model n} (h2 : μ * μ = 1)
    (hπ : piT μ = zP) (hc : c ∈ centralizer {μ}) (hA : c * c ∈ A n) (hc1 : c * c ≠ 1)
    (hc2 : c * c * (c * c) = 1) : c * c = zT (by omega) := by
  obtain ⟨p, hp⟩ := exists_eq_omegaEl hn hA hc2
  have hc' := mem_centralizer_singleton_iff.1 hc
  have hcomm : μ * omegaEl hn p = omegaEl hn p * μ := by
    rw [← hp]
    calc μ * (c * c) = μ * c * c := by group
      _ = c * μ * c := by rw [hc']
      _ = c * (μ * c) := by group
      _ = c * (c * μ) := by rw [hc']
      _ = c * c * μ := by group
  have hpat := patFix_of_comm hn hcomm
  rw [hπ] at hpat
  rcases patFix_zP_cases p hpat with rfl | rfl | rfl | rfl
  · exact absurd (hp.trans (omegaEl_zero hn)) hc1
  · rw [hp, zT_eq_omegaEl hn]
  · exact absurd (hp.trans (x1T_eq_omegaEl hn).symm) (mul_self_ne_x1T_of_piT_zP hn h2 hπ hc)
  · exact absurd (hp.trans (y1T_eq_omegaEl hn).symm) (mul_self_ne_y1T_of_piT_zP hn h2 hπ hc)

theorem isConj_mul_of_mem_center {G : Type*} [Group G] {a b c : G} (h : IsConj a b)
    (hc : c ∈ Subgroup.center G) : IsConj (a * c) (b * c) := by
  obtain ⟨g, rfl⟩ := isConj_iff.mp h
  rw [isConj_iff]
  refine ⟨g, ?_⟩
  have hgc : g⁻¹ * c = c * g⁻¹ := Subgroup.mem_center_iff.mp hc g⁻¹
  calc g * (a * c) * g⁻¹ = g * a * (c * g⁻¹) := by group
    _ = g * a * (g⁻¹ * c) := by rw [hgc]
    _ = g * a * g⁻¹ * c := by group

theorem mul_zT_mul_self (hn : 2 ≤ n) {μ : L4Model n} (h2 : μ * μ = 1) :
    μ * zT (by omega) * (μ * zT (by omega)) = 1 := by
  have hz := zT_mem_center (n := n) hn
  have hzz : zT (n := n) (by omega) * zT (by omega) = 1 := by
    rw [← pow_two, ← orderOf_dvd_iff_pow_eq_one, orderOf_zT hn]
  have hμz : μ * zT (n := n) (by omega) = zT (by omega) * μ := Subgroup.mem_center_iff.mp hz μ
  calc μ * zT (n := n) (by omega) * (μ * zT (by omega)) =
        μ * (zT (by omega) * μ) * zT (by omega) := by group
    _ = μ * (μ * zT (by omega)) * zT (by omega) := by rw [hμz]
    _ = μ * μ * (zT (by omega) * zT (by omega)) := by group
    _ = 1 := by rw [h2, hzz, one_mul]

theorem isConj_uT_mul_zT (hn : 3 ≤ n) :
    IsConj (uT (n := n) (by omega) * zT (by omega)) (uT (by omega)) := by
  have hd : detSum (hv n ![2, 1, 0, 0]) s23 :=
    detSum_hv_odd (by omega) (sgnH_s23 (by omega)) (by decide)
  have he : uT (n := n) (by omega) * zT (by omega) = el (hv n ![2, 1, 0, 0]) s23 hd := by
    rw [uT, zT, el_hv_mul, el_hv_eq_el_hv_iff' (by omega)]
    decide
  have h2 := mul_zT_mul_self (n := n) (by omega) (uT_mul_self (by omega))
  rw [he] at h2 ⊢
  refine isConj_el_s23_uT hn hd h2 ?_
  have hh2 := hh_add_hh (n := n) (by omega)
  simp only [hv, Matrix.cons_val, Nat.cast_one, Nat.cast_zero, Nat.cast_ofNat, mul_one, mul_zero]
  linear_combination -hh2

theorem uw1T_mul_self (hn : 3 ≤ n) : uw1T hn * uw1T hn = 1 := by
  rw [uw1T, el_mul, ← el_zero_one, el_eq_el_iff (by omega), pv_s23]
  refine ⟨by decide, isConst_of_eq_four (-(ss n + ss n)) ?_ ?_ ?_ ?_⟩ <;>
    simp only [Pi.sub_apply, Pi.add_apply, Pi.zero_apply, Matrix.cons_val] <;> ring1

theorem uvxyT_mul_self (hn : 2 ≤ n) : uvxyT (n := n) (by omega) * uvxyT (by omega) = 1 := by
  rw [uvxyT, el_mul, ← el_zero_one, el_eq_el_iff hn, pv_zP]
  have hh2 := hh_add_hh (n := n) (by omega)
  refine ⟨by decide, isConst_of_eq_four (-hh n) ?_ ?_ ?_ ?_⟩ <;>
    simp only [Pi.sub_apply, Pi.add_apply, Pi.zero_apply, Matrix.cons_val] <;>
    first | ring1 | linear_combination hh2 | linear_combination -hh2

theorem txT_mul_self (hn : 2 ≤ n) : txT n * txT n = 1 := by
  rw [txT, el_mul, ← el_zero_one, el_eq_el_iff hn, pv_tP]
  refine ⟨by decide, isConst_of_eq_four 0 ?_ ?_ ?_ ?_⟩ <;>
    simp only [Pi.sub_apply, Pi.add_apply, Pi.zero_apply, Matrix.cons_val] <;> ring1

theorem isConj_uw1T_mul_zT (hn : 3 ≤ n) : IsConj (uw1T hn * zT (by omega)) (uw1T hn) := by
  have hd : detSum (fun i => ss n + hv n ![1, 1, 0, 0] i) s23 := by
    rw [detSum_s23_iff (by omega)]
    simp only [hv, Matrix.cons_val, Nat.cast_one, Nat.cast_zero, mul_one, mul_zero]
    linear_combination four_mul_ss hn + 2 * hh_add_hh (n := n) (by omega)
  have he : uw1T hn * zT (by omega) = el (fun i => ss n + hv n ![1, 1, 0, 0] i) s23 hd := by
    rw [uw1T, zT, el_mul, el_eq_el_iff (by omega), pv_s23]
    refine ⟨mul_one _, isConst_of_eq_four 0 ?_ ?_ ?_ ?_⟩ <;>
      simp only [Pi.sub_apply, Pi.add_apply, hv, Matrix.cons_val, Nat.cast_one, Nat.cast_zero,
        mul_one, mul_zero] <;> ring1
  have h2 := mul_zT_mul_self (n := n) (by omega) (uw1T_mul_self hn)
  rw [he] at h2 ⊢
  exact isConj_el_s23_uw1T hn hd h2 (by simp [hv])

theorem isConj_uvT_mul_zT (hn : 3 ≤ n) :
    IsConj (uvT (n := n) (by omega) * zT (by omega)) (uvT (by omega)) := by
  have hd : detSum (hv n ![2, 1, 0, 1]) zP := detSum_hv_even (by omega) (by decide) (by decide)
  have he : uvT (n := n) (by omega) * zT (by omega) = el (hv n ![2, 1, 0, 1]) zP hd := by
    rw [uvT, zT, el_hv_mul, el_hv_eq_el_hv_iff' (by omega)]
    decide
  have h2 := mul_zT_mul_self (n := n) (by omega) (uvT_mul_self (by omega))
  rw [he] at h2 ⊢
  refine isConj_el_zP_uvT hn hd h2 (k := hh n) ?_
  simp only [hv, Matrix.cons_val, Nat.cast_one, Nat.cast_zero, Nat.cast_ofNat, mul_one, mul_zero]
  ring

theorem isConj_uvxyT_mul_zT (hn : 3 ≤ n) :
    IsConj (uvxyT (n := n) (by omega) * zT (by omega)) (uvxyT (by omega)) := by
  have hd : detSum (![hh n + hh n, hh n, 1, hh n - 1] : Fin 4 → ZMod (2 ^ n)) zP := by
    rw [detSum_even_iff (by decide)]
    simp only [Matrix.cons_val]
    linear_combination 2 * hh_add_hh (n := n) (by omega)
  have he : uvxyT (n := n) (by omega) * zT (by omega) =
      el (![hh n + hh n, hh n, 1, hh n - 1] : Fin 4 → ZMod (2 ^ n)) zP hd := by
    rw [uvxyT, zT, el_mul, el_eq_el_iff (by omega), pv_zP]
    refine ⟨mul_one _, isConst_of_eq_four 0 ?_ ?_ ?_ ?_⟩ <;>
      simp only [Pi.sub_apply, Pi.add_apply, hv, Matrix.cons_val, Nat.cast_one, Nat.cast_zero,
        mul_one, mul_zero] <;> ring1
  have h2 := mul_zT_mul_self (n := n) (by omega) (uvxyT_mul_self (by omega))
  rw [he] at h2 ⊢
  refine isConj_el_zP_uvxyT hn hd h2 (k := hh n - 1) ?_
  simp only [Matrix.cons_val]
  ring

theorem isConj_tT_mul_zT (hn : 3 ≤ n) :
    IsConj (tT (n := n) (by omega) * zT (by omega)) (tT (by omega)) := by
  have hd : detSum (hv n ![0, 0, 1, 1]) tP := detSum_hv_even (by omega) (by decide) (by decide)
  have he : tT (n := n) (by omega) * zT (by omega) = el (hv n ![0, 0, 1, 1]) tP hd := by
    rw [tT, zT, el_hv_mul, el_hv_eq_el_hv_iff' (by omega)]
    decide
  have h2 := mul_zT_mul_self (n := n) (by omega) (tT_mul_self (by omega))
  rw [he] at h2 ⊢
  refine isConj_el_tP_tT hn hd h2 (k := 0) ?_
  simp [hv]

theorem isConj_txT_mul_zT (hn : 3 ≤ n) : IsConj (txT n * zT (by omega)) (txT n) := by
  have hd : detSum (![-1, 0, 1 + hh n, hh n] : Fin 4 → ZMod (2 ^ n)) tP := by
    rw [detSum_even_iff (by decide)]
    simp only [Matrix.cons_val]
    linear_combination hh_add_hh (n := n) (by omega)
  have he : txT n * zT (by omega) = el (![-1, 0, 1 + hh n, hh n] : Fin 4 → ZMod (2 ^ n)) tP hd := by
    rw [txT, zT, el_mul, el_eq_el_iff (by omega), pv_tP]
    refine ⟨mul_one _, isConst_of_eq_four 0 ?_ ?_ ?_ ?_⟩ <;>
      simp only [Pi.sub_apply, Pi.add_apply, hv, Matrix.cons_val, Nat.cast_one, Nat.cast_zero,
        mul_one, mul_zero] <;> ring1
  have h2 := mul_zT_mul_self (n := n) (by omega) (txT_mul_self (by omega))
  rw [he] at h2 ⊢
  refine isConj_el_tP_txT hn hd h2 (k := 0) ?_
  simp only [Matrix.cons_val]
  ring

theorem isConj_mul_zT (hn : 3 ≤ n) {μ : L4Model n} (hA : μ ∉ A n) (h2 : μ * μ = 1) :
    IsConj (μ * zT (by omega)) μ := by
  have hz := zT_mem_center (n := n) (by omega)
  have key : ∀ ρ : L4Model n, IsConj μ ρ → IsConj (ρ * zT (by omega)) ρ →
      IsConj (μ * zT (by omega)) μ := fun ρ h hρ =>
    ((isConj_mul_of_mem_center h hz).trans hρ).trans h.symm
  have hπ1 : piT μ ≠ 1 := fun h => hA (mem_A_iff.2 h)
  rcases piT_eq_of_mul_self h2 with hπ | hπ | hπ | hπ | hπ | hπ
  · exact absurd hπ hπ1
  · rcases isConj_uT_or_uw1T hn h2 (Or.inl hπ) with h | h
    · exact key _ h (isConj_uT_mul_zT hn)
    · exact key _ h (isConj_uw1T_mul_zT hn)
  · rcases isConj_uT_or_uw1T hn h2 (Or.inr hπ) with h | h
    · exact key _ h (isConj_uT_mul_zT hn)
    · exact key _ h (isConj_uw1T_mul_zT hn)
  · rcases isConj_uvT_or_uvxyT hn h2 hπ with h | h
    · exact key _ h (isConj_uvT_mul_zT hn)
    · exact key _ h (isConj_uvxyT_mul_zT hn)
  · rcases isConj_tT_or_txT hn h2 (Or.inl hπ) with h | h
    · exact key _ h (isConj_tT_mul_zT hn)
    · exact key _ h (isConj_txT_mul_zT hn)
  · rcases isConj_tT_or_txT hn h2 (Or.inr hπ) with h | h
    · exact key _ h (isConj_tT_mul_zT hn)
    · exact key _ h (isConj_txT_mul_zT hn)

theorem isConj_tT_mul_x1T (hn : 3 ≤ n) :
    IsConj (tT (n := n) (by omega) * x1T (by omega)) (tT (by omega)) := by
  have hd : detSum (hv n ![1, 0, 1, 0]) tP := detSum_hv_even (by omega) (by decide) (by decide)
  have he : tT (n := n) (by omega) * x1T (by omega) = el (hv n ![1, 0, 1, 0]) tP hd := by
    rw [tT, x1T, el_hv_mul, el_hv_eq_el_hv_iff' (by omega)]
    decide
  have h2 : el (hv n ![1, 0, 1, 0]) tP hd * el (hv n ![1, 0, 1, 0]) tP hd = 1 := by
    rw [el_hv_mul, one_eq_el_hv (by omega), el_hv_eq_el_hv_iff' (by omega)]
    decide
  rw [he]
  refine isConj_el_tP_tT hn hd h2 (k := -zL4 n) ?_
  simp only [hv, Matrix.cons_val, Nat.cast_one, Nat.cast_zero, mul_one, mul_zero]
  rw [← two_mul_zL4 (by omega)]
  ring

theorem isConj_txT_mul_x1T (hn : 3 ≤ n) : IsConj (txT n * x1T (by omega)) (txT n) := by
  have hd : detSum (![-1 + hh n, 0, 1 + hh n, 0] : Fin 4 → ZMod (2 ^ n)) tP := by
    rw [detSum_even_iff (by decide)]
    simp only [Matrix.cons_val]
    linear_combination hh_add_hh (n := n) (by omega)
  have he : txT n * x1T (by omega) =
      el (![-1 + hh n, 0, 1 + hh n, 0] : Fin 4 → ZMod (2 ^ n)) tP hd := by
    rw [txT, x1T, el_mul, el_eq_el_iff (by omega), pv_tP]
    refine ⟨mul_one _, isConst_of_eq_four 0 ?_ ?_ ?_ ?_⟩ <;>
      simp only [Pi.sub_apply, Pi.add_apply, hv, Matrix.cons_val, Nat.cast_one, Nat.cast_zero,
        mul_one, mul_zero] <;> ring1
  have h2 : el (![-1 + hh n, 0, 1 + hh n, 0] : Fin 4 → ZMod (2 ^ n)) tP hd *
      el (![-1 + hh n, 0, 1 + hh n, 0] : Fin 4 → ZMod (2 ^ n)) tP hd = 1 := by
    rw [el_mul, ← el_zero_one, el_eq_el_iff (by omega), pv_tP]
    have hh2 := hh_add_hh (n := n) (by omega)
    refine ⟨by decide, isConst_of_eq_four 0 ?_ ?_ ?_ ?_⟩ <;>
      simp only [Pi.sub_apply, Pi.add_apply, Pi.zero_apply, Matrix.cons_val] <;>
      first | ring1 | linear_combination hh2 | linear_combination -hh2
  rw [he]
  refine isConj_el_tP_txT hn hd h2 (k := -zL4 n) ?_
  simp only [Matrix.cons_val]
  rw [← two_mul_zL4 (by omega)]
  ring

@[expose] def A02 (n : ℕ) : Subgroup (L4Model n) where
  carrier := {g | ∃ (e : Fin 4 → ZMod (2 ^ n)) (h : detSum e 1), g = el e 1 h ∧ e 2 = e 0}
  one_mem' := ⟨0, detSum_zero_one, el_zero_one.symm, rfl⟩
  mul_mem' := by
    rintro _ _ ⟨e, he, rfl, he2⟩ ⟨f, hf, rfl, hf2⟩
    have hef : detSum (e + f) 1 := by
      rw [detSum_one_iff] at he hf ⊢
      simp only [Pi.add_apply]
      rw [Finset.sum_add_distrib, he, hf, add_zero]
    refine ⟨e + f, hef, ?_, ?_⟩
    · rw [el_mul]
      exact el_congr _ _ (by rw [OneMemClass.coe_one, pv_one]) (mul_one 1)
    · simp only [Pi.add_apply, he2, hf2]
  inv_mem' := by
    rintro _ ⟨e, he, rfl, he2⟩
    exact ⟨-e, detSum_neg he, el_one_inv he, by simp only [Pi.neg_apply, he2]⟩

theorem A02_le_A : A02 n ≤ A n := by
  rintro _ ⟨e, he, rfl, -⟩
  exact el_mem_A he |>.2 rfl

theorem commutatorElement_el (hn : 2 ≤ n) {d e : Fin 4 → ZMod (2 ^ n)} {σ τ : Fin81.R0}
    (hd : detSum d σ) (he : detSum e τ) (hστ : σ * τ = τ * σ) :
    ⁅el d σ hd, el e τ he⁆ = el (d + pv (σ : Perm (Fin 4)) e - (e + pv (τ : Perm (Fin 4)) d)) 1
      (by rw [detSum_one_iff]; simp only [Pi.sub_apply, Pi.add_apply]
          rw [Finset.sum_sub_distrib, Finset.sum_add_distrib, Finset.sum_add_distrib, sum_pv,
            sum_pv]; ring) := by
  rw [commutatorElement_def, mul_inv_eq_iff_eq_mul, mul_inv_eq_iff_eq_mul, el_mul, el_mul, el_mul,
    el_eq_el_iff hn]
  refine ⟨by rw [one_mul, hστ], ?_⟩
  refine isConst_of_forall_eq 0 fun i => ?_
  simp only [Pi.sub_apply, Pi.add_apply, OneMemClass.coe_one, pv_one, one_mul]
  ring

theorem pv_two_sub_pv_zero (hn : 2 ≤ n) {m f : Fin 4 → ZMod (2 ^ n)} {ρ σ : Fin81.R0}
    (hf : IsConst ((pv (tP : Perm (Fin 4)) f - f) - (pv (ρ : Perm (Fin 4)) m - m)))
    (hσ : σ * tP = tP * σ) :
    pv (σ : Perm (Fin 4)) f 2 - pv (σ : Perm (Fin 4)) f 0 = f 2 - f 0 +
      (pv ((σ * ρ : Fin81.R0) : Perm (Fin 4)) m - m) 0 - (pv (σ : Perm (Fin 4)) m - m) 0 -
      (pv (ρ : Perm (Fin 4)) m - m) 0 := by
  have key : ∀ π : Fin81.R0, π * tP = tP * π →
      π = 1 ∨ π = zP ∨ π = tP ∨ π = tzP := by decide
  rw [pv_tP] at hf
  have Q01 := hf 0 1
  have Q02 := hf 0 2
  have Q03 := hf 0 3
  rcases key σ hσ with rfl | rfl | rfl | rfl
  · simp [pv]
  · simp only [Pi.sub_apply, Matrix.cons_val] at Q01
    rw [Subgroup.coe_mul, pv_mul (zP : Perm (Fin 4)) (ρ : Perm (Fin 4)) m,
      pv_zP (pv (ρ : Perm (Fin 4)) m), pv_zP f, pv_zP m]
    simp only [Pi.sub_apply, Matrix.cons_val]
    linear_combination -Q01
  · simp only [Pi.sub_apply, Matrix.cons_val] at Q02
    rw [Subgroup.coe_mul, pv_mul (tP : Perm (Fin 4)) (ρ : Perm (Fin 4)) m,
      pv_tP (pv (ρ : Perm (Fin 4)) m), pv_tP f, pv_tP m]
    simp only [Pi.sub_apply, Matrix.cons_val]
    linear_combination -Q02
  · simp only [Pi.sub_apply, Matrix.cons_val] at Q03
    rw [Subgroup.coe_mul, pv_mul (tzP : Perm (Fin 4)) (ρ : Perm (Fin 4)) m,
      pv_tzP (pv (ρ : Perm (Fin 4)) m), pv_tzP f, pv_tzP m]
    simp only [Pi.sub_apply, Matrix.cons_val]
    linear_combination -Q03

theorem el_comm_tP_iff (hn : 2 ≤ n) {m f : Fin 4 → ZMod (2 ^ n)} {ρ : Fin81.R0}
    (hm : detSum m tP) (hf : detSum f ρ) :
    el f ρ hf * el m tP hm = el m tP hm * el f ρ hf ↔
      ρ * tP = tP * ρ ∧
        IsConst ((pv (tP : Perm (Fin 4)) f - f) - (pv (ρ : Perm (Fin 4)) m - m)) := by
  rw [el_mul, el_mul, el_eq_el_iff hn]
  refine and_congr Iff.rfl ?_
  have : m + pv (tP : Perm (Fin 4)) f - (f + pv (ρ : Perm (Fin 4)) m) =
      (pv (tP : Perm (Fin 4)) f - f) - (pv (ρ : Perm (Fin 4)) m - m) := by abel
  rw [this]

theorem commutator_centralizer_le_A02 (hn : 2 ≤ n) {m : Fin 4 → ZMod (2 ^ n)}
    (hm : detSum m tP) :
    ⁅centralizer {el m tP hm}, centralizer {el m tP hm}⁆ ≤ A02 n := by
  rw [Subgroup.commutator_le]
  intro a ha b hb
  obtain ⟨d, σ, hd, rfl⟩ := exists_eq_el a
  obtain ⟨e, τ, he, rfl⟩ := exists_eq_el b
  rw [mem_centralizer_singleton_iff, el_comm_tP_iff hn hm hd] at ha
  rw [mem_centralizer_singleton_iff, el_comm_tP_iff hn hm he] at hb
  have key : ∀ π π' : Fin81.R0, π * tP = tP * π → π' * tP = tP * π' → π * π' = π' * π := by
    decide
  have hστ := key σ τ ha.1 hb.1
  rw [commutatorElement_el hn hd he hστ]
  refine ⟨_, _, rfl, ?_⟩
  have h1 := pv_two_sub_pv_zero hn hb.2 ha.1
  have h2 := pv_two_sub_pv_zero hn ha.2 hb.1
  rw [hστ] at h1
  simp only [Pi.sub_apply, Pi.add_apply] at h1 h2 ⊢
  linear_combination h1 - h2

theorem patFix_tP_cases : ∀ p : Fin 2 × Fin 2 × Fin 2,
    PatFix ((tP : Fin81.R0) : Perm (Fin 4)) (pat p) →
      p = (0, 0, 0) ∨ p = (0, 1, 1) ∨ p = (1, 0, 1) ∨ p = (1, 1, 0) := by
  decide

theorem eq_x1T_of_mem_commutator_centralizer (hn : 3 ≤ n) {m : Fin 4 → ZMod (2 ^ n)}
    (hm : detSum m tP) {ν : L4Model n}
    (hν : ν ∈ ⁅centralizer {el m tP hm}, centralizer {el m tP hm}⁆) (h1 : ν ≠ 1)
    (h2 : ν * ν = 1) : ν = x1T (by omega) := by
  have hA02 := commutator_centralizer_le_A02 (by omega) hm hν
  have hC : ν ∈ centralizer {el m tP hm} := by
    refine (Subgroup.commutator_le.mpr fun a ha b hb => ?_) hν
    rw [commutatorElement_def]
    exact Subgroup.mul_mem _ (Subgroup.mul_mem _ (Subgroup.mul_mem _ ha hb)
      (Subgroup.inv_mem _ ha)) (Subgroup.inv_mem _ hb)
  obtain ⟨p, rfl⟩ := exists_eq_omegaEl hn (A02_le_A hA02) h2
  have hpat := patFix_of_comm hn (s := el m tP hm) (mem_centralizer_singleton_iff.1 hC).symm
  rw [piT_el] at hpat
  obtain ⟨e', he', heq, he2⟩ := hA02
  have hh0 := natCast_two_pow_ne_zero (n := n) (by omega)
  rcases patFix_tP_cases p hpat with rfl | rfl | rfl | rfl
  · exact absurd (omegaEl_zero hn) h1
  · exfalso
    rw [← zT_eq_omegaEl hn, zT, el_eq_el_iff (by omega)] at heq
    have h := heq.2 0 2
    simp only [Pi.sub_apply, hv, Matrix.cons_val, Nat.cast_one, Nat.cast_zero, mul_one,
      mul_zero] at h
    exact hh0 (by linear_combination -h - he2)
  · exact (x1T_eq_omegaEl hn).symm
  · exfalso
    rw [← y1T_eq_omegaEl hn, y1T, el_eq_el_iff (by omega)] at heq
    have h := heq.2 0 2
    simp only [Pi.sub_apply, hv, Matrix.cons_val, Nat.cast_one, Nat.cast_zero, mul_one,
      mul_zero] at h
    exact hh0 (by linear_combination -h - he2)

abbrev g02 (n : ℕ) : L4Hat n := hat (Pi.single 2 1) 1

theorem g02_conj_hat (d : Fin 4 → ZMod (2 ^ n)) (π : Fin81.R0) :
    g02 n * hat d π * (g02 n)⁻¹ =
      hat (d + Pi.single 2 1 - pv (π : Perm (Fin 4)) (Pi.single 2 1)) π := by
  apply SemidirectProduct.ext
  · apply Multiplicative.toAdd.injective
    funext i
    simp only [SemidirectProduct.mul_left, SemidirectProduct.inv_left, SemidirectProduct.mul_right,
      toAdd_mul, toAdd_inv, Pi.add_apply, Pi.neg_apply, Pi.sub_apply, toAdd_ofAdd, map_one,
      MulAut.one_apply, inv_one, OneMemClass.coe_one, one_mul]
    rw [map_inv, toAdd_inv, Pi.neg_apply, toAdd_actL4, toAdd_ofAdd]
    ring
  · simp

theorem g02_conj_cL4 : MulAut.conjNormal (g02 n) (cL4 n) = cL4 n := by
  apply Subtype.ext
  rw [MulAut.conjNormal_apply, coe_cL4, ← cHat_mul_comm n (g02 n), mul_inv_cancel_right]

@[expose] noncomputable def diagAut (n : ℕ) : L4Model n ≃* L4Model n :=
  QuotientGroup.congr (Subgroup.zpowers (cL4 n)) (Subgroup.zpowers (cL4 n))
    (MulAut.conjNormal (g02 n)) (by rw [MonoidHom.map_zpowers]; exact congrArg _ g02_conj_cL4)

theorem detSum_g02 {d : Fin 4 → ZMod (2 ^ n)} {π : Fin81.R0} (h : detSum d π) :
    detSum (d + Pi.single 2 1 - pv (π : Perm (Fin 4)) (Pi.single 2 1)) π := by
  have := (L4P n).mul_mem (Subgroup.mul_mem _ (hat_mem_L4P.2 h) (Subgroup.one_mem _))
    (Subgroup.one_mem _)
  rw [← hat_mem_L4P, ← g02_conj_hat]
  exact (inferInstance : (L4P n).Normal).conj_mem _ (hat_mem_L4P.2 h) _

theorem diagAut_el {d : Fin 4 → ZMod (2 ^ n)} {π : Fin81.R0} (h : detSum d π) :
    diagAut n (el d π h) =
      el (d + Pi.single 2 1 - pv (π : Perm (Fin 4)) (Pi.single 2 1)) π (detSum_g02 h) := by
  rw [el, diagAut, QuotientGroup.congr_mk]
  congr 1
  apply Subtype.ext
  rw [MulAut.conjNormal_apply]
  exact g02_conj_hat d π

theorem diagAut_el_one {d : Fin 4 → ZMod (2 ^ n)} (h : detSum d 1) :
    diagAut n (el d 1 h) = el d 1 h := by
  rw [diagAut_el]
  have hv1 : d + Pi.single 2 1 - pv ((1 : Fin81.R0) : Perm (Fin 4)) (Pi.single 2 1) = d := by
    rw [OneMemClass.coe_one, pv_one]
    abel
  exact el_congr _ _ hv1 rfl

theorem diagAut_of_mem_A {g : L4Model n} (hg : g ∈ A n) : diagAut n g = g := by
  obtain ⟨d, π, h, rfl⟩ := exists_eq_el g
  rw [el_mem_A] at hg
  subst hg
  exact diagAut_el_one h

theorem pv_tP_single_two : pv (tP : Perm (Fin 4)) (Pi.single 2 1 : Fin 4 → ZMod (2 ^ n)) =
    Pi.single 0 1 := by
  rw [pv_tP]
  funext i
  fin_cases i <;> simp [Pi.single_apply]

theorem pv_zP_single_two : pv (zP : Perm (Fin 4)) (Pi.single 2 1 : Fin 4 → ZMod (2 ^ n)) =
    Pi.single 3 1 := by
  rw [pv_zP]
  funext i
  fin_cases i <;> simp [Pi.single_apply]

theorem diagAut_tT (hn : 1 ≤ n) : diagAut n (tT (n := n) hn) = txT n := by
  rw [tT, txT, diagAut_el]
  refine el_congr _ _ ?_ rfl
  rw [pv_tP_single_two]
  funext i
  fin_cases i <;> simp [hv, Pi.single_apply]

theorem diagAut_uvT (hn : 1 ≤ n) : diagAut n (uvT (n := n) hn) = uvxyT hn := by
  rw [uvT, uvxyT, diagAut_el]
  refine el_congr _ _ ?_ rfl
  rw [pv_zP_single_two]
  funext i
  fin_cases i <;> simp [hv, Pi.single_apply] <;> ring

theorem diagAut_x1T (hn : 1 ≤ n) : diagAut n (x1T (n := n) hn) = x1T hn :=
  diagAut_of_mem_A (x1T_mem_A hn)

theorem diagAut_y1T (hn : 1 ≤ n) : diagAut n (y1T (n := n) hn) = y1T hn :=
  diagAut_of_mem_A (y1T_mem_A hn)

theorem centralizer_mulEquiv_apply {G : Type*} [Group G] (θ : G ≃* G) (μ : G) :
    centralizer {θ μ} = (centralizer {μ}).map θ.toMonoidHom := by
  ext x
  simp only [mem_centralizer_singleton_iff, mem_map, MulEquiv.coe_toMonoidHom]
  constructor
  · intro hx
    refine ⟨θ.symm x, ?_, θ.apply_symm_apply x⟩
    apply θ.injective
    rw [map_mul, map_mul, θ.apply_symm_apply, hx]
  · rintro ⟨y, hy, rfl⟩
    rw [← map_mul, hy, map_mul]

end CFSG.LocalAnalysis.Mason73
