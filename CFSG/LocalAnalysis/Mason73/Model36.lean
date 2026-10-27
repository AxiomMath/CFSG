module

public import CFSG.LocalAnalysis.Mason73.Powers
import Mathlib.Tactic.LinearCombination

public section

namespace CFSG.LocalAnalysis.Mason73

open CFSG.CGT.Stroth77.L4Sylow CFSG.GH74.GLS.Stage1.Thm3.Sec8 Equiv Subgroup

variable {n : ℕ}

theorem four_ne_zero_zmod (hn : 3 ≤ n) : (4 : ZMod (2 ^ n)) ≠ 0 := by
  rw [show (4 : ZMod (2 ^ n)) = ((4 : ℕ) : ZMod (2 ^ n)) by norm_num, Ne,
    ZMod.natCast_eq_zero_iff]
  intro h
  have h1 := Nat.le_of_dvd (by norm_num) h
  have h2 : 2 ^ 3 ≤ 2 ^ n := Nat.pow_le_pow_right (by norm_num) hn
  omega

theorem card_centralizer_le_of_mul_self_not_mem_A (hn : 3 ≤ n) {ν : L4Model n}
    (h2 : ν * ν = 1) (hA : ν ∉ A n) : Nat.card (centralizer {ν}) ≤ 2 ^ (2 * n) := by
  have hle : ∀ k, k ≤ n + 3 → 2 ^ k ≤ 2 ^ (2 * n) := fun k hk =>
    Nat.pow_le_pow_right (by norm_num) (by omega)
  rcases piT_eq_of_mul_self h2 with h | h | h | h | h | h
  · exact absurd (mem_A_iff.2 h) hA
  · exact card_centralizer_le_of_piT_s23 (by omega) (Or.inl h)
  · exact card_centralizer_le_of_piT_s23 (by omega) (Or.inr h)
  · exact (card_centralizer_le_of_piT_zP (by omega) h).trans (hle _ le_rfl)
  · exact (card_centralizer_le_of_piT_tP (by omega) (Or.inl h)).trans (hle _ (by omega))
  · exact (card_centralizer_le_of_piT_tP (by omega) (Or.inr h)).trans (hle _ (by omega))

theorem w1T_mul_self (hn : 3 ≤ n) : w1T (n := n) hn * w1T hn = 1 := by
  rw [w1T, el_mul, ← el_zero_one, el_eq_el_iff (by omega)]
  refine ⟨mul_one 1, ?_⟩
  have h2 := hh_add_hh (n := n) (by omega)
  refine isConst_of_eq_four (-(ss n + ss n)) ?_ ?_ ?_ ?_ <;>
    simp only [Pi.sub_apply, Pi.add_apply, Pi.zero_apply, OneMemClass.coe_one, pv_one, wv, hv,
      Matrix.cons_val, Nat.cast_one, Nat.cast_zero, mul_one, mul_zero] <;>
    first | ring1 | linear_combination -h2 | linear_combination h2

theorem w1T_ne_one (hn : 3 ≤ n) : w1T (n := n) hn ≠ 1 := fun h =>
  pow_ne_w1T hn (one_mem (A n)) (by rw [one_pow, h])

theorem w1T_mul_omegaEl_odd (hn : 3 ≤ n) (p : Fin 2 × Fin 2 × Fin 2)
    (hp : (pat p 0 + pat p 1 + pat p 2 + pat p 3) % 2 = 1) :
    w1T hn * omegaEl hn p = 1 ∨ w1T hn * omegaEl hn p = zT (by omega) ∨
      w1T hn * omegaEl hn p = x1T (by omega) ∨ w1T hn * omegaEl hn p = y1T (by omega) := by
  have key : ∀ (χ : Fin 4 → ℕ) (h : detSum (hv n χ) 1),
      (∀ i j, (χ i + (![1, 0, 0, 0] + pat p : Fin 4 → ℕ) j) % 2 =
        (χ j + (![1, 0, 0, 0] + pat p : Fin 4 → ℕ) i) % 2) →
      w1T hn * omegaEl hn p = el (hv n χ) 1 h := by
    intro χ h hχ
    rw [w1T, omegaEl, dif_neg (by omega), el_mul, el_eq_el_iff (by omega)]
    refine ⟨mul_one 1, ?_⟩
    have hc := (hv_sub_hv_isConst_iff (n := n) (by omega) χ
      (![1, 0, 0, 0] + pat p : Fin 4 → ℕ)).2 hχ
    intro i j
    have h1 := hc i j
    simp only [Pi.sub_apply, Pi.add_apply, OneMemClass.coe_one, pv_one, wv, hv,
      Nat.cast_add] at h1 ⊢
    linear_combination h1
  have hcases : ∀ q : Fin 2 × Fin 2 × Fin 2, (pat q 0 + pat q 1 + pat q 2 + pat q 3) % 2 = 1 →
      q = (1, 1, 1) ∨ q = (0, 0, 1) ∨ q = (0, 1, 0) ∨ q = (1, 0, 0) := by
    decide
  rcases hcases p hp with rfl | rfl | rfl | rfl
  · exact Or.inl ((key ![0, 0, 0, 0] (detSum_hv (by omega) (by decide)) (by decide)).trans
      (one_eq_el_hv (by omega)).symm)
  · exact Or.inr (Or.inr (Or.inr (key χy1 (detSum_hv (by omega) (by decide)) (by decide))))
  · exact Or.inr (Or.inr (Or.inl (key χx1 (detSum_hv (by omega) (by decide)) (by decide))))
  · exact Or.inr (Or.inl (key χz (detSum_hv (by omega) (by decide)) (by decide)))

theorem wT_mem_centralizer_of_piT_s23 (hn : 2 ≤ n) {μ : L4Model n} (hμ : piT μ = s23) :
    wT n ∈ centralizer {μ} := by
  obtain ⟨d, π, hd, rfl⟩ := exists_eq_el μ
  rw [piT_el] at hμ
  subst hμ
  rw [mem_centralizer_singleton_iff, wT, eq_comm, el_comm_diag_iff hn, pv_s23]
  refine isConst_of_eq_four 0 ?_ ?_ ?_ ?_ <;> simp only [Pi.sub_apply, Matrix.cons_val] <;> ring1

theorem wT_not_mem_centralizer_of_piT_s01 (hn : 3 ≤ n) {μ : L4Model n} (hμ : piT μ = s01) :
    wT n ∉ centralizer {μ} := by
  obtain ⟨d, π, hd, rfl⟩ := exists_eq_el μ
  rw [piT_el] at hμ
  subst hμ
  rw [mem_centralizer_singleton_iff, wT, eq_comm, el_comm_diag_iff (by omega), pv_s01]
  intro h
  have h02 := h 0 2
  simp only [Pi.sub_apply, Matrix.cons_val] at h02
  exact four_ne_zero_zmod hn (by linear_combination h02)

theorem tT_inv (hn : 2 ≤ n) : (tT (n := n) (by omega))⁻¹ = tT (by omega) :=
  inv_eq_of_mul_eq_one_right (tT_mul_self hn)

theorem piT_tT_conj_of_piT_s23 (hn : 1 ≤ n) {μ : L4Model n} (hμ : piT μ = s23) :
    piT (tT (n := n) hn * μ * (tT hn)⁻¹) = s01 := by
  rw [map_mul, map_mul, map_inv, hμ, piT_tT]
  decide

theorem detSum_zero_tP : detSum (0 : Fin 4 → ZMod (2 ^ n)) tP := by
  rw [detSum_even_iff (by decide)]
  simp

theorem tT_eq_el_zero (hn : 1 ≤ n) : tT (n := n) hn = el 0 tP detSum_zero_tP :=
  el_congr _ _ (by funext i; fin_cases i <;> simp [hv]) rfl

theorem detSum_conj_tP {d : Fin 4 → ZMod (2 ^ n)} {π : Fin81.R0} (h : detSum d π) :
    detSum (pv (tP : Perm (Fin 4)) d) (tP * π * tP) := by
  have h3 := detSum_mul (detSum_mul detSum_zero_tP h) detSum_zero_tP
  have heq : (0 + pv (tP : Perm (Fin 4)) d + pv ((tP * π : Fin81.R0) : Perm (Fin 4)) 0 :
      Fin 4 → ZMod (2 ^ n)) = pv (tP : Perm (Fin 4)) d := by
    funext i
    simp [pv]
  rwa [heq] at h3

theorem tT_mul_el_mul_tT (hn : 1 ≤ n) {d : Fin 4 → ZMod (2 ^ n)} {π : Fin81.R0}
    (h : detSum d π) :
    tT hn * el d π h * tT hn = el (pv (tP : Perm (Fin 4)) d) (tP * π * tP) (detSum_conj_tP h) := by
  rw [tT_eq_el_zero, el_mul, el_mul]
  exact el_congr _ _ (by funext i; simp [pv]) rfl

theorem tT_conj_mem_centralizer_of_piT_s23 (hn : 2 ≤ n) {μ : L4Model n} (h2 : μ * μ = 1)
    (hμ : piT μ = s23) : tT (n := n) (by omega) * μ * (tT (by omega))⁻¹ ∈ centralizer {μ} := by
  obtain ⟨d, π, hd, rfl⟩ := exists_eq_el μ
  rw [piT_el] at hμ
  subst hμ
  have h01 := (el_s23_mul_self hn hd h2).1
  have hσ : tP * s23 * tP = s01 := by decide
  have hd' : detSum (pv (tP : Perm (Fin 4)) d) s01 := hσ ▸ detSum_conj_tP hd
  have hx : tT (n := n) (by omega) * el d s23 hd * (tT (by omega))⁻¹ =
      el (pv (tP : Perm (Fin 4)) d) s01 hd' := by
    rw [tT_inv hn, tT_mul_el_mul_tT]
    exact el_congr _ _ rfl hσ
  rw [hx, mem_centralizer_singleton_iff, el_mul, el_mul, el_eq_el_iff hn]
  refine ⟨by decide, ?_⟩
  rw [pv_s01, pv_s23, pv_tP]
  refine isConst_of_eq_four (d 0 - d 1) ?_ ?_ ?_ ?_ <;>
    simp only [Pi.sub_apply, Pi.add_apply, Matrix.cons_val] <;>
    first | ring1 | linear_combination h01 | linear_combination -h01

theorem mem_A_or_mul_mem_A_of_mem_V23 {μ c : L4Model n} (hμ : piT μ = s23)
    (hc : c ∈ V23.comap piT) : c ∈ A n ∨ c * μ ∈ A n := by
  rcases mem_V23_iff.1 hc with h | h
  · exact Or.inl (mem_A_iff.2 h)
  · refine Or.inr (mem_A_iff.2 ?_)
    rw [map_mul, h, hμ]
    decide

theorem comm_of_mem_centralizer_inf_V23 {μ : L4Model n} (h2 : μ * μ = 1) (hμ : piT μ = s23)
    {a b : L4Model n} (ha : a ∈ centralizer {μ} ⊓ V23.comap piT)
    (hb : b ∈ centralizer {μ} ⊓ V23.comap piT) : a * b = b * a := by
  have key : ∀ c ∈ centralizer {μ} ⊓ V23.comap piT, ∃ α ∈ A n, α * μ = μ * α ∧
      (c = α ∨ c = α * μ) := by
    intro c hc
    obtain ⟨hcμ, hcV⟩ := Subgroup.mem_inf.1 hc
    have hcμ' := mem_centralizer_singleton_iff.1 hcμ
    rcases mem_A_or_mul_mem_A_of_mem_V23 hμ hcV with h | h
    · exact ⟨c, h, hcμ', Or.inl rfl⟩
    · refine ⟨c * μ, h, by rw [← mul_assoc μ c μ, ← hcμ'], Or.inr ?_⟩
      rw [mul_assoc, h2, mul_one]
  obtain ⟨α, hαA, hαμ, hα⟩ := key a ha
  obtain ⟨β, hβA, hβμ, hβ⟩ := key b hb
  rcases hα with hα | hα <;> rcases hβ with hβ | hβ <;> rw [hα, hβ]
  · exact A_comm hαA hβA
  · calc α * (β * μ) = α * β * μ := by group
      _ = β * α * μ := by rw [A_comm hαA hβA]
      _ = β * (μ * α) := by rw [mul_assoc, hαμ]
      _ = β * μ * α := by group
  · calc α * μ * β = α * (μ * β) := by group
      _ = α * (β * μ) := by rw [← hβμ]
      _ = β * α * μ := by rw [← mul_assoc, A_comm hαA hβA]
      _ = β * (α * μ) := by group
  · calc α * μ * (β * μ) = α * (μ * β) * μ := by group
      _ = α * (β * μ) * μ := by rw [← hβμ]
      _ = α * β * (μ * μ) := by group
      _ = β * α * (μ * μ) := by rw [A_comm hαA hβA]
      _ = β * (α * μ) * μ := by group
      _ = β * (μ * α) * μ := by rw [hαμ]
      _ = β * μ * (α * μ) := by group

theorem le_card_centralizer_inf_V23 (hn : 2 ≤ n) {μ : L4Model n} (hμ : piT μ = s23) :
    2 ^ (2 * n - 1) ≤ Nat.card (centralizer {μ} ⊓ V23.comap piT : Subgroup (L4Model n)) := by
  rw [card_eq_card_inf_A_mul]
  have h1 : 2 ^ (2 * n - 2) ≤
      Nat.card ((centralizer {μ} ⊓ V23.comap piT) ⊓ A n : Subgroup (L4Model n)) := by
    refine (le_card_centA_of_piT_s23 hn hμ).trans (Subgroup.card_le_of_le ?_)
    intro x hx
    obtain ⟨hxA, hxμ⟩ := Subgroup.mem_inf.1 hx
    exact Subgroup.mem_inf.2
      ⟨Subgroup.mem_inf.2 ⟨hxμ, mem_V23_iff.2 (Or.inl (mem_A_iff.1 hxA))⟩, hxA⟩
  have h2 : 2 ≤ Nat.card ((centralizer {μ} ⊓ V23.comap piT).map piT) := by
    have hμm : piT μ ∈ (centralizer {μ} ⊓ V23.comap piT).map piT :=
      ⟨μ, Subgroup.mem_inf.2 ⟨mem_centralizer_singleton_iff.2 rfl, mem_V23_iff.2 (Or.inr hμ)⟩,
        rfl⟩
    have hne : (centralizer {μ} ⊓ V23.comap piT).map piT ≠ ⊥ := by
      intro h
      rw [h, Subgroup.mem_bot, hμ] at hμm
      exact absurd hμm (by decide)
    have := (Subgroup.one_lt_card_iff_ne_bot _).2 hne
    omega
  calc 2 ^ (2 * n - 1) = 2 ^ (2 * n - 2) * 2 := by
        rw [← pow_succ]
        congr 1
        omega
    _ ≤ _ := Nat.mul_le_mul h1 h2

theorem w1T_mem_centralizer_inf_V23 (hn : 3 ≤ n) {μ : L4Model n} (hμ : piT μ = s23) :
    w1T hn ∈ (centralizer {μ} ⊓ V23.comap piT : Subgroup (L4Model n)) := by
  have hμw : μ ∈ centralizer {w1T (n := n) hn} := by
    rw [centralizer_w1T hn]
    exact mem_V23_iff.2 (Or.inr hμ)
  refine Subgroup.mem_inf.2 ⟨?_, mem_V23_iff.2 (Or.inl (mem_A_iff.1 (w1T_mem_A hn)))⟩
  rw [mem_centralizer_singleton_iff]
  exact (mem_centralizer_singleton_iff.1 hμw).symm

theorem wT_mem_centralizer_inf_V23 (hn : 2 ≤ n) {μ : L4Model n} (hμ : piT μ = s23) :
    wT n ∈ (centralizer {μ} ⊓ V23.comap piT : Subgroup (L4Model n)) :=
  Subgroup.mem_inf.2 ⟨wT_mem_centralizer_of_piT_s23 hn hμ,
    mem_V23_iff.2 (Or.inl (mem_A_iff.1 (mem_A_of_one _)))⟩

theorem pv_s23_single_two : pv (s23 : Perm (Fin 4)) (Pi.single 2 1 : Fin 4 → ZMod (2 ^ n)) =
    Pi.single 3 1 := by
  rw [pv_s23]
  funext i
  fin_cases i <;> simp [Pi.single_apply]

theorem isConj_diagAut_of_piT_s23 (hn : 3 ≤ n) {μ : L4Model n} (h2 : μ * μ = 1)
    (hμ : piT μ = s23) : IsConj (diagAut n μ) μ := by
  obtain ⟨d, π, hd, rfl⟩ := exists_eq_el μ
  rw [piT_el] at hμ
  subst hμ
  have h2' : diagAut n (el d s23 hd) * diagAut n (el d s23 hd) = 1 := by
    rw [← map_mul, h2, map_one]
  rw [diagAut_el] at h2' ⊢
  obtain ⟨b, hb, hb'⟩ := exists_hh_of_two_mul (by omega) (x := d 1 - d 0)
    (by linear_combination -(el_s23_mul_self (by omega) hd h2).1)
  interval_cases b
  · simp only [Nat.cast_zero, mul_zero] at hb'
    refine (isConj_el_s23_uw1T hn _ h2' ?_).trans
      (isConj_el_s23_uw1T hn hd h2 (by linear_combination hb')).symm
    rw [pv_s23_single_two]
    simp only [Pi.add_apply, Pi.sub_apply, Pi.single_apply]
    simp only [show (1 : Fin 4) ≠ 2 by decide, show (1 : Fin 4) ≠ 3 by decide,
      show (0 : Fin 4) ≠ 2 by decide, show (0 : Fin 4) ≠ 3 by decide, if_false]
    linear_combination hb'
  · simp only [Nat.cast_one, mul_one] at hb'
    refine (isConj_el_s23_uT hn _ h2' ?_).trans
      (isConj_el_s23_uT hn hd h2 (by linear_combination hb')).symm
    rw [pv_s23_single_two]
    simp only [Pi.add_apply, Pi.sub_apply, Pi.single_apply]
    simp only [show (1 : Fin 4) ≠ 2 by decide, show (1 : Fin 4) ≠ 3 by decide,
      show (0 : Fin 4) ≠ 2 by decide, show (0 : Fin 4) ≠ 3 by decide, if_false]
    linear_combination hb'

theorem isConj_diagAut_of_piT_zP (hn : 3 ≤ n) {μ : L4Model n} (h2 : μ * μ = 1)
    (hμ : piT μ = zP) :
    (IsConj μ (uvT (by omega)) ∧ IsConj (diagAut n μ) (uvxyT (by omega))) ∨
      (IsConj μ (uvxyT (by omega)) ∧ IsConj (diagAut n μ) (uvT (by omega))) := by
  obtain ⟨d, π, hd, rfl⟩ := exists_eq_el μ
  rw [piT_el] at hμ
  subst hμ
  have h2' : diagAut n (el d zP hd) * diagAut n (el d zP hd) = 1 := by
    rw [← map_mul, h2, map_one]
  rw [diagAut_el] at h2' ⊢
  have hs : ∀ _ : ZMod (2 ^ n),
      (d + Pi.single 2 1 - pv (zP : Perm (Fin 4)) (Pi.single 2 1) : Fin 4 → ZMod (2 ^ n)) 0 -
        (d + Pi.single 2 1 - pv (zP : Perm (Fin 4)) (Pi.single 2 1) : Fin 4 → ZMod (2 ^ n)) 2 =
          d 0 - d 2 - 1 := by
    intro _
    rw [pv_zP_single_two]
    simp only [Pi.add_apply, Pi.sub_apply, Pi.single_apply]
    simp only [show (0 : Fin 4) ≠ 2 by decide, show (0 : Fin 4) ≠ 3 by decide,
      show (2 : Fin 4) ≠ 3 by decide, if_false, if_true]
    ring
  obtain ⟨k, hk | hk⟩ := exists_eq_two_mul_or (d 0 - d 2)
  · left
    refine ⟨isConj_el_zP_uvT hn hd h2 hk, isConj_el_zP_uvxyT hn _ h2' (k := k - 1) ?_⟩
    rw [hs k, hk]
    ring
  · right
    refine ⟨isConj_el_zP_uvxyT hn hd h2 hk, isConj_el_zP_uvT hn _ h2' (k := k) ?_⟩
    rw [hs k, hk]
    ring

end CFSG.LocalAnalysis.Mason73
