module

public import CFSG.LocalAnalysis.OddStandard.SmallF3.U33.Sec4B.SbQ13d5c
public import CFSG.LocalAnalysis.OddStandard.SmallF3.U33.Sec4B.SbQ13d5a

public section

namespace CFSG.OddStandard.SmallF3.HarrisU33.S4B

open Subgroup
open scoped Pointwise

variable {G : Type} [Group G] [Finite G] {t : G} {L S : Subgroup G} {x₁ x₂ lam rho tau om : G}

private theorem q13d_B_odd_aux (h : Q13Om t L S x₁ x₂ lam rho tau om)
    (hII : closure ({t, om} : Set G) ⊓
      centralizer ((q13A t tau x₁ x₂ rho : Subgroup G) : Set G) = zpowers (t * om))
    {b : G} (hb : b ∈ q13B t tau x₁ x₂ rho om) {p : G}
    (hp : p ∈ q13P t tau x₁ x₂ rho om) :
    ∃ u ∈ q13P t tau x₁ x₂ rho om,
      u ∈ ctxN tau x₁ x₂ ∧ u * u = 1 ∧ b * p * b⁻¹ = p * u ∧ b * u * b⁻¹ = u := by
  have hbC : ∀ n ∈ ctxN tau x₁ x₂, n * b = b * n :=
    Subgroup.mem_centralizer_iff.mp (Subgroup.mem_inf.mp hb).2
  have hbL : b ∈ q13L t tau x₁ x₂ rho om := (Subgroup.mem_inf.mp hb).1
  set u : G := p⁻¹ * (b * p * b⁻¹) with hu
  have hqP : b * p * b⁻¹ ∈ q13P t tau x₁ x₂ rho om :=
    q13d_P_normal_L h hII b hbL p hp
  have huP : u ∈ q13P t tau x₁ x₂ rho om := by
    rw [hu]
    exact (q13P t tau x₁ x₂ rho om).mul_mem ((q13P t tau x₁ x₂ rho om).inv_mem hp) hqP
  have hpP : p⁻¹ ∈ q13P t tau x₁ x₂ rho om := (q13P t tau x₁ x₂ rho om).inv_mem hp
  have hcomm_qp : (b * p * b⁻¹) * p⁻¹ = p⁻¹ * (b * p * b⁻¹) :=
    q13d_P_comm h hII (b * p * b⁻¹) hqP p⁻¹ hpP
  have hbp : b * p * b⁻¹ = p * u := by rw [hu]; group
  have hq2 : (b * p * b⁻¹) * (b * p * b⁻¹) = b * p ^ 2 * b⁻¹ := by
    rw [pow_two]; group
  have hp2N : p ^ 2 ∈ ctxN tau x₁ x₂ := q13d_P_sq_mem_N h hII p hp
  have hbp2 : b * p ^ 2 * b⁻¹ = p ^ 2 := by
    have h1 := hbC (p ^ 2) hp2N
    calc b * p ^ 2 * b⁻¹ = (p ^ 2 * b) * b⁻¹ := by rw [h1]
      _ = p ^ 2 := by group
  have huu : u * u = 1 := by
    rw [hu]
    calc (p⁻¹ * (b * p * b⁻¹)) * (p⁻¹ * (b * p * b⁻¹))
        = p⁻¹ * ((b * p * b⁻¹) * p⁻¹) * (b * p * b⁻¹) := by group
      _ = p⁻¹ * (p⁻¹ * (b * p * b⁻¹)) * (b * p * b⁻¹) := by rw [hcomm_qp]
      _ = p⁻¹ * p⁻¹ * ((b * p * b⁻¹) * (b * p * b⁻¹)) := by group
      _ = p⁻¹ * p⁻¹ * (b * p ^ 2 * b⁻¹) := by rw [hq2]
      _ = p⁻¹ * p⁻¹ * p ^ 2 := by rw [hbp2]
      _ = 1 := by group
  have huN : u ∈ ctxN tau x₁ x₂ :=
    q13d_P_sq_eq_one_mem_N h hII u huP (by rw [pow_two]; exact huu)
  have hbu : b * u * b⁻¹ = u := by
    have h1 := hbC u huN
    calc b * u * b⁻¹ = (u * b) * b⁻¹ := by rw [← h1]
      _ = u := by group
  exact ⟨u, huP, huN, huu, hbp, hbu⟩

private theorem q13d_B_odd_sq_cent (h : Q13Om t L S x₁ x₂ lam rho tau om)
    (hII : closure ({t, om} : Set G) ⊓
      centralizer ((q13A t tau x₁ x₂ rho : Subgroup G) : Set G) = zpowers (t * om))
    {b : G} (hb : b ∈ q13B t tau x₁ x₂ rho om) :
    ∀ p ∈ q13P t tau x₁ x₂ rho om, (b * b) * p = p * (b * b) := by
  intro p hp
  obtain ⟨u, _huP, _huN, huu, hbp, hbu⟩ := q13d_B_odd_aux h hII hb hp
  have hconj : (b * b) * p * (b * b)⁻¹ = p := by
    calc (b * b) * p * (b * b)⁻¹ = b * (b * p * b⁻¹) * b⁻¹ := by group
      _ = b * (p * u) * b⁻¹ := by rw [hbp]
      _ = (b * p * b⁻¹) * (b * u * b⁻¹) := by group
      _ = (p * u) * u := by rw [hbp, hbu]
      _ = p * (u * u) := by group
      _ = p := by rw [huu, mul_one]
  calc (b * b) * p = ((b * b) * p * (b * b)⁻¹) * (b * b) := by group
    _ = p * (b * b) := by rw [hconj]

private theorem q13d_B_odd_comm_P (h : Q13Om t L S x₁ x₂ lam rho tau om)
    (hII : closure ({t, om} : Set G) ⊓
      centralizer ((q13A t tau x₁ x₂ rho : Subgroup G) : Set G) = zpowers (t * om))
    {b : G} (hb : b ∈ q13B t tau x₁ x₂ rho om) (hodd : Odd (orderOf b)) :
    ∀ p ∈ q13P t tau x₁ x₂ rho om, Commute b p := by
  intro p hp
  have hc2 : Commute (b * b) p := q13d_B_odd_sq_cent h hII hb p hp
  obtain ⟨m, hm⟩ := hodd
  have hb_eq : b = (b * b) ^ (m + 1) := by
    have h1 : b ^ (2 * m + 1) = 1 := by rw [← hm]; exact pow_orderOf_eq_one b
    have h2 : b ^ (2 * m + 2) = b := by
      rw [show 2 * m + 2 = (2 * m + 1) + 1 by omega, pow_succ, h1, one_mul]
    calc b = b ^ (2 * m + 2) := h2.symm
      _ = (b ^ 2) ^ (m + 1) := by rw [show 2 * m + 2 = 2 * (m + 1) by omega, pow_mul]
      _ = (b * b) ^ (m + 1) := by rw [pow_two]
  rw [hb_eq]
  exact hc2.pow_left (m + 1)

private theorem q13d_B_odd_conj_pow {b t p0 : G} (hcommb : Commute b p0)
    (hp0eq : b * t * b⁻¹ = t * p0) :
    ∀ j : ℕ, b ^ j * t * (b ^ j)⁻¹ = t * p0 ^ j := by
  intro j
  induction j with
  | zero => simp
  | succ j ih =>
    have hbpow : b * p0 ^ j * b⁻¹ = p0 ^ j := by
      calc b * p0 ^ j * b⁻¹ = (p0 ^ j * b) * b⁻¹ := by rw [hcommb.pow_right j]
        _ = p0 ^ j := by group
    calc b ^ (j + 1) * t * (b ^ (j + 1))⁻¹
        = b * (b ^ j * t * (b ^ j)⁻¹) * b⁻¹ := by rw [pow_succ']; group
      _ = b * (t * p0 ^ j) * b⁻¹ := by rw [ih]
      _ = (b * t * b⁻¹) * (b * p0 ^ j * b⁻¹) := by group
      _ = (t * p0) * p0 ^ j := by rw [hp0eq, hbpow]
      _ = t * p0 ^ (j + 1) := by rw [pow_succ']; group

theorem q13d_B_odd_eq_one (h : Q13Om t L S x₁ x₂ lam rho tau om)
    (hII : closure ({t, om} : Set G) ⊓
      centralizer ((q13A t tau x₁ x₂ rho : Subgroup G) : Set G) = zpowers (t * om)) {b : G} (hb :
        b ∈ q13B t tau x₁ x₂ rho om) (hodd : Odd (orderOf b)) :
    b = 1 := by
  have hbL : b ∈ q13L t tau x₁ x₂ rho om := (Subgroup.mem_inf.mp hb).1
  have hcomm_P := q13d_B_odd_comm_P h hII hb hodd
  obtain ⟨p0, hp0P, hp0eq0⟩ : ∃ p0 ∈ q13P t tau x₁ x₂ rho om, t * p0 = b * t * b⁻¹ := by
    have htL := q13d_tL h hII b hbL
    rw [Set.mem_smul_set] at htL
    obtain ⟨p0, hp0P, hp0eq⟩ := htL
    refine ⟨p0, hp0P, ?_⟩
    rwa [smul_eq_mul] at hp0eq
  have hp0eq : b * t * b⁻¹ = t * p0 := hp0eq0.symm
  have hcommb : Commute b p0 := hcomm_P p0 hp0P
  have hconj := q13d_B_odd_conj_pow hcommb hp0eq (orderOf b)
  have hp0k : p0 ^ orderOf b = 1 := by
    rw [pow_orderOf_eq_one b, one_mul, inv_one, mul_one] at hconj
    have hh : t * p0 ^ orderOf b = t * 1 := by rw [mul_one]; exact hconj.symm
    exact mul_left_cancel hh
  have hp01 : p0 = 1 := by
    have hdvd4 : orderOf p0 ∣ 4 :=
      orderOf_dvd_iff_pow_eq_one.mpr (q13d_P_pow_four h hII p0 hp0P)
    have hdvdk : orderOf p0 ∣ orderOf b := orderOf_dvd_iff_pow_eq_one.mpr hp0k
    have hcop : Nat.Coprime (2 ^ 2) (orderOf b) :=
      (Odd.coprime_two_left hodd).pow_left 2
    have hgcd : Nat.gcd 4 (orderOf b) = 1 := by simpa using hcop
    have hdvd1 : orderOf p0 ∣ 1 := by
      rw [← hgcd]
      exact Nat.dvd_gcd hdvd4 hdvdk
    exact orderOf_eq_one_iff.mp (Nat.dvd_one.mp hdvd1)
  have hbt : Commute b t := by
    rw [commute_iff_eq]
    rw [hp01, mul_one] at hp0eq
    calc b * t = (b * t * b⁻¹) * b := by group
      _ = t * b := by rw [hp0eq]
  have hbE0 : b ∈ centralizer ((q13E0 t tau x₁ x₂ rho om : Subgroup G) : Set G) := by
    rw [Subgroup.mem_centralizer_iff]
    intro e he
    have hle : q13E0 t tau x₁ x₂ rho om ≤ centralizer ({b} : Set G) := by
      refine sup_le ?_ ?_
      · intro p hp
        rw [Subgroup.mem_centralizer_singleton_iff]
        exact (hcomm_P p hp).eq.symm
      · rw [Subgroup.zpowers_le]
        rw [Subgroup.mem_centralizer_singleton_iff]
        exact hbt.eq.symm
    exact Subgroup.mem_centralizer_singleton_iff.mp (hle he)
  have hbN : b ∈ ctxN tau x₁ x₂ := by
    rwa [q13d_cent_E0 h] at hbE0
  have hb2 : b ^ 2 = 1 := (q13b_N_elemAbelian h).2 b hbN
  have hdvd : orderOf b ∣ 2 := orderOf_dvd_iff_pow_eq_one.mpr hb2
  rcases (Nat.dvd_prime Nat.prime_two).mp hdvd with h1 | h1
  · exact orderOf_eq_one_iff.mp h1
  · exfalso
    obtain ⟨m, hm⟩ := hodd
    omega

theorem q13d_B_two (h : Q13Om t L S x₁ x₂ lam rho tau om)
    (hII : closure ({t, om} : Set G) ⊓
      centralizer ((q13A t tau x₁ x₂ rho : Subgroup G) : Set G) = zpowers (t * om)) :
    IsPGroup 2 (q13B t tau x₁ x₂ rho om) := by
  intro g
  set b : G := (g : G) with hbdef
  have hb : b ∈ q13B t tau x₁ x₂ rho om := g.2
  obtain ⟨k, m, hm_odd, hm_eq⟩ := Nat.exists_eq_two_pow_mul_odd (orderOf_pos b).ne'
  have hbm_mem : b ^ (2 ^ k) ∈ q13B t tau x₁ x₂ rho om :=
    (q13B t tau x₁ x₂ rho om).pow_mem hb (2 ^ k)
  have hpow : (b ^ (2 ^ k)) ^ m = 1 := by
    rw [← pow_mul, ← hm_eq, pow_orderOf_eq_one]
  have hdvd : orderOf (b ^ (2 ^ k)) ∣ m := orderOf_dvd_iff_pow_eq_one.mpr hpow
  have hodd_ord : Odd (orderOf (b ^ (2 ^ k))) := by
    rw [← Nat.not_even_iff_odd]
    intro heven
    exact (Nat.not_even_iff_odd.mpr hm_odd) (heven.trans_dvd hdvd)
  have hbm1 : b ^ (2 ^ k) = 1 := q13d_B_odd_eq_one h hII hbm_mem hodd_ord
  refine ⟨k, ?_⟩
  have hg_eq : (⟨b, hb⟩ : ↥(q13B t tau x₁ x₂ rho om)) = g := Subtype.ext rfl
  rw [← hg_eq]
  exact Subtype.ext (by simpa using hbm1)

end CFSG.OddStandard.SmallF3.HarrisU33.S4B
