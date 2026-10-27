module

public import CFSG.LocalAnalysis.OddStandard.SmallF3.U33.Sec4B.SbQ13b2a
public import CFSG.LocalAnalysis.OddStandard.SmallF3.U33.Sec4B.SbQ13d2a

public section

namespace CFSG.OddStandard.SmallF3.HarrisU33.S4B

open Subgroup
open scoped Pointwise

variable {G : Type} [Group G] [Finite G] {t : G} {L S : Subgroup G} {x₁ x₂ lam rho tau om : G}

private theorem q13d_z4pow2_pow_four : ∀ x : Outside.Z4pow 2, x ^ 4 = 1 := by
  decide +kernel

private theorem q13d_A_pow_four (h : Q13Om t L S x₁ x₂ lam rho tau om) :
    ∀ a ∈ q13A t tau x₁ x₂ rho, a ^ 4 = 1 := by
  intro a ha
  obtain ⟨e⟩ := q13a_A_iso h
  have hm : e ⟨a, ha⟩ ^ 4 = 1 := q13d_z4pow2_pow_four (e ⟨a, ha⟩)
  have h1 : e (⟨a, ha⟩ ^ 4) = 1 := by rw [map_pow, hm]
  have h2 : (⟨a, ha⟩ : ↥(q13A t tau x₁ x₂ rho)) ^ 4 = 1 :=
    (MulEquiv.map_eq_one_iff e).mp h1
  simpa using congrArg Subtype.val h2

private theorem q13d_A_sq_mem_V (h : Q13Om t L S x₁ x₂ lam rho tau om) :
    ∀ a ∈ q13A t tau x₁ x₂ rho, a * a ∈ fourGrp x₁ x₂ := by
  intro a ha
  apply q13b_omega1_A h (a * a) ((q13A t tau x₁ x₂ rho).mul_mem ha ha)
  have h4 := q13d_A_pow_four h a ha
  rw [show (4 : ℕ) = 2 * 2 by norm_num, pow_mul] at h4
  simpa only [pow_two] using h4

private theorem q13d_gam_comm' (h : Q13Om t L S x₁ x₂ lam rho tau om)
    (hII : closure ({t, om} : Set G) ⊓
      centralizer ((q13A t tau x₁ x₂ rho : Subgroup G) : Set G) = zpowers (t * om)) :
    ∀ a ∈ q13A t tau x₁ x₂ rho, Commute (t * om) a :=
  fun a ha => q13d_gam_cent_A h hII a ha

private theorem q13d_gam_zpow_sq (h : Q13Om t L S x₁ x₂ lam rho tau om) (k : ℤ) :
    ((t * om) ^ k) ^ 2 = tau ^ k := by
  have h2 : (t * om) ^ ((2 : ℕ) : ℤ) = tau := by
    rw [zpow_natCast]
    exact q13d_gam_sq h
  rw [← zpow_natCast, zpow_comm, h2]

private theorem q13d_tau_zpow_even (h : Q13Om t L S x₁ x₂ lam rho tau om) (m : ℤ) :
    tau ^ ((2 : ℤ) * m) = 1 := by
  rw [zpow_mul]
  have h2 : tau ^ (2 : ℤ) = 1 := by
    rw [zpow_two]
    exact q13a_tau_mul_self h
  rw [h2, one_zpow]

private theorem q13d_tau_zpow_odd (h : Q13Om t L S x₁ x₂ lam rho tau om) (m : ℤ) :
    tau ^ ((2 : ℤ) * m + 1) = tau := by
  rw [zpow_add, zpow_mul]
  have h2 : tau ^ (2 : ℤ) = 1 := by
    rw [zpow_two]
    exact q13a_tau_mul_self h
  rw [h2, one_zpow, one_mul, zpow_one]

theorem q13d_P_pow_four (h : Q13Om t L S x₁ x₂ lam rho tau om)
    (hII : closure ({t, om} : Set G) ⊓
      centralizer ((q13A t tau x₁ x₂ rho : Subgroup G) : Set G) = zpowers (t * om)) :
    ∀ p ∈ q13P t tau x₁ x₂ rho om, p ^ 4 = 1 := by
  intro p hp
  obtain ⟨a, ha, k, rfl⟩ := (q13d_mem_P h hII).mp hp
  have hcomm : Commute a ((t * om) ^ k) :=
    (q13d_gam_comm' h hII a ha).symm.zpow_right k
  have ha4 : a ^ 4 = 1 := q13d_A_pow_four h a ha
  have hg4 : ((t * om) ^ k) ^ 4 = 1 := by
    have hthis := zpow_pow_orderOf (x := t * om) (i := k)
    rwa [q13d_orderOf_gam h] at hthis
  rw [hcomm.mul_pow 4, ha4, hg4, one_mul]

theorem q13d_P_sq_mem_N (h : Q13Om t L S x₁ x₂ lam rho tau om)
    (hII : closure ({t, om} : Set G) ⊓
      centralizer ((q13A t tau x₁ x₂ rho : Subgroup G) : Set G) = zpowers (t * om)) :
    ∀ p ∈ q13P t tau x₁ x₂ rho om, p ^ 2 ∈ ctxN tau x₁ x₂ := by
  intro p hp
  obtain ⟨a, ha, k, rfl⟩ := (q13d_mem_P h hII).mp hp
  have hcomm : Commute a ((t * om) ^ k) :=
    (q13d_gam_comm' h hII a ha).symm.zpow_right k
  have hsq : (a * (t * om) ^ k) ^ 2 = (a * a) * tau ^ k := by
    rw [hcomm.mul_pow 2, show a ^ 2 = a * a by rw [pow_two], q13d_gam_zpow_sq h k]
  rw [hsq]
  exact (ctxN tau x₁ x₂).mul_mem (q13b_V_le_N h (q13d_A_sq_mem_V h a ha))
    ((ctxN tau x₁ x₂).zpow_mem (q13b_tau_mem_N h) k)

theorem q13d_P_sq_eq_one_mem_N (h : Q13Om t L S x₁ x₂ lam rho tau om)
    (hII : closure ({t, om} : Set G) ⊓
      centralizer ((q13A t tau x₁ x₂ rho : Subgroup G) : Set G) = zpowers (t * om)) :
    ∀ p ∈ q13P t tau x₁ x₂ rho om, p ^ 2 = 1 → p ∈ ctxN tau x₁ x₂ := by
  intro p hp hp2
  obtain ⟨a, ha, k, rfl⟩ := (q13d_mem_P h hII).mp hp
  have hcomm : Commute a ((t * om) ^ k) :=
    (q13d_gam_comm' h hII a ha).symm.zpow_right k
  have hprod : (a * a) * tau ^ k = 1 := by
    have hthis := hp2
    rw [hcomm.mul_pow 2, show a ^ 2 = a * a by rw [pow_two], q13d_gam_zpow_sq h k] at hthis
    exact hthis
  have haA : a * a ∈ q13A t tau x₁ x₂ rho := (q13A t tau x₁ x₂ rho).mul_mem ha ha
  rcases Int.even_or_odd' k with ⟨m, hk | hk⟩
  · rw [hk] at hprod ⊢
    have haa : a * a = 1 := by
      rw [q13d_tau_zpow_even h m, mul_one] at hprod
      exact hprod
    have haV : a ∈ fourGrp x₁ x₂ := q13b_omega1_A h a ha haa
    have hgk : (t * om) ^ ((2 : ℤ) * m) ∈ ctxN tau x₁ x₂ := by
      rw [zpow_mul]
      have h2 : (t * om) ^ (2 : ℤ) = tau := by
        rw [zpow_two, ← pow_two]
        exact q13d_gam_sq h
      rw [h2]
      exact (ctxN tau x₁ x₂).zpow_mem (q13b_tau_mem_N h) m
    exact (ctxN tau x₁ x₂).mul_mem (q13b_V_le_N h haV) hgk
  · rw [hk] at hprod
    have hprod' : (a * a) * tau = 1 := by
      rw [q13d_tau_zpow_odd h m] at hprod
      exact hprod
    have haa : a * a = tau := by
      calc a * a = (a * a) * (tau * tau) := by rw [q13a_tau_mul_self h, mul_one]
        _ = ((a * a) * tau) * tau := by group
        _ = 1 * tau := by rw [hprod']
        _ = tau := one_mul tau
    exact absurd (haa ▸ haA) (q13d_tau_not_mem_A h)

end CFSG.OddStandard.SmallF3.HarrisU33.S4B
