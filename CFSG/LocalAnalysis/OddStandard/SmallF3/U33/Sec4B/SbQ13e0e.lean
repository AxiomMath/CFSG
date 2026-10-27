module

public import CFSG.LocalAnalysis.OddStandard.SmallF3.U33.Sec4B.SbQ13e0e0
public import CFSG.LocalAnalysis.OddStandard.SmallF3.U33.Sec4B.SbQ13e0b
public import CFSG.LocalAnalysis.OddStandard.SmallF3.U33.Sec4B.SbQ13e0a

public section

namespace CFSG.OddStandard.SmallF3.HarrisU33.S4B

open Subgroup
open scoped Pointwise

variable {G : Type} [Group G]

@[expose] def q13H1 (t tau x₁ x₂ lam rho : G) : Subgroup G :=
  zpowers tau ⊔ (q13A t tau x₁ x₂ rho ⊓ centralizer ({lam} : Set G))

variable [Finite G] {t : G} {L S : Subgroup G} {x₁ x₂ lam rho tau om : G}

private theorem q13e_mem_zpowers_tau (h : Q13Om t L S x₁ x₂ lam rho tau om) {k : G}
    (hk : k ∈ zpowers tau) : k = 1 ∨ k = tau := by
  obtain ⟨m, rfl⟩ := Subgroup.mem_zpowers_iff.mp hk
  rw [zpow_eq_zpow_emod' m (show tau ^ 2 = 1 by rw [pow_two]; exact q13a_tau_mul_self h)]
  rcases Int.emod_two_eq_zero_or_one m with hm | hm
  · left
    have hm' : m % ((2 : ℕ) : ℤ) = 0 := by simpa using hm
    rw [hm', zpow_zero]
  · right
    have hm' : m % ((2 : ℕ) : ℤ) = 1 := by simpa using hm
    rw [hm', zpow_one]

private lemma q13e_rotate {x y z : G} (hxy : x * y = y * x) (hxz : x * z = z * x) :
    x * y * z = y * z * x := by
  calc x * y * z = (x * y) * z := rfl
    _ = (y * x) * z := by rw [hxy]
    _ = y * (x * z) := by rw [mul_assoc]
    _ = y * (z * x) := by rw [hxz]
    _ = (y * z) * x := by rw [mul_assoc]

private theorem q13e_f_gam_zpow (h : Q13Om t L S x₁ x₂ lam rho tau om)
    (hC : Q13C t x₁ x₂ lam tau om) (k : ℤ) :
    (t * lam) * (t * om) ^ k * (t * lam)⁻¹ = ((t * om) ^ k)⁻¹ := by
  have h1 : (t * lam) * (t * om) * (t * lam)⁻¹ = (t * om)⁻¹ := q13e_f_gam h hC
  calc (t * lam) * (t * om) ^ k * (t * lam)⁻¹
      = ((t * lam) * (t * om) * (t * lam)⁻¹) ^ k := by rw [conj_zpow]
    _ = ((t * om)⁻¹) ^ k := by rw [h1]
    _ = ((t * om) ^ k)⁻¹ := by rw [inv_zpow]

private theorem q13e_tau_shift (h : Q13Om t L S x₁ x₂ lam rho tau om) {a b : G}
    (ha : a ∈ q13A t tau x₁ x₂ rho) (hb : b ∈ q13A t tau x₁ x₂ rho) :
    (a * tau) * (b * tau) = a * b := by
  have h1 : a * tau = tau * a := q13d_A_cent_tau h a ha
  have h2 : b * tau = tau * b := q13d_A_cent_tau h b hb
  calc (a * tau) * (b * tau) = a * (tau * b) * tau := by group
    _ = a * (b * tau) * tau := by rw [← h2]
    _ = a * b * (tau * tau) := by group
    _ = a * b := by rw [q13a_tau_mul_self h, mul_one]

private theorem q13e_cocycle (h : Q13Om t L S x₁ x₂ lam rho tau om)
    (hC : Q13C t x₁ x₂ lam tau om) (hD : Q13D t x₁ x₂ lam rho tau om)
    {a : G} (ha : a ∈ q13A t tau x₁ x₂ rho) (k : ℤ) :
    (t * lam) * (a * (t * om) ^ k) * (t * lam)⁻¹ * (a * (t * om) ^ k)⁻¹ =
      ((t * om) ^ 2) ^ (-k) * (a * (lam * a * lam⁻¹))⁻¹ := by
  have hfa : (t * lam) * a * (t * lam)⁻¹ = (lam * a * lam⁻¹)⁻¹ := q13e_f_A h a ha
  have hfg : (t * lam) * (t * om) ^ k * (t * lam)⁻¹ = ((t * om) ^ k)⁻¹ :=
    q13e_f_gam_zpow h hC k
  have hBP : (lam * a * lam⁻¹)⁻¹ ∈ q13P t tau x₁ x₂ rho om :=
    q13d_A_le_P h (Subgroup.inv_mem (q13A t tau x₁ x₂ rho) (q13a_A_inv h a ha).2.1)
  have hgk_invP : ((t * om) ^ k)⁻¹ ∈ q13P t tau x₁ x₂ rho om :=
    Subgroup.inv_mem _ (Subgroup.zpow_mem (q13P t tau x₁ x₂ rho om) (q13d_gam_mem_P h) k)
  have hcomm : (lam * a * lam⁻¹)⁻¹ * ((t * om) ^ k)⁻¹ =
      ((t * om) ^ k)⁻¹ * (lam * a * lam⁻¹)⁻¹ :=
    q13d_P_comm h hD.A_cent _ hBP _ hgk_invP
  have hG2 : ((t * om) ^ k)⁻¹ * ((t * om) ^ k)⁻¹ = ((t * om) ^ 2) ^ (-k) := by
    have hg2 : (t * om) ^ (2 : ℤ) = (t * om) ^ 2 := zpow_natCast (t * om) 2
    rw [← hg2, ← zpow_mul, ← zpow_neg, ← zpow_add]
    congr 1
    ring
  have hBa : (lam * a * lam⁻¹)⁻¹ * a⁻¹ = (a * (lam * a * lam⁻¹))⁻¹ := by
    group
  calc (t * lam) * (a * (t * om) ^ k) * (t * lam)⁻¹ * (a * (t * om) ^ k)⁻¹
      = ((t * lam) * a * (t * lam)⁻¹) * ((t * lam) * (t * om) ^ k * (t * lam)⁻¹)
          * ((t * om) ^ k)⁻¹ * a⁻¹ := by
          rw [mul_inv_rev]; group
    _ = (lam * a * lam⁻¹)⁻¹ * ((t * om) ^ k)⁻¹ * ((t * om) ^ k)⁻¹ * a⁻¹ := by
          rw [hfa, hfg]
    _ = ((t * om) ^ k)⁻¹ * ((t * om) ^ k)⁻¹ * (lam * a * lam⁻¹)⁻¹ * a⁻¹ := by
          rw [q13e_rotate hcomm hcomm]
    _ = (((t * om) ^ k)⁻¹ * ((t * om) ^ k)⁻¹) * ((lam * a * lam⁻¹)⁻¹ * a⁻¹) := by
          rw [mul_assoc]
    _ = ((t * om) ^ 2) ^ (-k) * (a * (lam * a * lam⁻¹))⁻¹ := by rw [hG2, hBa]

private theorem q13e_Z1_compute (h : Q13Om t L S x₁ x₂ lam rho tau om)
    (hC : Q13C t x₁ x₂ lam tau om) (hD : Q13D t x₁ x₂ lam rho tau om)
    {a : G} (ha : a ∈ q13A t tau x₁ x₂ rho) (k : ℤ) :
    (a * (t * om) ^ k) * ((t * lam) * (a * (t * om) ^ k) * (t * lam)⁻¹) =
      a * (lam * a * lam⁻¹)⁻¹ := by
  have hfa : (t * lam) * a * (t * lam)⁻¹ = (lam * a * lam⁻¹)⁻¹ := q13e_f_A h a ha
  have hfg : (t * lam) * (t * om) ^ k * (t * lam)⁻¹ = ((t * om) ^ k)⁻¹ :=
    q13e_f_gam_zpow h hC k
  have hBP : (lam * a * lam⁻¹)⁻¹ ∈ q13P t tau x₁ x₂ rho om :=
    q13d_A_le_P h (Subgroup.inv_mem (q13A t tau x₁ x₂ rho) (q13a_A_inv h a ha).2.1)
  have hgkP : (t * om) ^ k ∈ q13P t tau x₁ x₂ rho om :=
    Subgroup.zpow_mem (q13P t tau x₁ x₂ rho om) (q13d_gam_mem_P h) k
  have hcomm : (t * om) ^ k * (lam * a * lam⁻¹)⁻¹ =
      (lam * a * lam⁻¹)⁻¹ * (t * om) ^ k :=
    q13d_P_comm h hD.A_cent _ hgkP _ hBP
  have hinner : (t * om) ^ k * ((lam * a * lam⁻¹)⁻¹ * ((t * om) ^ k)⁻¹) =
      (lam * a * lam⁻¹)⁻¹ := by
    rw [← mul_assoc, hcomm, mul_assoc, mul_inv_cancel, mul_one]
  calc (a * (t * om) ^ k) * ((t * lam) * (a * (t * om) ^ k) * (t * lam)⁻¹)
      = (a * (t * om) ^ k) * (((t * lam) * a * (t * lam)⁻¹) *
          ((t * lam) * (t * om) ^ k * (t * lam)⁻¹)) := by group
    _ = (a * (t * om) ^ k) * ((lam * a * lam⁻¹)⁻¹ * ((t * om) ^ k)⁻¹) := by
          rw [hfa, hfg]
    _ = a * ((t * om) ^ k * ((lam * a * lam⁻¹)⁻¹ * ((t * om) ^ k)⁻¹)) := by group
    _ = a * (lam * a * lam⁻¹)⁻¹ := by rw [hinner]

private lemma q13e_mul_zpow_tau_mem_H1 (h : Q13Om t L S x₁ x₂ lam rho tau om) {a : G}
    (ha : a ∈ q13A t tau x₁ x₂ rho ⊓ centralizer ({lam} : Set G)) (m : ℤ) :
    a * tau ^ m ∈ q13H1 t tau x₁ x₂ lam rho := by
  have haA : a ∈ q13A t tau x₁ x₂ rho := (Subgroup.mem_inf.mp ha).1
  have hcomm : a * tau ^ m = tau ^ m * a :=
    (Commute.zpow_right (q13d_A_cent_tau h a haA) m).eq
  rw [q13H1, hcomm]
  exact Subgroup.mul_mem_sup (Subgroup.zpow_mem (zpowers tau) (Subgroup.mem_zpowers tau) m) ha

theorem q13e_mem_H1 (h : Q13Om t L S x₁ x₂ lam rho tau om) {p : G} :
    p ∈ q13H1 t tau x₁ x₂ lam rho ↔ ∃ c ∈ (q13A t tau x₁ x₂ rho ⊓ centralizer ({lam} : Set G)),
      p = c ∨ p = tau * c := by
  have hnorm : ∀ k ∈ (q13A t tau x₁ x₂ rho ⊓ centralizer ({lam} : Set G)),
      ∀ h' ∈ zpowers tau, k * h' * k⁻¹ ∈ zpowers tau := by
    intro k hk h' hh'
    have hkA : k ∈ q13A t tau x₁ x₂ rho := (Subgroup.mem_inf.mp hk).1
    rcases q13e_mem_zpowers_tau h hh' with h1 | ht
    · rw [h1, mul_one, mul_inv_cancel]
      exact Subgroup.one_mem _
    · rw [ht, q13d_A_cent_tau h k hkA]
      rw [show tau * k * k⁻¹ = tau by group]
      exact Subgroup.mem_zpowers tau
  rw [q13H1, mem_sup_iff_of_normalizes (H := zpowers tau)
        (K := q13A t tau x₁ x₂ rho ⊓ centralizer ({lam} : Set G)) hnorm]
  constructor
  · rintro ⟨h', hh', c, hc, heq⟩
    rcases q13e_mem_zpowers_tau h hh' with h1 | ht
    · exact ⟨c, hc, Or.inl (by rw [heq, h1, one_mul])⟩
    · exact ⟨c, hc, Or.inr (by rw [heq, ht])⟩
  · rintro ⟨c, hc, h1 | ht⟩
    · exact ⟨1, Subgroup.one_mem _, c, hc, by rw [h1, one_mul]⟩
    · exact ⟨tau, Subgroup.mem_zpowers tau, c, hc, ht⟩

theorem q13e_H1_le_AN : q13H1 t tau x₁ x₂ lam rho ≤ q13AN t tau x₁ x₂ rho := by
  rw [q13H1]
  refine sup_le ?_ ?_
  · exact Subgroup.zpowers_le.mpr q13e_tau_mem_AN
  · exact inf_le_left.trans q13e_A_le_AN

theorem q13e_P_of_H1 (h : Q13Om t L S x₁ x₂ lam rho tau om) (hC : Q13C t x₁ x₂ lam tau om)
    (hD : Q13D t x₁ x₂ lam rho tau om) :
    ∀ p ∈ q13H1 t tau x₁ x₂ lam rho, ∃ q ∈ q13P t tau x₁ x₂ rho om,
      p = (t * lam) * q * (t * lam)⁻¹ * q⁻¹ := by
  intro p hp
  obtain ⟨c, hc, hpc | hpc⟩ := (q13e_mem_H1 h).mp hp
  · obtain ⟨a, ha, haeq⟩ := q13e_Ap_onto h c⁻¹ (Subgroup.inv_mem _ hc)
    refine ⟨a, q13d_A_le_P h ha, ?_⟩
    rw [hpc, q13e_f_A h a ha]
    have hc_eq : (lam * a * lam⁻¹)⁻¹ * a⁻¹ = c := by
      rw [← mul_inv_rev, haeq, inv_inv]
    exact hc_eq.symm
  · obtain ⟨a, ha, haeq⟩ := q13e_Ap_onto h c⁻¹ (Subgroup.inv_mem _ hc)
    refine ⟨a * (t * om) ^ (1 : ℤ), Subgroup.mul_mem _ (q13d_A_le_P h ha)
      (Subgroup.zpow_mem (q13P t tau x₁ x₂ rho om) (q13d_gam_mem_P h) 1), ?_⟩
    rw [hpc, q13e_cocycle h hC hD ha 1]
    rw [haeq, inv_inv, hD.gam_sq]
    have htau1 : tau ^ (-1 : ℤ) = tau := by
      rw [zpow_neg_one]
      exact inv_eq_of_mul_eq_one_right (q13a_tau_mul_self h)
    rw [htau1]

theorem q13e_Z1_AN (h : Q13Om t L S x₁ x₂ lam rho tau om) :
    ∀ p ∈ q13AN t tau x₁ x₂ rho,
      p * ((t * lam) * p * (t * lam)⁻¹) = 1 → p ∈ q13H1 t tau x₁ x₂ lam rho := by
  intro p hp h1
  obtain ⟨a, ha, hp_eq | hp_eq⟩ := (q13e_mem_AN' h).mp hp
  · have hfa : (t * lam) * a * (t * lam)⁻¹ = (lam * a * lam⁻¹)⁻¹ := q13e_f_A h a ha
    have ha1 : a * (lam * a * lam⁻¹)⁻¹ = 1 := by
      rw [← hfa]
      rw [hp_eq] at h1
      exact h1
    have halam : a = lam * a * lam⁻¹ := mul_inv_eq_one.mp ha1
    have haAp : a ∈ q13A t tau x₁ x₂ rho ⊓ centralizer ({lam} : Set G) :=
      ⟨ha, Subgroup.mem_centralizer_singleton_iff.mpr (by nth_rewrite 1 [halam]; group)⟩
    rw [hp_eq, q13H1]
    exact Subgroup.mem_sup_right haAp
  · have hfa : (t * lam) * a * (t * lam)⁻¹ = (lam * a * lam⁻¹)⁻¹ := q13e_f_A h a ha
    have hftau : (t * lam) * tau * (t * lam)⁻¹ = tau := q13e_f_tau h
    have hbA : (lam * a * lam⁻¹)⁻¹ ∈ q13A t tau x₁ x₂ rho :=
      Subgroup.inv_mem _ (q13a_A_inv h a ha).2.1
    have hprod : (a * tau) * ((t * lam) * (a * tau) * (t * lam)⁻¹) =
        a * (lam * a * lam⁻¹)⁻¹ := by
      have hexp : (t * lam) * (a * tau) * (t * lam)⁻¹ =
          ((t * lam) * a * (t * lam)⁻¹) * ((t * lam) * tau * (t * lam)⁻¹) := by group
      rw [hexp, hfa, hftau]
      exact q13e_tau_shift h ha hbA
    have ha1 : a * (lam * a * lam⁻¹)⁻¹ = 1 := by
      rw [← hprod]
      rw [hp_eq] at h1
      exact h1
    have halam : a = lam * a * lam⁻¹ := mul_inv_eq_one.mp ha1
    have haAp : a ∈ q13A t tau x₁ x₂ rho ⊓ centralizer ({lam} : Set G) :=
      ⟨ha, Subgroup.mem_centralizer_singleton_iff.mpr (by nth_rewrite 1 [halam]; group)⟩
    rw [hp_eq, q13H1, q13d_A_cent_tau h a ha]
    exact Subgroup.mul_mem_sup (Subgroup.mem_zpowers tau) haAp

theorem q13e_Z1_P (h : Q13Om t L S x₁ x₂ lam rho tau om) (hC : Q13C t x₁ x₂ lam tau om)
    (hD : Q13D t x₁ x₂ lam rho tau om) :
    ∀ p ∈ q13P t tau x₁ x₂ rho om,
      p * ((t * lam) * p * (t * lam)⁻¹) = 1 →
      p ∈ q13H1 t tau x₁ x₂ lam rho ∨ (t * om)⁻¹ * p ∈ q13H1 t tau x₁ x₂ lam rho := by
  intro p hp h1
  obtain ⟨a, ha, k, rfl⟩ := (q13d_mem_P h hD.A_cent).mp hp
  have hZ := q13e_Z1_compute h hC hD ha k
  have ha1 : a * (lam * a * lam⁻¹)⁻¹ = 1 := by
    rw [← hZ]
    exact h1
  have halam : a = lam * a * lam⁻¹ := mul_inv_eq_one.mp ha1
  have haAp : a ∈ q13A t tau x₁ x₂ rho ⊓ centralizer ({lam} : Set G) :=
    ⟨ha, Subgroup.mem_centralizer_singleton_iff.mpr (by nth_rewrite 1 [halam]; group)⟩
  rcases Int.even_or_odd' k with ⟨m, hk | hk⟩
  · left
    have hg2 : (t * om) ^ (2 : ℤ) = (t * om) ^ 2 := zpow_natCast (t * om) 2
    have hgk : (t * om) ^ k = tau ^ m := by rw [hk, zpow_mul, hg2, hD.gam_sq]
    rw [hgk]
    exact q13e_mul_zpow_tau_mem_H1 h haAp m
  · right
    have hga : (t * om) * a = a * (t * om) := q13d_gam_cent_A h hD.A_cent a ha
    have hgainv : (t * om)⁻¹ * a = a * (t * om)⁻¹ := by
      calc (t * om)⁻¹ * a = (t * om)⁻¹ * a * (t * om) * (t * om)⁻¹ := by group
        _ = (t * om)⁻¹ * (a * (t * om)) * (t * om)⁻¹ := by group
        _ = (t * om)⁻¹ * ((t * om) * a) * (t * om)⁻¹ := by rw [hga]
        _ = a * (t * om)⁻¹ := by group
    have hstep : (t * om)⁻¹ * (a * (t * om) ^ k) =
        a * ((t * om)⁻¹ * (t * om) ^ k) := by
      rw [← mul_assoc, hgainv, mul_assoc]
    have hcancel : (t * om)⁻¹ * (t * om) ^ k = (t * om) ^ (k - 1) := by
      rw [← zpow_neg_one, ← zpow_add]
      congr 1
      ring
    have hk1 : k - 1 = 2 * m := by rw [hk]; ring
    have hgoal : (t * om)⁻¹ * (a * (t * om) ^ k) = a * tau ^ m := by
      have hg2 : (t * om) ^ (2 : ℤ) = (t * om) ^ 2 := zpow_natCast (t * om) 2
      rw [hstep, hcancel, hk1, zpow_mul, hg2, hD.gam_sq]
    rw [hgoal]
    exact q13e_mul_zpow_tau_mem_H1 h haAp m

end CFSG.OddStandard.SmallF3.HarrisU33.S4B
