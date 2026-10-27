module

public import CFSG.LocalAnalysis.EvenSporadicStandard.HSStd.Zassenhaus.PartA.Basic

public section

namespace CFSG.EvenSporadicStandard.HSStd.Zassenhaus.PartA

open Wreath Equiv

namespace S5W

set_option synthInstance.maxSize 2000 in
set_option synthInstance.maxHeartbeats 400000 in
theorem perm5_commute_sq_aux : ∀ i j : Fin 5, i ≠ j → ∀ c : Perm (Fin 5), c ≠ 1 →
    c * c * c = 1 → swap i j * c = c * swap i j → ∀ a : Perm (Fin 5), a * a = 1 →
    swap i j * a = a * swap i j → c * a = a * c → (a = 1 ∨ a = swap i j) := by
  decide +kernel

theorem perm5_commute_sq {σ c a : Perm (Fin 5)} (hσ : σ.IsSwap) (hc1 : c ≠ 1) (hc3 : c * c * c = 1)
    (hσc : σ * c = c * σ) (ha2 : a * a = 1) (haσ : σ * a = a * σ) (hac : c * a = a * c) :
    a = 1 ∨ a = σ := by
  obtain ⟨i, j, hij, rfl⟩ := hσ
  exact perm5_commute_sq_aux i j hij c hc1 hc3 hσc a ha2 haσ hac

theorem sign_ne_one_of_isSwap {σ : Perm (Fin 5)} (hσ : σ.IsSwap) : Perm.sign σ ≠ 1 := by
  rw [hσ.sign_eq]
  decide

theorem exists_diag_of_commute {σ : Perm (Fin 5)} {x : Wr2 (Perm (Fin 5))}
    (hxt : x * tau = tau * x) (hx3 : x * x * x = 1) (hx1 : x ≠ 1)
    (hxσ : x * base σ σ = base σ σ * x) :
    ∃ c : Perm (Fin 5), x = base c c ∧ c ≠ 1 ∧ c * c * c = 1 ∧ σ * c = c * σ := by
  rcases eq_base_or_eq_base_mul_tau x with ⟨a, b, rfl⟩ | ⟨a, b, rfl⟩
  · have hab : a = b :=
      (mem_centralizer_tau_iff a b).1 (Subgroup.mem_centralizer_singleton_iff.2 hxt)
    subst hab
    rw [base_mul_base, base_mul_base, ← base_one, base_injective] at hx3
    rw [base_mul_base, base_mul_base, base_injective] at hxσ
    refine ⟨a, rfl, ?_, hx3.1, ?_⟩
    · intro h
      apply hx1
      rw [h, base_one]
    · exact hxσ.1.symm
  · exfalso
    have h1 : base a b * tau * (base a b * tau) = base (a * b) (b * a) := base_mul_tau_sq a b
    have h2 : base a b * tau * (base a b * tau) * (base a b * tau) =
        base (a * b * a) (b * a * b) * tau := by
      rw [h1, ← mul_assoc, base_mul_base]
    have : base (1 : Perm (Fin 5)) 1 = base (a * b * a) (b * a * b) * tau := by
      rw [base_one, ← h2, hx3]
    exact base_ne_base_mul_tau _ _ _ _ this

theorem eq_of_commute_conj {σ c : Perm (Fin 5)} (hσ : σ.IsSwap) (hc1 : c ≠ 1)
    (hc3 : c * c * c = 1) (hσc : σ * c = c * σ) {v : Wr2 (Perm (Fin 5))}
    (h1 : v * base σ σ = base σ σ * v) (h2 : v * base c c = base c c * v)
    (h3 : tau * v * tau = base σ σ * v) (h4 : v * v = 1) :
    v = base σ 1 ∨ v = base 1 σ := by
  have hσ2 : σ * σ = 1 := by
    obtain ⟨i, j, hij, rfl⟩ := hσ
    exact swap_mul_self i j
  rcases eq_base_or_eq_base_mul_tau v with ⟨a, b, rfl⟩ | ⟨a, b, rfl⟩
  · rw [tau_mul_base, mul_assoc, tau_mul_tau, mul_one, base_mul_base, base_injective] at h3
    rw [base_mul_base, base_mul_base, base_injective] at h1 h2
    rw [base_mul_base, ← base_one, base_injective] at h4
    have hb : b = σ * a := h3.1
    rcases perm5_commute_sq hσ hc1 hc3 hσc h4.1 h1.1.symm h2.1.symm with ha | ha
    · right
      rw [hb, ha, mul_one]
    · left
      rw [hb, ha, hσ2]
  · exfalso
    have h3' : tau * (base a b * tau) * tau = base b a * tau := by
      rw [mul_assoc, mul_assoc, tau_mul_tau, mul_one, tau_mul_base]
    rw [h3'] at h3
    have h3'' : base b a * tau = base (σ * a) (σ * b) * tau := by
      rw [h3, ← mul_assoc, base_mul_base]
    rw [base_mul_tau_inj] at h3''
    have h1' : base a b * tau * base σ σ = base (a * σ) (b * σ) * tau := by
      rw [mul_assoc, tau_mul_base, ← mul_assoc, base_mul_base]
    have h1'' : base σ σ * (base a b * tau) = base (σ * a) (σ * b) * tau := by
      rw [← mul_assoc, base_mul_base]
    rw [h1', h1'', base_mul_tau_inj] at h1
    rw [base_mul_tau_sq, ← base_one, base_injective] at h4
    have hab : a * (σ * a) = 1 := by rw [← h3''.1]; exact h4.1
    have hs := congrArg (fun w : Perm (Fin 5) => Perm.sign w) hab
    simp only [map_mul, map_one] at hs
    have haa : Perm.sign a * Perm.sign a = 1 := Int.units_mul_self _
    apply sign_ne_one_of_isSwap hσ
    calc Perm.sign σ = Perm.sign a * (Perm.sign σ * Perm.sign a) := by
          rw [mul_comm (Perm.sign σ), ← mul_assoc, haa, one_mul]
      _ = 1 := hs

theorem ne_conj_tau_of_sgnProd {σ : Perm (Fin 5)} (hσ : σ.IsSwap) {d : Wr2 (Perm (Fin 5))}
    (hd : sgnProd d = 1) : d * tau * d⁻¹ ≠ base σ σ * tau := by
  intro h
  have key : ∀ x y : Perm (Fin 5), base x y * tau * (base x y)⁻¹ = base σ σ * tau →
      sgnProd (base x y) = 1 → False := by
    intro x y hxy hsg
    rw [conj_base_tau, base_mul_tau_inj] at hxy
    rw [sgnProd_base] at hsg
    have h1 : Perm.sign (x * y⁻¹) = Perm.sign σ := by rw [hxy.1]
    rw [map_mul, Perm.sign_inv, hsg] at h1
    exact sign_ne_one_of_isSwap hσ h1.symm
  rcases eq_base_or_eq_base_mul_tau d with ⟨x, y, rfl⟩ | ⟨x, y, rfl⟩
  · exact key x y h hd
  · refine key x y ?_ ?_
    · rw [← h]
      simp only [mul_inv_rev, mul_assoc, tau_inv, tau_mul_tau, mul_one]
    · rw [map_mul, sgnProd_tau, mul_one] at hd
      exact hd

end S5W

end CFSG.EvenSporadicStandard.HSStd.Zassenhaus.PartA
