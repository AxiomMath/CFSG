module

public import CFSG.LocalAnalysis.OddStandard.SmallF3.U33.Sec4A.S4AC16P
public import CFSG.LocalAnalysis.OddStandard.SmallF3.U33.Sec4A.S4AQ14A

public section

namespace CFSG.OddStandard.SmallF3.HarrisU33.S4A

open Subgroup
open scoped commutatorElement

variable {G : Type} [Group G] {K Y Q : Subgroup G} {t rho z u fz fu : G}

private lemma c16_theta_Nu (σ : C16H0) : c16Theta (c16Nu σ) = c16Nu σ := by
  revert σ; decide

private lemma c16_theta_zero : c16Theta (0 : C16H0) = 0 := by decide

theorem c16_beta_qm [Finite G] (H : C16Ab K Y Q t rho z u fz fu) {R : Subgroup G}
    (hR : ∀ r, r ∈ R ↔ r ∈ Q ∧ ∀ f ∈ Y, r * f = f * r) (hR3 : ¬ 3 ∣ Nat.card R)
    (hQt : ∀ x ∈ Q, rho * x * rho⁻¹ = x → x = 1 ∨ x = t) :
    ∀ q ∈ Q, c16Qm (c16Beta z u fz fu q) := by
  intro q hq
  unfold c16Qm
  let q₁ : G := rho * q * rho⁻¹
  let q₂ : G := rho * q₁ * rho⁻¹
  let w : G := q * q₁ * q₂
  have hq₁ : q₁ ∈ Q := H.rho_Q q hq
  have hq₂ : q₂ ∈ Q := H.rho_Q q₁ hq₁
  have hwQ : w ∈ Q := by
    dsimp [w]
    exact Q.mul_mem (Q.mul_mem hq hq₁) hq₂
  have hq₁_eq : c16Beta z u fz fu q₁ = c16Theta (c16Beta z u fz fu q) := by
    dsimp [q₁]
    exact c16_beta_rho H hq
  have hq₂_eq : c16Beta z u fz fu q₂
      = c16Theta (c16Theta (c16Beta z u fz fu q)) := by
    dsimp [q₂]
    rw [c16_beta_rho H hq₁, hq₁_eq]
  have hbetaw : c16Beta z u fz fu w = c16Nu (c16Beta z u fz fu q) := by
    have h : w = q * (q₁ * q₂) := by
      dsimp [w]
      rw [mul_assoc]
    rw [h, c16_beta_add H hq (Q.mul_mem hq₁ hq₂), c16_beta_add H hq₁ hq₂,
      hq₁_eq, hq₂_eq]
    unfold c16Nu
    simp only [add_assoc]
  have hRinv : ∀ n ∈ R, rho * n * rho⁻¹ ∈ R := by
    intro n hn
    obtain ⟨hnQ, hncent⟩ := (hR n).mp hn
    have hbeta0 : c16Beta z u fz fu n = 0 :=
      (c16_beta_eq_zero_iff H hnQ).mpr hncent
    have hbeta1 : c16Beta z u fz fu (rho * n * rho⁻¹) = 0 := by
      rw [c16_beta_rho H hnQ, hbeta0, c16_theta_zero]
    exact (hR _).mpr
      ⟨H.rho_Q n hnQ, (c16_beta_eq_zero_iff H (H.rho_Q n hnQ)).mp hbeta1⟩
  have hwconjR : rho * w * rho⁻¹ * w⁻¹ ∈ R := by
    have hQ1 : rho * w * rho⁻¹ ∈ Q := H.rho_Q w hwQ
    have hQ2 : w⁻¹ ∈ Q := Q.inv_mem hwQ
    have hQ3 : rho * w * rho⁻¹ * w⁻¹ ∈ Q := Q.mul_mem hQ1 hQ2
    refine (hR _).mpr ⟨hQ3, ?_⟩
    have hbeta : c16Beta z u fz fu (rho * w * rho⁻¹ * w⁻¹) = 0 := by
      rw [c16_beta_add H hQ1 hQ2, c16_beta_rho H hwQ, c16_beta_inv H hwQ,
        hbetaw, c16_theta_Nu]
      exact c16_add_self _
    exact (c16_beta_eq_zero_iff H hQ3).mp hbeta
  obtain ⟨x, hxwR, hxfix⟩ :=
    q14_exists_fixed_coset (N := R) H.rho_cube hRinv hR3 hwconjR
  have hxwQ : x * w⁻¹ ∈ Q := ((hR _).mp hxwR).1
  have hxwcent : ∀ f ∈ Y, (x * w⁻¹) * f = f * (x * w⁻¹) := ((hR _).mp hxwR).2
  have hxQ : x ∈ Q := by
    have hx : x = (x * w⁻¹) * w := by group
    rw [hx]
    exact Q.mul_mem hxwQ hwQ
  have hbetaxw : c16Beta z u fz fu (x * w⁻¹) = 0 :=
    (c16_beta_eq_zero_iff H hxwQ).mpr hxwcent
  have hbetax : c16Beta z u fz fu x = c16Nu (c16Beta z u fz fu q) := by
    have hx : x = (x * w⁻¹) * w := by group
    rw [hx, c16_beta_add H hxwQ hwQ, hbetaxw, zero_add, hbetaw]
  rcases hQt x hxQ hxfix with hx1 | hxt
  · left
    rw [← hbetax, hx1]
    exact c16_beta_one z u fz fu
  · right
    rw [← hbetax, hxt]
    exact c16_beta_t H

end CFSG.OddStandard.SmallF3.HarrisU33.S4A
