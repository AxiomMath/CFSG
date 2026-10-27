module

public import CFSG.LocalAnalysis.OddStandard.SmallF3.FritzII.FzL410Def
public import CFSG.LocalAnalysis.OddStandard.SmallF3.FritzII.FzL316H0
public import CFSG.LocalAnalysis.OddStandard.SmallF3.FritzII.FzL316P2

public section

namespace CFSG.OddStandard.SmallF3.FritzII

open Subgroup CFSG.OddStandard.SmallF3.HarrisU33
open scoped commutatorElement

structure Fz410Set {G : Type} [Group G] [Finite G] (t : G) (L S T : Subgroup G)
    (x₁ x₂ lam rho tau s : G) (Z E W Q R P : Subgroup G) : Prop where
  ctx : Ctx t L S x₁ x₂ lam rho tau
  card_two : Nat.card (twoCore t) = 2
  isT2 : IsFzT2 t x₁ x₂ S T
  not_sylow : ¬ FzSylow T
  hZ : Z = fourGrp x₁ x₂
  hE : E = baseGrp x₁ x₂
  hW : W = ctxW t x₁ x₂
  hQ : Q = fzQ t x₁ x₂ rho
  hR : R = fzR t x₁ x₂
  str : FzStr t tau lam rho Z E W Q R T
  pf : FzPFacts t tau rho E W Q T P
  t_notin_P : t ∉ P
  exF : ∃ f : ↥(fzN2 t x₁ x₂) →* FzZ2xSigma4, FzF t x₁ x₂ f
  s_cases : s = tau ∨ s = t * tau
  facts : Fz410Facts t s Z E P Q R T

namespace Fz410Set

variable {G : Type} [Group G] [Finite G] {t : G} {L S T : Subgroup G}
  {x₁ x₂ lam rho tau s : G} {Z E W Q R P : Subgroup G}
  (D : Fz410Set t L S T x₁ x₂ lam rho tau s Z E W Q R P)

include D

theorem t_mem_R : t ∈ R := D.str.QR (D.str.WQ D.str.t_mem)

theorem s_mem_R : s ∈ R := by
  rcases D.s_cases with h | h
  · rw [h]; exact D.str.tau_R
  · rw [h]; exact R.mul_mem D.t_mem_R D.str.tau_R

private theorem tau_comm_t : tau * t = t * tau := by
  have h := D.str.tau_t
  calc tau * t = tau * t * tau⁻¹ * tau := by group
    _ = t * tau := by rw [h]

theorem s_sq : s ^ 2 = 1 := by
  have hτ : tau ^ 2 = 1 := D.pf.tau_sq1
  have ht2 : t ^ 2 = 1 := D.str.t_sq
  rcases D.s_cases with h | h
  · rw [h]; exact hτ
  · rw [h]
    calc (t * tau) ^ 2 = t * tau * (t * tau) := pow_two _
      _ = t * (tau * t) * tau := by group
      _ = t * (t * tau) * tau := by rw [D.tau_comm_t]
      _ = t ^ 2 * tau ^ 2 := by simp only [pow_two, mul_assoc]
      _ = 1 := by rw [ht2, hτ, one_mul]

theorem s_comm_t : s * t = t * s := by
  rcases D.s_cases with h | h
  · rw [h]; exact D.tau_comm_t
  · rw [h]
    calc t * tau * t = t * (tau * t) := by group
      _ = t * (t * tau) := by rw [D.tau_comm_t]
      _ = t * (t * tau) := rfl

theorem ts_notin_P : t * s ∉ P := by
  have htQ : t ∈ Q := D.str.WQ D.str.t_mem
  intro hP
  have hQ' : t * s ∈ Q := D.pf.PQ hP
  rcases D.s_cases with h | h
  · rw [h] at hQ'
    apply D.str.tau_notin_Q
    have := Q.mul_mem (Q.inv_mem htQ) hQ'
    simpa using this
  · rw [h] at hQ'
    apply D.str.tau_notin_Q
    have ht2 : t * (t * tau) = tau := by
      calc t * (t * tau) = t ^ 2 * tau := by simp only [pow_two, mul_assoc]
        _ = tau := by rw [D.str.t_sq, one_mul]
    rwa [ht2] at hQ'

theorem Z_le_P : Z ≤ P := D.str.ZE.trans D.pf.EP

theorem E_cent : ∀ a ∈ P, (a * t = t * a ↔ a ∈ E) := by
  intro a ha
  constructor
  · intro hc
    have haQ : a ∈ Q := D.pf.PQ ha
    by_cases haW : a ∈ W
    · exact D.pf.PW a ha haW
    · exfalso
      apply D.str.Q_t a haQ haW
      calc a * t * a⁻¹ = t * a * a⁻¹ := by rw [hc]
        _ = t := by group
  · intro haE
    exact D.str.W_comm a (D.str.EW haE) t D.str.t_mem

theorem s_inv_E : ∀ e ∈ E, s * e * s⁻¹ = e⁻¹ := by
  intro e he
  have heW : e ∈ W := D.str.EW he
  have hte : t * e = e * t := (D.str.W_comm t D.str.t_mem e heW)
  rcases D.s_cases with h | h
  · rw [h]; exact D.str.tau_W e heW
  · rw [h]
    calc t * tau * e * (t * tau)⁻¹ = t * (tau * e * tau⁻¹) * t⁻¹ := by group
      _ = t * e⁻¹ * t⁻¹ := by rw [D.str.tau_W e heW]
      _ = e⁻¹ := by
        have : t * e⁻¹ = e⁻¹ * t := by
          have h2 : e * t = t * e := hte.symm
          calc t * e⁻¹ = e⁻¹ * (e * t) * e⁻¹ := by group
            _ = e⁻¹ * (t * e) * e⁻¹ := by rw [h2]
            _ = e⁻¹ * t := by group
        rw [this]; group

theorem ets_sq : ∀ e ∈ E, (e * (t * s)) ^ 2 = 1 := by
  intro e he
  have hse := D.s_inv_E e he
  have hte : t * e = e * t := D.str.W_comm t D.str.t_mem e (D.str.EW he)
  have hst := D.s_comm_t
  have hs2 := D.s_sq
  have ht2 := D.str.t_sq
  have h1 : s * e = e⁻¹ * s := by
    calc s * e = s * e * s⁻¹ * s := by group
      _ = e⁻¹ * s := by rw [hse]
  have h2 : t * e⁻¹ = e⁻¹ * t := by
    calc t * e⁻¹ = e⁻¹ * (e * t) * e⁻¹ := by group
      _ = e⁻¹ * (t * e) * e⁻¹ := by rw [← hte]
      _ = e⁻¹ * t := by group
  calc (e * (t * s)) ^ 2 = e * (t * (s * e)) * (t * s) := by rw [pow_two]; group
    _ = e * (t * (e⁻¹ * s)) * (t * s) := by rw [h1]
    _ = e * (t * e⁻¹) * (s * (t * s)) := by group
    _ = e * (e⁻¹ * t) * (s * (t * s)) := by rw [h2]
    _ = t * (s * (t * s)) := by group
    _ = t * ((s * t) * s) := by group
    _ = t * ((t * s) * s) := by rw [hst]
    _ = t ^ 2 * s ^ 2 := by simp only [pow_two, mul_assoc]
    _ = 1 := by rw [ht2, hs2, one_mul]

theorem exists_E_not_Z : ∃ a ∈ E, a ∉ Z := by
  by_contra hcon
  have hle : E ≤ Z := fun a ha => by_contra (fun h => hcon ⟨a, ha, h⟩)
  have := Subgroup.card_le_of_le hle
  rw [D.str.card_E, D.str.card_Z] at this
  omega

theorem exists_E_sq_ne_one : ∃ e ∈ E, e ^ 2 ≠ 1 := by
  have hcard : 1 < Nat.card Z := by rw [D.str.card_Z]; norm_num
  obtain ⟨z, hz, hz1⟩ := (Subgroup.one_lt_card_iff_ne_bot Z |>.mp hcard |> fun h =>
    Subgroup.bot_or_exists_ne_one Z |>.resolve_left h)
  obtain ⟨e, he, hez⟩ := D.str.Z_sqrt z hz
  exact ⟨e, he, by rw [hez]; exact hz1⟩

end Fz410Set

end CFSG.OddStandard.SmallF3.FritzII
