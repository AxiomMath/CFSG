module

public import CFSG.LocalAnalysis.EvenSmallLie.OmegaEight.SplitInStage1D

public section

namespace CFSG.EvenSmallLie.OmegaEight.SplitIn

open Subgroup Matrix CFSG.EvenSmallLie.OmegaEight.Stage1
open CFSG.EvenSmallLie.UnitarySix.YamadaPar

variable {G : Type} [Group G]

namespace SetupX

variable {ε : Eps} {t : G} {L H₀ U Q P : Subgroup G} {a : G} {ψ : V6 → G} {p u : Fin 6 → G}
  {x₀ : G} (hS : SetupX ε t L H₀ U Q P a ψ p u x₀)
  (hZ : ∀ v, v ∈ Zset t Q ψ)
include hS

omit hS in
theorem D_comm_Q {d : G} (hd : d ∈ Dsub t Q) {q : G} (hq : q ∈ Q) : d * q = q * d :=
  (mem_centralizer_iff.1 hd.2 q hq).symm

include hZ

theorem mul_self_mem_Q {x : G} (hx : x ∈ Dsub t Q) : x * x ∈ Q := by
  have hxx : x * x ∈ (Q ⊔ zpowers t : Subgroup G) := by
    rw [← hS.tauD_eq_zero_iff hZ (mul_mem hx hx), hS.tauD_mul hZ hx hx,
      CharTwo.add_self_eq_zero]
  obtain ⟨v, h | h⟩ := hS.mem_E_iff.1 hxx
  · exact h ▸ hS.rad.ψ_mem v
  · exfalso
    obtain ⟨g, -, hg⟩ := hZ v
    apply hS.shape.not_square (g⁻¹ * x * g)
    calc g⁻¹ * x * g * (g⁻¹ * x * g) = g⁻¹ * (x * x) * g := by group
      _ = g⁻¹ * (g * t * g⁻¹) * g := by rw [h, hg]
      _ = t := by group

theorem kap_mem_Q {x y : G} (hx : x ∈ Dsub t Q) (hy : y ∈ Dsub t Q) : kap x y ∈ Q := by
  have h1 := hS.mul_self_mem_Q hZ (mul_mem hx hy)
  have h2 := hS.mul_self_mem_Q hZ hx
  have h3 := hS.mul_self_mem_Q hZ hy
  have hc : y⁻¹ * (x * x)⁻¹ = (x * x)⁻¹ * y⁻¹ :=
    (D_comm_Q (inv_mem hy) (inv_mem h2))
  have : kap x y = x * y * (x * y) * ((x * x)⁻¹ * (y * y)⁻¹) := by
    calc kap x y = x * y * (x * y) * (y⁻¹ * (x * x)⁻¹ * y⁻¹) := by rw [kap]; group
      _ = x * y * (x * y) * ((x * x)⁻¹ * y⁻¹ * y⁻¹) := by rw [hc]
      _ = x * y * (x * y) * ((x * x)⁻¹ * (y * y)⁻¹) := by group
  rw [this]
  exact mul_mem h1 (mul_mem (inv_mem h2) (inv_mem h3))

theorem kap_mul_left {x x' y : G} (hx : x ∈ Dsub t Q) (hx' : x' ∈ Dsub t Q)
    (hy : y ∈ Dsub t Q) : kap (x * x') y = kap x y * kap x' y := by
  have hc : x * kap x' y = kap x' y * x := D_comm_Q hx (hS.kap_mem_Q hZ hx' hy)
  have hQ := hS.rad.Q_comm (hS.kap_mem_Q hZ hx hy) (hS.kap_mem_Q hZ hx' hy)
  calc kap (x * x') y = x * kap x' y * y * x⁻¹ * y⁻¹ := by rw [kap, kap]; group
    _ = kap x' y * (x * y * x⁻¹ * y⁻¹) := by rw [hc]; group
    _ = kap x y * kap x' y := by rw [← kap, hQ]

theorem kap_mul_right {x y y' : G} (hx : x ∈ Dsub t Q) (hy : y ∈ Dsub t Q)
    (hy' : y' ∈ Dsub t Q) : kap x (y * y') = kap x y * kap x y' := by
  have hc : y * kap x y' = kap x y' * y := D_comm_Q hy (hS.kap_mem_Q hZ hx hy')
  calc kap x (y * y') = kap x y * (y * kap x y' * y⁻¹) := by rw [kap, kap, kap]; group
    _ = kap x y * kap x y' := by rw [hc]; group

theorem kap_symm {x y : G} (hx : x ∈ Dsub t Q) (hy : y ∈ Dsub t Q) : kap y x = kap x y := by
  have h : kap y x = (kap x y)⁻¹ := by rw [kap, kap]; group
  rw [h]
  exact inv_eq_of_mul_eq_one_right (hS.rad.Q_mul_self (hS.kap_mem_Q hZ hx hy))

omit hZ in
theorem t_mem_D : t ∈ Dsub t Q := hS.E_le_D (t_mem_sup (X := Q))

theorem kap_t_right {d : G} (hd : d ∈ Dsub t Q) : kap d t = ψ (tauD t ψ d) := by
  rw [kap, hS.conj_t_D hZ hd, ← hS.commute_ψ (tauD t ψ d), mul_inv_cancel_right]

theorem kap_t_left {d : G} (hd : d ∈ Dsub t Q) : kap t d = ψ (tauD t ψ d) := by
  rw [hS.kap_symm hZ hd hS.t_mem_D, hS.kap_t_right hZ hd]

end SetupX

end CFSG.EvenSmallLie.OmegaEight.SplitIn
