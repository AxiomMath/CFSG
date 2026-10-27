module

public import CFSG.LocalAnalysis.OddStandard.SmallF3.U33.Sec4B.SbZ4SK

public section

namespace CFSG.OddStandard.SmallF3.HarrisU33

open Subgroup
open scoped Pointwise

variable {G : Type} [Group G] [Finite G] {t : G} {L S : Subgroup G} {x₁ x₂ lam rho tau : G}

namespace Z4Pre

variable (hp : Z4Pre t L S x₁ x₂ lam rho tau)
include hp

theorem tau_ttau_not_conj : (∀ g : G, g * t * g⁻¹ ≠ tau) ∧ ∀ g : G, g * t * g⁻¹ ≠ t * tau := by
  constructor
  · intro g h
    have hmem : g * t * g⁻¹ ∈ t • (fourGrp x₁ x₂ : Set G) :=
      hp.tG_X g (by rw [h]; exact hp.tau_mem_X)
    rw [h, Set.mem_smul_set] at hmem
    obtain ⟨v, hv, htv⟩ := hmem
    have htv' : t * v = tau := by simpa using htv
    have htinv : t⁻¹ = t := inv_eq_of_mul_eq_one_right hp.t_mul_self
    have hveq : v = t * tau := by
      calc v = t⁻¹ * (t * v) := by group
        _ = t⁻¹ * tau := by rw [htv']
        _ = t * tau := by rw [htinv]
    rw [hveq] at hv
    exact hp.ttau_not_mem_Q (hp.V_le_Q hv)
  · intro g h
    have hmem : g * t * g⁻¹ ∈ t • (fourGrp x₁ x₂ : Set G) :=
      hp.tG_X g (by rw [h]; exact hp.ttau_mem_X)
    rw [h, Set.mem_smul_set] at hmem
    obtain ⟨v, hv, htv⟩ := hmem
    have htv' : t * v = t * tau := by simpa using htv
    have hveq : v = tau := by
      calc v = t⁻¹ * (t * v) := by group
        _ = t⁻¹ * (t * tau) := by rw [htv']
        _ = tau := by group
    rw [hveq] at hv
    exact hp.tau_not_mem_Q (hp.V_le_Q hv)

theorem conj_t_eq {g : G} (hg : g * t * g⁻¹ ∈ closure ({t, tau} : Set G)) : g * t * g⁻¹ = t := by
  rcases (S4B.mem_closure_pair_of_invol hp.t_mul_self hp.tau_mul_self hp.t_comm_tau).mp hg with
    h | h | h | h
  · exfalso
    have ht1 : t = 1 := by
      calc t = g⁻¹ * (g * t * g⁻¹) * g := by group
        _ = 1 := by rw [h]; group
    exact hp.t_ne_one ht1
  · exact h
  · exact absurd h (hp.tau_ttau_not_conj.1 g)
  · exact absurd h (hp.tau_ttau_not_conj.2 g)

end Z4Pre

namespace Z4Good

variable (hg : Z4Good t L S x₁ x₂ lam rho tau)
include hg

theorem conj_cent_Y {n a : G} (hn : n ∈ normalizer ((ctxQ t tau x₁ x₂ rho : Subgroup G) : Set G))
    (ha : ∀ b ∈ ctxYq t tau x₁ x₂ rho, a * b = b * a) :
    ∀ b ∈ ctxYq t tau x₁ x₂ rho, (n * a * n⁻¹) * b = b * (n * a * n⁻¹) := by
  intro b hb
  have hb' : n⁻¹ * b * n ∈ ctxYq t tau x₁ x₂ rho := by
    have h := hg.toZ4Pre.conj_Y (n := n⁻¹) (a := b) (inv_mem hn) hb
    simpa using h
  have hb_eq : b = n * (n⁻¹ * b * n) * n⁻¹ := by group
  rw [hb_eq]
  calc (n * a * n⁻¹) * (n * (n⁻¹ * b * n) * n⁻¹)
      = n * (a * (n⁻¹ * b * n)) * n⁻¹ := by group
    _ = n * ((n⁻¹ * b * n) * a) * n⁻¹ := by rw [ha (n⁻¹ * b * n) hb']
    _ = (n * (n⁻¹ * b * n) * n⁻¹) * (n * a * n⁻¹) := by group

theorem conj_tau_eq {n : G} (hn : n ∈ normalizer ((ctxQ t tau x₁ x₂ rho : Subgroup G) : Set G))
    (h : n * tau * n⁻¹ ∈ closure ({t, tau} : Set G)) : n * tau * n⁻¹ = tau := by
  rcases (S4B.mem_closure_pair_of_invol hg.t_mul_self hg.tau_mul_self hg.t_comm_tau).mp h with
    h1 | h1 | h1 | h1
  · exfalso
    have htau : tau = 1 := by
      calc tau = n⁻¹ * (n * tau * n⁻¹) * n := by group
        _ = 1 := by rw [h1]; group
    exact hg.tau_ne_one htau
  · exfalso
    have hc : n⁻¹ * t * (n⁻¹)⁻¹ = tau := by
      rw [inv_inv]
      calc n⁻¹ * t * n = n⁻¹ * (n * tau * n⁻¹) * n := by rw [← h1]
        _ = tau := by group
    exact hg.toZ4Pre.tau_ttau_not_conj.1 n⁻¹ hc
  · exact h1
  · exfalso
    apply hg.toZ4Pre.not_cent_t_Y
    have hcent0 : ∀ b ∈ ctxYq t tau x₁ x₂ rho,
        (n * tau * n⁻¹) * b = b * (n * tau * n⁻¹) := hg.conj_cent_Y hn hg.tau_cent
    have hcent : ∀ b ∈ ctxYq t tau x₁ x₂ rho,
        (t * tau) * b = b * (t * tau) := fun b hb => by
      rw [← h1]; exact hcent0 b hb
    intro b hb
    have h1b := hcent b hb
    have h2b := hg.tau_cent b hb
    have ht_eq : t = (t * tau) * tau := by rw [mul_assoc, hg.tau_mul_self, mul_one]
    calc t * b = ((t * tau) * tau) * b := by rw [← ht_eq]
      _ = (t * tau) * (tau * b) := by group
      _ = (t * tau) * (b * tau) := by rw [h2b]
      _ = ((t * tau) * b) * tau := by group
      _ = (b * (t * tau)) * tau := by rw [h1b]
      _ = b * ((t * tau) * tau) := by group
      _ = b * t := by rw [← ht_eq]

end Z4Good

end CFSG.OddStandard.SmallF3.HarrisU33
