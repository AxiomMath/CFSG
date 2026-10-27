module

public import CFSG.LocalAnalysis.OddStandard.SmallF3.U33.Sec4B.SbZ4SB
public import CFSG.LocalAnalysis.OddStandard.SmallF3.U33.Sec4B.SbC17
public import CFSG.Goldschmidt.Steps.Sec89a
public import CFSG.LocalAnalysis.OddStandard.SmallF3.U33.Sec4B.SbZ4SD

public section

namespace CFSG.OddStandard.SmallF3.HarrisU33

open Subgroup

variable {G : Type} [Group G] [Finite G] {t : G} {L S : Subgroup G} {x₁ x₂ lam rho tau : G}

namespace Z4Good

variable (hg : Z4Good t L S x₁ x₂ lam rho tau)
include hg

private theorem mem_zpowers_tau {c : G} (hc : c ∈ zpowers tau) : c = 1 ∨ c = tau := by
  obtain ⟨n, rfl⟩ := Subgroup.mem_zpowers_iff.mp hc
  have h2 : tau ^ (2 : ℕ) = 1 := by rw [pow_two, hg.tau_mul_self]
  have hmod : tau ^ n = tau ^ (n % 2) := zpow_eq_zpow_emod' n h2
  rcases Int.emod_two_eq_zero_or_one n with h | h
  · left; rw [hmod, h]; simp
  · right; rw [hmod, h]; simp

private theorem Y_isElemAbelian : CFSG.Open.IsElemAbelian 2 (ctxYq t tau x₁ x₂ rho) :=
  ⟨IsMulCommutative.of_comm (fun a b => Subtype.ext (hg.Y_comm a a.2 b b.2)),
    fun x hx => hg.Y_sq hx⟩

theorem tG_Qtau (htau : ∀ a ∈ ctxQ t tau x₁ x₂ rho, tau * a * tau⁻¹ = a⁻¹) :
    ∀ g : G, ∀ u ∈ ctxQ t tau x₁ x₂ rho ⊔ zpowers tau, g * t * g⁻¹ ≠ u := by
  intro g u hu heq
  have hu2 : u * u = 1 := by
    rw [← heq]
    calc (g * t * g⁻¹) * (g * t * g⁻¹) = g * (t * t) * g⁻¹ := by group
      _ = 1 := by rw [hg.t_mul_self]; group
  have hu_ne : u ≠ 1 := by
    intro h1
    have ht : t = 1 := by
      calc t = g⁻¹ * (g * t * g⁻¹) * g := by group
        _ = 1 := by rw [heq, h1]; group
    exact hg.t_ne_one ht
  have hzM : zpowers tau ≤ ctxM t tau x₁ x₂ := Subgroup.zpowers_le.mpr hg.tau_mem_M
  obtain ⟨q, hq, c, hc, hqc⟩ := mem_sup_of_normalizes
    (A := ctxQ t tau x₁ x₂ rho) (C := zpowers tau)
    (fun c hc a ha => hg.normal_Q.2 c (hzM hc) a ha) hu
  rcases mem_zpowers_tau hg hc with hc1 | hctau
  · have huq : u = q := by rw [hqc, hc1, mul_one]
    have hq2 : q ^ 2 = 1 := by rw [pow_two, ← huq]; exact hu2
    have hqY : q ∈ ctxYq t tau x₁ x₂ rho := (hg.mem_Y_iff q).mpr ⟨hq, hq2⟩
    have htau_notY : tau ∉ ctxYq t tau x₁ x₂ rho :=
      fun h => hg.tau_not_mem_Q (hg.Y_le_Q h)
    have htau2 : tau ^ 2 = 1 := by rw [pow_two]; exact hg.tau_mul_self
    have hcommYtau : ∀ a ∈ ctxYq t tau x₁ x₂ rho, a * tau = tau * a :=
      fun a ha => (hg.tau_cent a ha).symm
    obtain ⟨hAe, hAcard⟩ := CFSG.Goldschmidt.Sec89.isElemAbelian_sup_zpowers
      (A := ctxYq t tau x₁ x₂ rho) (Y_isElemAbelian hg) htau_notY htau2 hcommYtau
    have hYcent : ctxYq t tau x₁ x₂ rho ≤ centralizer ({u} : Set G) := by
      intro y hy
      rw [Subgroup.mem_centralizer_singleton_iff, huq]
      exact hg.Y_comm y hy q hqY
    have hzp : zpowers tau ≤ centralizer ({u} : Set G) :=
      Subgroup.zpowers_le.mpr
        (Subgroup.mem_centralizer_singleton_iff.mpr (by rw [huq]; exact hg.tau_cent q hqY))
    have hAc : ctxYq t tau x₁ x₂ rho ⊔ zpowers tau ≤ centralizer ({u} : Set G) :=
      sup_le hYcent hzp
    have hle := S4B.c17_card_elemAbelian_conj_le (hc := hg.toCtx10) (g := g)
      (A := ctxYq t tau x₁ x₂ rho ⊔ zpowers tau) (by rw [heq]; exact hAc) hAe
    have h32 : (32 : ℕ) ≤ Nat.card ↥(ctxYq t tau x₁ x₂ rho ⊔ zpowers tau) := by
      have h := hAcard
      rw [hg.card_Y] at h
      norm_num at h
      exact h
    omega
  · have huq : u = q * tau := by rw [hqc, hctau]
    have hu_notY : u ∉ ctxYq t tau x₁ x₂ rho := by
      intro hY
      have huQ : u ∈ ctxQ t tau x₁ x₂ rho := hg.Y_le_Q hY
      have htauQ : tau ∈ ctxQ t tau x₁ x₂ rho := by
        have h1 : tau = q⁻¹ * u := by rw [huq]; group
        have hmem : q⁻¹ * u ∈ ctxQ t tau x₁ x₂ rho := mul_mem (inv_mem hq) huQ
        rwa [← h1] at hmem
      exact hg.tau_not_mem_Q htauQ
    have hcommYu : ∀ a ∈ ctxYq t tau x₁ x₂ rho, a * u = u * a := by
      intro a ha
      rw [huq]
      calc a * (q * tau) = (a * q) * tau := by group
        _ = (q * a) * tau := by rw [hg.Q_comm a (hg.Y_le_Q ha) q hq]
        _ = q * (a * tau) := by group
        _ = q * (tau * a) := by rw [hg.tau_cent a ha]
        _ = (q * tau) * a := by group
    have hu2' : u ^ 2 = 1 := by rw [pow_two]; exact hu2
    obtain ⟨hAe, hAcard⟩ := CFSG.Goldschmidt.Sec89.isElemAbelian_sup_zpowers
      (A := ctxYq t tau x₁ x₂ rho) (Y_isElemAbelian hg) hu_notY hu2' hcommYu
    have hYcent : ctxYq t tau x₁ x₂ rho ≤ centralizer ({u} : Set G) :=
      fun y hy => Subgroup.mem_centralizer_singleton_iff.mpr (hcommYu y hy)
    have hzp : zpowers u ≤ centralizer ({u} : Set G) :=
      Subgroup.zpowers_le.mpr
        (Subgroup.mem_centralizer_singleton_iff.mpr rfl)
    have hAc : ctxYq t tau x₁ x₂ rho ⊔ zpowers u ≤ centralizer ({u} : Set G) :=
      sup_le hYcent hzp
    have hle := S4B.c17_card_elemAbelian_conj_le (hc := hg.toCtx10) (g := g)
      (A := ctxYq t tau x₁ x₂ rho ⊔ zpowers u) (by rw [heq]; exact hAc) hAe
    have h32 : (32 : ℕ) ≤ Nat.card ↥(ctxYq t tau x₁ x₂ rho ⊔ zpowers u) := by
      have h := hAcard
      rw [hg.card_Y] at h
      norm_num at h
      exact h
    omega

end Z4Good

end CFSG.OddStandard.SmallF3.HarrisU33
