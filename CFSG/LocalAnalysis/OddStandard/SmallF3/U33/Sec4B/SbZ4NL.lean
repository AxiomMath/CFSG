module

public import CFSG.LocalAnalysis.OddStandard.SmallF3.U33.Sec4B.SbZ4NJ
public import CFSG.LocalAnalysis.OddStandard.SmallF3.U33.Sec4B.SbC17
public import CFSG.LocalAnalysis.OddStandard.SmallF3.U33.Sec4B.SbL414c

public section

namespace CFSG.OddStandard.SmallF3.HarrisU33

open Subgroup

variable {G : Type} [Group G] [Finite G] {t : G} {L S : Subgroup G} {x₁ x₂ lam rho tau : G}

private lemma isElemAbelian_zpowers_of_mul_self {a : G} (ha : a * a = 1) :
    CFSG.Open.IsElemAbelian 2 (zpowers a) := by
  have ha2 : a ^ 2 = 1 := by rwa [pow_two]
  have haz : a ^ (2 : ℤ) = 1 := by
    rw [show (2 : ℤ) = ((2 : ℕ) : ℤ) by norm_num, zpow_natCast]
    exact ha2
  refine ⟨IsMulCommutative.of_comm ?_, ?_⟩
  · intro x y
    apply Subtype.ext
    obtain ⟨m, hm⟩ := Subgroup.mem_zpowers_iff.mp x.2
    obtain ⟨n, hn⟩ := Subgroup.mem_zpowers_iff.mp y.2
    show (x : G) * (y : G) = (y : G) * (x : G)
    rw [← hm, ← hn, ← zpow_add, ← zpow_add, add_comm]
  · intro x hx
    obtain ⟨m, hm⟩ := Subgroup.mem_zpowers_iff.mp hx
    show (x : G) ^ 2 = 1
    rw [← hm, pow_two, ← zpow_add, show m + m = 2 * m by ring, zpow_mul a 2 m, haz, one_zpow]

namespace Ctx4Z

variable (hz : Ctx4Z t L S x₁ x₂ lam rho tau)
include hz

theorem lam_conj_z : ∃ c ∈ L, c * (x₁ * x₂) ^ 2 * c⁻¹ = lam := by
  have hlam_ne : lam ≠ 1 := by
    intro h
    have h2 : orderOf lam = orderOf (1 : G) := by rw [h]
    rw [hz.wreath.ord_lam, orderOf_one] at h2
    exact absurd h2 (by norm_num)
  exact hz.invol_L lam hz.lam_mem_L hz.lam_mul_self hlam_ne

section


theorem tau_lam_conj_tau : ∃ c ∈ L, c * tau * c⁻¹ = tau * lam := by
  have h2 : (tau * lam) * (tau * lam) = 1 := by
    have h : (tau * lam) * (tau * lam) = (tau * tau) * (lam * lam) := by
      calc (tau * lam) * (tau * lam) = tau * (lam * tau) * lam := by group
        _ = tau * (tau * lam) * lam := by rw [← hz.tau_lam]
        _ = (tau * tau) * (lam * lam) := by group
    rw [h, hz.tau_mul_self, hz.lam_mul_self, one_mul]
  exact (Ctx4.involutions_tau_coset hz.toCtx4).1 lam hz.lam_mem_L h2

theorem not_conj_t_lam : ∀ g : G, g * t * g⁻¹ ≠ lam := by
  intro g hg
  obtain ⟨c, _, hcz⟩ := hz.lam_conj_z
  refine Ctx4.not_conj_z hz.toCtx4 ⟨c⁻¹ * g, ?_⟩
  calc (c⁻¹ * g) * t * (c⁻¹ * g)⁻¹ = c⁻¹ * (g * t * g⁻¹) * c := by group
    _ = c⁻¹ * lam * c := by rw [hg]
    _ = (x₁ * x₂) ^ 2 := by rw [← hcz]; group

theorem not_conj_t_lamtau : ∀ g : G, g * t * g⁻¹ ≠ lam * tau := by
  intro g hg
  obtain ⟨c, _, hct⟩ := hz.tau_lam_conj_tau
  refine hz.tG_Qtau (c⁻¹ * g) tau (Subgroup.mem_sup_right (Subgroup.mem_zpowers tau)) ?_
  calc (c⁻¹ * g) * t * (c⁻¹ * g)⁻¹ = c⁻¹ * (g * t * g⁻¹) * c := by group
    _ = c⁻¹ * (lam * tau) * c := by rw [hg]
    _ = tau := by rw [← hz.tau_lam, ← hct]; group

theorem tG_not_mem_E0 (g : G) : g * t * g⁻¹ ∉ ctxE0N t tau x₁ x₂ rho := by
  intro hmem
  set u : G := g * t * g⁻¹ with hu
  have hu2 : u * u = 1 := by
    rw [hu]
    calc (g * t * g⁻¹) * (g * t * g⁻¹) = g * (t * t) * g⁻¹ := by group
      _ = 1 := by rw [hz.t_mul_self]; group
  have huNotY : u ∉ ctxYq t tau x₁ x₂ rho := by
    intro huY
    exact hz.tG_Qtau g u (Subgroup.mem_sup_left (hz.Y_le_Q huY)) hu.symm
  have hcomm : ∀ y ∈ ctxYq t tau x₁ x₂ rho, y * u = u * y :=
    fun y hy => (hz.E0_le_cent_Y u hmem y hy).symm
  have hcomm' : ∀ y ∈ ctxYq t tau x₁ x₂ rho, ∀ z ∈ zpowers u, y * z = z * y := by
    intro y hy z hz
    obtain ⟨k, rfl⟩ := Subgroup.mem_zpowers_iff.mp hz
    exact (show Commute y u from hcomm y hy).zpow_right k
  let B : Subgroup G := ctxYq t tau x₁ x₂ rho ⊔ zpowers u
  have hBe : CFSG.Open.IsElemAbelian 2 B :=
    S4B.isElemAbelian_sup hz.Y_isElemAbelian (isElemAbelian_zpowers_of_mul_self hu2) hcomm'
  have hBcard : Nat.card B = 32 := by
    have h := S4B.card_sup_zpowers_of_commute (T := ctxYq t tau x₁ x₂ rho) (lam := u)
      (by rw [pow_two]; exact hu2) huNotY hcomm
    change Nat.card ↥(ctxYq t tau x₁ x₂ rho ⊔ zpowers u) = 32
    rw [h, hz.card_Y]
  have hBcent : B ≤ centralizer ({u} : Set G) := by
    change ctxYq t tau x₁ x₂ rho ⊔ zpowers u ≤ centralizer ({u} : Set G)
    refine sup_le (fun y hy => ?_) ?_
    · exact Subgroup.mem_centralizer_singleton_iff.mpr (hz.E0_le_cent_Y u hmem y hy).symm
    · exact Subgroup.zpowers_le.mpr (Subgroup.mem_centralizer_singleton_iff.mpr rfl)
  have hbound : Nat.card B ≤ 16 :=
    S4B.c17_card_elemAbelian_conj_le hz.toCtx10 g (by rw [← hu]; exact hBcent) hBe
  rw [hBcard] at hbound
  omega

end

end Ctx4Z

end CFSG.OddStandard.SmallF3.HarrisU33
