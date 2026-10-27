module

public import CFSG.LocalAnalysis.OddStandard.SmallF3.U33.Sec4B.SbZ4SB
public import CFSG.LocalAnalysis.OddStandard.SmallF3.U33.Sec4B.SbZ4SD

public section

namespace CFSG.OddStandard.SmallF3.HarrisU33

open Subgroup

variable {G : Type} [Group G] [Finite G] {t : G} {L S : Subgroup G} {x₁ x₂ lam rho tau : G}

namespace Z4Pre

variable (hp : Z4Pre t L S x₁ x₂ lam rho tau)
include hp

theorem Q_le_U : ctxQ t tau x₁ x₂ rho ≤ ctxU t tau x₁ x₂ lam :=
  (hp.Q_le_O).trans le_sup_left

theorem t_mem_U : t ∈ ctxU t tau x₁ x₂ lam := mem_sup_left hp.t_mem_O

theorem lam_mem_U : lam ∈ ctxU t tau x₁ x₂ lam := mem_sup_right (mem_zpowers lam)

theorem sigma_mem_U : lam * t ∈ ctxU t tau x₁ x₂ lam := mul_mem hp.lam_mem_U hp.t_mem_U

end Z4Pre

namespace Z4Good

variable (hg : Z4Good t L S x₁ x₂ lam rho tau)
include hg

theorem E_comm : ∀ a ∈ closure ({t, tau, lam} : Set G), ∀ b ∈ closure ({t, tau, lam} : Set G),
    a * b = b * a := by
  have hk : ∀ x ∈ ({t, tau, lam} : Set G), ∀ y ∈ ({t, tau, lam} : Set G), x * y = y * x := by
    intro x hx y hy
    simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hx hy
    rcases hx with h | h | h <;> rcases hy with h' | h' | h' <;> rw [h, h']
    all_goals first
      | rfl
      | exact hg.t_comm_tau
      | exact hg.t_comm_tau.symm
      | exact hg.t_lam_comm
      | exact hg.t_lam_comm.symm
      | exact hg.tau_lam
      | exact hg.tau_lam.symm
  haveI : IsMulCommutative (closure ({t, tau, lam} : Set G)) :=
    Subgroup.isMulCommutative_closure (fun x hx y hy _ => hk x hx y hy)
  intro a ha b hb
  exact congrArg Subtype.val (mul_comm' (⟨a, ha⟩ : closure ({t, tau, lam} : Set G))
    ⟨b, hb⟩)

theorem E_le_M : closure ({t, tau, lam} : Set G) ≤ ctxM t tau x₁ x₂ := by
  rw [Subgroup.closure_le]
  rintro g (rfl | rfl | rfl)
  · exact hg.t_mem_M
  · exact hg.tau_mem_M
  · exact hg.lam_mem_M

theorem E_normalizes_Q : ∀ c ∈ closure ({t, tau, lam} : Set G), ∀ a ∈ ctxQ t tau x₁ x₂ rho,
    c * a * c⁻¹ ∈ ctxQ t tau x₁ x₂ rho :=
  fun c hc a ha => hg.normal_Q.2 c (hg.E_le_M hc) a ha

theorem mem_U_decomp {s : G} (hs : s ∈ ctxU t tau x₁ x₂ lam) :
    ∃ q ∈ ctxQ t tau x₁ x₂ rho, ∃ c ∈ closure ({t, tau, lam} : Set G), s = q * c := by
  have hle : ctxU t tau x₁ x₂ lam ≤ ctxQ t tau x₁ x₂ rho ⊔ closure ({t, tau, lam} : Set G) := by
    unfold ctxU
    refine sup_le ?_ ?_
    · rw [hg.O_eq_Q]
      refine sup_le le_sup_left ?_
      exact (Subgroup.closure_mono (by
        intro g hg'
        simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hg' ⊢
        tauto)).trans le_sup_right
    · exact Subgroup.zpowers_le.mpr (Subgroup.mem_sup_right (Subgroup.subset_closure (by simp)))
  exact mem_sup_of_normalizes hg.E_normalizes_Q (hle hs)

theorem comm_mem_Q {a b : G} (ha : a ∈ ctxU t tau x₁ x₂ lam) (hb : b ∈ ctxU t tau x₁ x₂ lam) :
    z4Comm a b ∈ ctxQ t tau x₁ x₂ rho := by
  obtain ⟨q₁, hq₁, c₁, hc₁, rfl⟩ := hg.mem_U_decomp ha
  obtain ⟨q₂, hq₂, c₂, hc₂, rfl⟩ := hg.mem_U_decomp hb
  have hc : c₁ * c₂ = c₂ * c₁ := hg.E_comm c₁ hc₁ c₂ hc₂
  have e1 : (q₁ * c₁)⁻¹ = c₁⁻¹ * q₁⁻¹ := by group
  have e2 : (q₂ * c₂)⁻¹ = c₂⁻¹ * q₂⁻¹ := by group
  have h1 : c₂ * c₁⁻¹ = c₁⁻¹ * c₂ := by
    calc c₂ * c₁⁻¹ = c₁⁻¹ * (c₁ * c₂) * c₁⁻¹ := by group
      _ = c₁⁻¹ * (c₂ * c₁) * c₁⁻¹ := by rw [hc]
      _ = c₁⁻¹ * c₂ := by group
  have key : z4Comm (q₁ * c₁) (q₂ * c₂) =
      q₁ * (c₁ * q₂ * c₁⁻¹) * (c₂ * q₁⁻¹ * c₂⁻¹) * q₂⁻¹ := by
    unfold z4Comm
    rw [e1, e2]
    rw [show (q₁ * c₁) * (q₂ * c₂) * (c₁⁻¹ * q₁⁻¹) * (c₂⁻¹ * q₂⁻¹)
        = q₁ * c₁ * q₂ * (c₂ * c₁⁻¹) * q₁⁻¹ * c₂⁻¹ * q₂⁻¹ by group]
    rw [h1]
    group
  rw [key]
  exact mul_mem (mul_mem (mul_mem hq₁ (hg.E_normalizes_Q c₁ hc₁ q₂ hq₂))
    (hg.E_normalizes_Q c₂ hc₂ q₁⁻¹ (inv_mem hq₁))) (inv_mem hq₂)

end Z4Good

end CFSG.OddStandard.SmallF3.HarrisU33
