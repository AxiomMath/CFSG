module

public import CFSG.LocalAnalysis.OddStandard.SmallF3.U33.Sec4B.SbW4d4
public import CFSG.LocalAnalysis.OddStandard.SmallF3.U33.Sec4B.SbW4c

public section

namespace CFSG.OddStandard.SmallF3.HarrisU33.S4B

open Subgroup
open scoped Pointwise

variable {G : Type} [Group G] [Finite G] {t : G} {L S : Subgroup G} {x₁ x₂ lam rho tau : G}

theorem w4_comm_commutator {r a b : G} (ha : r * a = a * r) (hb : r * b = b * r) :
    r * (a * b * a⁻¹ * b⁻¹) = (a * b * a⁻¹ * b⁻¹) * r := by
  have ha' : Commute r a := ha
  have hb' : Commute r b := hb
  exact ((ha'.mul_right hb').mul_right ha'.inv_right).mul_right hb'.inv_right

theorem w4_cent_X_rho_le (hc : Ctx4 t L S x₁ x₂ lam rho tau) {g : G}
    (hgX : g ∈ ctxX t tau x₁ x₂) (hgρ : rho * g = g * rho) : g ∈ closure ({t, tau} : Set G) := by
  have hc0 : Ctx0 t L S x₁ x₂ lam rho := hc.toCtx0
  have hρt : Commute rho t := w4_rho_t hc
  have hρτ : Commute rho tau := w4_rho_tau hc
  have hρg : Commute rho g := hgρ
  have htC : t ∈ closure ({t, tau} : Set G) := Subgroup.subset_closure (by simp)
  have htauC : tau ∈ closure ({t, tau} : Set G) := Subgroup.subset_closure (by simp)
  rcases l12_X_cases hc hgX with hN | hN
  · rcases l12_N_cases hc hN with hV | hV
    · rw [w4_fpf hc0 hV hgρ]
      exact one_mem _
    · have h1 : tau * g = 1 := w4_fpf hc0 hV (hρτ.mul_right hρg)
      rw [eq_inv_of_mul_eq_one_right h1]
      exact inv_mem htauC
  · rcases l12_N_cases hc hN with hV | hV
    · have h1 : t * g = 1 := w4_fpf hc0 hV (hρt.mul_right hρg)
      rw [eq_inv_of_mul_eq_one_right h1]
      exact inv_mem htC
    · have h1 : tau * (t * g) = 1 := w4_fpf hc0 hV (hρτ.mul_right (hρt.mul_right hρg))
      have h2 : tau * t * g = 1 := by rw [mul_assoc]; exact h1
      rw [eq_inv_of_mul_eq_one_right h2]
      exact inv_mem (mul_mem htauC htC)

theorem w4_CO_rho
    (hc : W4Ctxb t L S x₁ x₂ lam rho tau) :
    ctxCO t tau x₁ x₂ rho = closure ({t, tau} : Set G) := by
  have hc4 : Ctx4 t L S x₁ x₂ lam rho tau := hc.toCtx10.toCtx4
  have hc0 : Ctx0 t L S x₁ x₂ lam rho := hc4.toCtx0
  have hρt := w4_rho_t hc4
  have hρτ := w4_rho_tau hc4
  have htX : t ∈ ctxX t tau x₁ x₂ := Subgroup.subset_closure (by simp)
  have htauX : tau ∈ ctxX t tau x₁ x₂ := Subgroup.subset_closure (by simp)
  obtain ⟨htO, htauO, -, -⟩ := w4_gens_mem_O hc
  apply le_antisymm
  · intro g hg
    have hg' : g ∈ ctxO t tau x₁ x₂ ⊓ centralizer ({rho} : Set G) := hg
    obtain ⟨hgO, hgC⟩ := Subgroup.mem_inf.mp hg'
    have hgρ : g * rho = rho * g := Subgroup.mem_centralizer_singleton_iff.mp hgC
    have hgR : g ∈ ctxR t tau x₁ x₂ := w4_O_le_R hc hgO
    have h1 : g * t * g⁻¹ * t⁻¹ = 1 :=
      w4_fpf hc0 (hgR.2.1 t htX) (w4_comm_commutator hgρ.symm hρt)
    have h2 : g * tau * g⁻¹ * tau⁻¹ = 1 :=
      w4_fpf hc0 (hgR.2.1 tau htauX) (w4_comm_commutator hgρ.symm hρτ)
    exact w4_cent_X_rho_le hc4 (w4_mem_X_of_mem_R hc4 hgR h1 h2) hgρ.symm
  · rw [Subgroup.closure_le]
    intro u hu
    show u ∈ ctxO t tau x₁ x₂ ⊓ centralizer ({rho} : Set G)
    simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hu
    rcases hu with rfl | rfl
    · exact ⟨htO, Subgroup.mem_centralizer_singleton_iff.mpr hρt.symm⟩
    · exact ⟨htauO, Subgroup.mem_centralizer_singleton_iff.mpr hρτ.symm⟩

end CFSG.OddStandard.SmallF3.HarrisU33.S4B
