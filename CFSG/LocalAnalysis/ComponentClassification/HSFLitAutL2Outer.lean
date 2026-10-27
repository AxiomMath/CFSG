module

public import CFSG.LocalAnalysis.ComponentClassification.HSFLitAutL2Fact

public section

namespace CFSG.ComponentClassification.HSFLit.AutL2

open CFSG Subgroup Equiv CFSG.GH74.KGroups
open CFSG.ComponentClassification.GrSLit CFSG.ComponentClassification.GrSLit.L34Facts
open CFSG.ComponentClassification.UnbalancedLayer CFSG.ComponentClassification.HSFLit.AutBeta

variable {G : Type} [Group G] {J : Subgroup G} {n : ℕ} (M : AutModel (Jhat J) (Perm (Fin n)))

theorem rhoM_mem_P (hPA : M.P ≤ M.A) {j : G} (hj : j ∈ J) : rhoM M (le_normalizer hj) ∈ M.P := by
  set e₀ : Perm (Fin n) := (M.e (jq J ⟨j, hj⟩) : Perm (Fin n)) with he₀
  set a : Perm (Fin n) := e₀ * rhoM M (le_normalizer hj) with ha
  have haA : a ∈ M.A := M.A.mul_mem (hPA (M.e (jq J ⟨j, hj⟩)).2) (rhoM_mem M _)
  have hfix : ∀ y : Jhat J, a * (M.e y : Perm (Fin n)) * a⁻¹ = M.e y := by
    intro y
    have h1 := rhoM_spec M (le_normalizer hj) y
    rw [betaHat_mem_K J hj y, map_mul, map_mul, map_inv] at h1
    simp only [Subgroup.coe_mul, Subgroup.coe_inv] at h1
    rw [ha, ← he₀] at *
    calc e₀ * rhoM M (le_normalizer hj) * (M.e y : Perm (Fin n)) *
        (e₀ * rhoM M (le_normalizer hj))⁻¹ =
        e₀ * (rhoM M (le_normalizer hj) * (M.e y : Perm (Fin n)) *
          (rhoM M (le_normalizer hj))⁻¹) * e₀⁻¹ := by group
      _ = e₀ * (e₀⁻¹ * (M.e y : Perm (Fin n)) * e₀) * e₀⁻¹ := by rw [← h1]
      _ = M.e y := by group
  obtain ⟨ψ, hψ⟩ := M.Φ.surjective ⟨a, haA⟩
  have hψ1 : ψ = 1 := by
    ext y
    apply M.e.injective
    apply Subtype.ext
    have h2 := M.spec ψ y
    rw [hψ] at h2
    rw [h2]
    exact hfix y
  have ha1 : a = 1 := by
    have := congrArg Subtype.val hψ
    rw [hψ1, map_one] at this
    exact this.symm
  have : rhoM M (le_normalizer hj) = e₀⁻¹ := by
    rw [ha] at ha1
    exact eq_inv_of_mul_eq_one_right ha1
  rw [this]
  exact M.P.inv_mem (M.e (jq J ⟨j, hj⟩)).2

variable [Finite G]

theorem l2UnbalancingOuter :
    ∀ (G : Type) [Group G] [Finite G] (a x : G) (J : Subgroup G), GSUnbalancingTriple a x J →
      (IsL2Type 5 (J ⧸ pPrimeCore 2 J) ∨ IsL2Type 7 (J ⧸ pPrimeCore 2 J)) →
      ∀ j ∈ J, j⁻¹ * x ∉ coreActionKernel J := by
  intro G _ _ a x J htri hL j hj hjx
  obtain ⟨-, hxo, -, -, -, hxJ, hDJ⟩ := htri
  have hx2 : x * x = 1 := by rw [← pow_two, ← hxo, pow_orderOf_eq_one]
  have hset : {y | ∃ i ∈ J, ∃ d ∈ ({x} : Set G), y = i⁻¹ * d⁻¹ * i * d} =
      {y | ∃ i ∈ J, y = i⁻¹ * x⁻¹ * i * x} := by
    ext y
    simp
  have hxJ' : closure {y | ∃ i ∈ J, ∃ d ∈ ({x} : Set G), y = i⁻¹ * d⁻¹ * i * d} = J := by
    rw [hset]
    exact hxJ
  have hxN : x ∈ normalizer (J : Set G) := mem_normalizer_of_closure hxJ' (Set.mem_singleton x)
  obtain ⟨n, M, hF, -⟩ := exists_l2Model' hL
  obtain ⟨-, -, hρP⟩ := rhoM_outer M hF hxN hx2 hxJ' hDJ fun d hd => (mem_inf.mp hd).1
  have hjN : j⁻¹ ∈ normalizer (J : Set G) := le_normalizer (J.inv_mem hj)
  have h1 : rhoM M (mul_mem hjN hxN) = 1 := by
    have := (rhoHom_eq_one_iff M ⟨j⁻¹ * x, mul_mem hjN hxN⟩).2 hjx
    rwa [rhoHom_apply, inv_eq_one] at this
  rw [rhoM_mul M hjN hxN] at h1
  have h2 : rhoM M hxN = (rhoM M hjN)⁻¹ := eq_inv_of_mul_eq_one_left h1
  exact hρP (h2 ▸ M.P.inv_mem (rhoM_mem_P M hF.le (J.inv_mem hj)))

end CFSG.ComponentClassification.HSFLit.AutL2
