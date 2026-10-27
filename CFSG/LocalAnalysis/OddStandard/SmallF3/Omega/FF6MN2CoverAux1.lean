module

public import CFSG.LocalAnalysis.OddStandard.SmallF3.Omega.FF6MHerm3

public section

attribute [-instance] instAddCommGroupOfIsSimpleAddGroupOfIsNilpotent
  instCommGroupOfIsSimpleGroupOfIsNilpotent

namespace CFSG.OddStandard.SmallF3.Omega

open QuadraticMap

variable {V : Type} [AddCommGroup V] [Module (ZMod 3) V] [FiniteDimensional (ZMod 3) V]
  {Q : QuadraticForm (ZMod 3) V}

private theorem hermForm_single_one {n : ℕ} (j : Fin n) :
    hermForm n (Pi.single j (1 : F9)) = 1 := by
  rw [hermForm_apply, Finset.sum_eq_single j]
  · simp [QuadraticAlgebra.re_one, QuadraticAlgebra.im_one]
  · intro i _ hi; simp [Pi.single_eq_of_ne hi]
  · intro h; exact absurd (Finset.mem_univ j) h

private theorem polar_hermForm_single_left {n : ℕ} (i : Fin n) (a : F9) (y : Fin n → F9) :
    polar (hermForm n) (Pi.single i a) y = -(a.re * (y i).re + a.im * (y i).im) := by
  rw [polar_hermForm, herm9_re, Finset.sum_eq_single i]
  · simp
  · intro k _ hk; simp [Pi.single_eq_of_ne hk]
  · intro h; exact absurd (Finset.mem_univ i) h

private theorem polar_hermForm_single_single {n : ℕ} {i j : Fin n} (a b : F9) (hij : i ≠ j) :
    polar (hermForm n) (Pi.single i a) (Pi.single j b) = 0 := by
  rw [polar_hermForm_single_left]; simp [Pi.single_eq_of_ne hij]

private theorem polar_hermForm_single_omega {n : ℕ} (i : Fin n) :
    polar (hermForm n) (Pi.single i (1 : F9)) (Pi.single i omega9) = 0 := by
  rw [polar_hermForm_single_left]; simp [omega9, QuadraticAlgebra.re_one, QuadraticAlgebra.im_one]

private theorem omega9_smul_single {n : ℕ} (j : Fin n) :
    omega9 • Pi.single j (1 : F9) = Pi.single j omega9 := by
  funext k
  by_cases h : k = j
  · subst h; simp
  · simp [Pi.single_eq_of_ne h]

theorem ff6m_N2_pair_facts (hQ : Q.Nondegenerate) (hdim : Module.finrank (ZMod 3) V = 6)
    (hsgn : quadSign Q = -1) {p : OGroup Q} (hp : p * p = piOrth Q) :
    ∃ u₁ u₂ : V, Q u₁ = 1 ∧ Q u₂ = 1 ∧ polar Q u₁ u₂ = 0 ∧
      polar Q u₁ ((p : V ≃ₗ[ZMod 3] V) u₁) = 0 ∧ polar Q u₂ ((p : V ≃ₗ[ZMod 3] V) u₂) = 0 ∧
      polar Q u₁ ((p : V ≃ₗ[ZMod 3] V) u₂) = 0 ∧ polar Q u₂ ((p : V ≃ₗ[ZMod 3] V) u₁) = 0 := by
  obtain ⟨e, he⟩ := ff6m_exists_iso3 hQ hdim hsgn hp
  refine ⟨e (Pi.single (0 : Fin 3) 1), e (Pi.single (1 : Fin 3) 1), ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · rw [e.map_app]; exact hermForm_single_one 0
  · rw [e.map_app]; exact hermForm_single_one 1
  · rw [e.polar_apply]
    exact polar_hermForm_single_single (1 : F9) (1 : F9) (by decide)
  · rw [← he (Pi.single (0 : Fin 3) 1), e.polar_apply, omega9_smul_single]
    exact polar_hermForm_single_omega 0
  · rw [← he (Pi.single (1 : Fin 3) 1), e.polar_apply, omega9_smul_single]
    exact polar_hermForm_single_omega 1
  · rw [← he (Pi.single (1 : Fin 3) 1), e.polar_apply, omega9_smul_single]
    exact polar_hermForm_single_single (1 : F9) omega9 (by decide)
  · rw [← he (Pi.single (0 : Fin 3) 1), e.polar_apply, omega9_smul_single]
    exact polar_hermForm_single_single (1 : F9) omega9 (by decide)

end CFSG.OddStandard.SmallF3.Omega
