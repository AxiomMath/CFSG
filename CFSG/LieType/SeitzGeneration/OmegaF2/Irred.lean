module

public import Mathlib.Algebra.Field.Defs
public import Mathlib.Algebra.Module.Pi
import Mathlib.Tactic.FinCases
public import Mathlib.Algebra.Module.Submodule.Lattice

public section

namespace CFSG.LieType.SeitzGeneration.OmegaF2

variable {K : Type} [Field K]

theorem eq_top_of_stable (Ω : Submodule K (Fin 3 → K))
    (hΩ : ∀ i j : Fin 3, i ≠ j → ∀ ω ∈ Ω, Function.update ω j (ω j + ω i) ∈ Ω)
    {ω : Fin 3 → K} (hω : ω ∈ Ω) (hne : ω ≠ 0) : Ω = ⊤ := by
  obtain ⟨b, hb⟩ : ∃ b, ω b ≠ 0 := by
    by_contra h
    push Not at h
    exact hne (funext h)
  have key : ∀ j, j ≠ b → (Pi.single j (1 : K) : Fin 3 → K) ∈ Ω := by
    intro j hj
    have h1 := hΩ b j (Ne.symm hj) ω hω
    have h2 := Ω.sub_mem h1 hω
    have h3 : Function.update ω j (ω j + ω b) - ω = ω b • (Pi.single j (1 : K) : Fin 3 → K) := by
      funext i
      by_cases hij : i = j
      · subst hij
        simp
      · simp [Function.update_of_ne hij, Pi.single_apply, hij]
    rw [h3] at h2
    have h4 := Ω.smul_mem (ω b)⁻¹ h2
    rwa [smul_smul, inv_mul_cancel₀ hb, one_smul] at h4
  obtain ⟨j, hj⟩ := exists_ne b
  have hjb : (Pi.single b (1 : K) : Fin 3 → K) ∈ Ω := by
    have h1 := hΩ j b hj (Pi.single j (1 : K)) (key j hj)
    have h2 := Ω.sub_mem h1 (key j hj)
    have hbj : b ≠ j := Ne.symm hj
    have h3 : Function.update (Pi.single j (1 : K) : Fin 3 → K) b
        ((Pi.single j (1 : K) : Fin 3 → K) b + (Pi.single j (1 : K) : Fin 3 → K) j) -
          (Pi.single j (1 : K) : Fin 3 → K) =
          (Pi.single b (1 : K) : Fin 3 → K) := by
      funext i
      by_cases hib : i = b
      · subst hib
        simp [Pi.single_apply, hbj]
      · simp [Function.update_of_ne hib, Pi.single_apply, hib]
    rwa [h3] at h2
  have hbasis : ∀ i : Fin 3, (Pi.single i (1 : K) : Fin 3 → K) ∈ Ω := by
    intro i
    by_cases hi : i = b
    · subst hi
      exact hjb
    · exact key i hi
  rw [Submodule.eq_top_iff']
  intro v
  have hv : v = v 0 • (Pi.single 0 (1 : K) : Fin 3 → K) + v 1 • (Pi.single 1 (1 : K) : Fin 3 → K) +
      v 2 • (Pi.single 2 (1 : K) : Fin 3 → K) := by
    funext i
    fin_cases i <;> simp
  rw [hv]
  exact Ω.add_mem (Ω.add_mem (Ω.smul_mem _ (hbasis 0)) (Ω.smul_mem _ (hbasis 1)))
    (Ω.smul_mem _ (hbasis 2))

end CFSG.LieType.SeitzGeneration.OmegaF2
