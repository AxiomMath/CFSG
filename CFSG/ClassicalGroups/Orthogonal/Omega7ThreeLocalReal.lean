module

public import CFSG.ClassicalGroups.Orthogonal.Omega7ThreeLocalFrame
import CFSG.ClassicalGroups.Orthogonal.Omega7ThreeLocalRealGen
import CFSG.ClassicalGroups.Orthogonal.Omega7ThreeLocalRealSwap

public section

namespace CFSG.ClassicalGroups.Orthogonal.Omega7ThreeLocal

variable {K : Type} [Field K]

theorem realized_perm [Finite K] (F : Frame K) (σ : Equiv.Perm (Fin 3)) :
    Realized F σ (fun _ => 1) := by
  have hc := realized_cycle F
  have hs := realized_swap F
  have hmul : ∀ {σ₁ σ₂ : Equiv.Perm (Fin 3)}, Realized F σ₁ (fun _ => 1) →
      Realized F σ₂ (fun _ => 1) → Realized F (σ₂ * σ₁) (fun _ => 1) := by
    intro σ₁ σ₂ h₁ h₂
    simpa using h₁.mul h₂
  have key : ∀ τ : Equiv.Perm (Fin 3), τ = 1 ∨ τ = finRotate 3 ∨ τ = finRotate 3 * finRotate 3 ∨
      τ = Equiv.swap 0 1 ∨ τ = finRotate 3 * Equiv.swap 0 1 ∨
      τ = finRotate 3 * finRotate 3 * Equiv.swap 0 1 := by decide
  rcases key σ with rfl | rfl | rfl | rfl | rfl | rfl
  · exact Realized.one F
  · exact hc
  · exact hmul hc hc
  · exact hs
  · exact hmul hs hc
  · exact hmul hs (hmul hc hc)

theorem realized_signs [Finite K] (F : Frame K) (T : Finset (Fin 3)) :
    Realized F 1 (fun i => if i ∈ T then -1 else 1) := by
  induction T using Finset.induction_on with
  | empty => simpa using Realized.one F
  | insert j T hj ih =>
    have h := (realized_signChange F j).mul ih
    rw [mul_one] at h
    convert h using 1
    funext i
    by_cases hi : i = j
    · subst hi; simp [hj]
    · by_cases hiT : i ∈ T <;> simp [hi, hiT]

theorem exists_realizer [Finite K] (F : Frame K) (σ : Equiv.Perm (Fin 3)) (ε : Fin 3 → ZMod 3)
    (hε : ∀ i, ε i ≠ 0) :
    ∃ n : ↥(Omega7 K), ∀ v : F3Cube, n * c₀ F v * n⁻¹ =
      c₀ F (Multiplicative.ofAdd fun i => ε i * Multiplicative.toAdd v (σ i)) := by
  have hsign : Realized F 1 (fun i => ε (σ.symm i)) := by
    have e : (fun i => ε (σ.symm i)) =
        fun i => if i ∈ Finset.univ.filter (fun j => ε (σ.symm j) = -1) then -1 else 1 := by
      funext i
      have h3 : ∀ x : ZMod 3, x ≠ 0 → x = 1 ∨ x = -1 := by decide
      rcases h3 _ (hε (σ.symm i)) with h | h <;> simp [h]
    rw [e]
    exact realized_signs F _
  have h := (realized_perm F σ).mul hsign
  have e : (fun i => 1 * ε (σ.symm (σ i))) = ε := by
    funext i
    simp
  rw [one_mul, e] at h
  exact h

end CFSG.ClassicalGroups.Orthogonal.Omega7ThreeLocal
