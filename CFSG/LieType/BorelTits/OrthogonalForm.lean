module

public import CFSG.LieType.BorelTits.FormFlag
public import CFSG.LieType.BorelTits.Matrix
public import CFSG.Assembly.LowTwoRankDefs

public section

namespace CFSG.LieType.BorelTits

open Matrix CFSG.Assembly.LowTwoRank

universe u v

variable {K : Type u} [Field K] {V : Type v} [AddCommGroup V] [Module K V]

structure QuadForm (K : Type u) (V : Type v) [Field K] [AddCommGroup V] [Module K V] where
  Q : V → K
  polar : ReflForm K V
  polar_σ : polar.σ = RingEquiv.refl K
  Q_smul : ∀ (c : K) (v : V), Q (c • v) = c ^ 2 * Q v
  Q_add : ∀ u v : V, Q (u + v) = Q u + Q v + polar.β u v

namespace QuadForm

variable (Φ : QuadForm K V)

theorem polar_symm (u v : V) : Φ.polar.β u v = Φ.polar.β v u := by
  have h1 := Φ.Q_add u v
  have h2 := Φ.Q_add v u
  rw [add_comm v u] at h2
  linear_combination h2 - h1

theorem polar_self (v : V) : Φ.polar.β v v = 2 * Q Φ v := by
  have h := Φ.Q_add v v
  have h2 : v + v = (2 : K) • v := by rw [two_smul]
  rw [h2, Φ.Q_smul] at h
  linear_combination -h

theorem Q_zero : Φ.Q 0 = 0 := by
  have := Φ.Q_smul 0 0
  rwa [zero_smul, zero_pow two_ne_zero, zero_mul] at this

theorem polar_map_of_Q {g : V →ₗ[K] V} (hg : ∀ v, Φ.Q (g v) = Φ.Q v) (u v : V) :
    Φ.polar.β (g u) (g v) = Φ.polar.β u v := by
  have h1 := Φ.Q_add (g u) (g v)
  have h2 := Φ.Q_add u v
  rw [← map_add, hg, hg, hg] at h1
  linear_combination h2 - h1

end QuadForm

section Matrix

variable {ι : Type} [Fintype ι] [DecidableEq ι] {K' : Type} [Field K']

abbrev orthGroup (Q : (ι → K') → K') : Subgroup (GL ι K') :=
  Subgroup.closure {A : GL ι K' | ∀ v, Q ((A : Matrix ι ι K') *ᵥ v) = Q v}

theorem orthGroup_preserves (Q : (ι → K') → K') {A : GL ι K'} (hA : A ∈ orthGroup Q)
    (v : ι → K') : Q ((A : Matrix ι ι K') *ᵥ v) = Q v := by
  induction hA using Subgroup.closure_induction generalizing v with
  | mem A hA => exact hA v
  | one => simp
  | mul A B _ _ hA hB =>
    rw [Units.val_mul, ← Matrix.mulVec_mulVec, hA, hB]
  | inv A _ hA =>
    rw [← hA]
    simp [Matrix.mulVec_mulVec]

theorem statedOmega_le_orthGroup (Q : (ι → K') → K') : StatedOmega Q ≤ orthGroup Q :=
  Subgroup.commutator_le.mpr fun g₁ h₁ g₂ h₂ => by
    rw [commutatorElement_def]
    exact mul_mem (mul_mem (mul_mem h₁ h₂) (inv_mem h₁)) (inv_mem h₂)

theorem isIsometric_natRep_statedOmega (Φ : QuadForm K' (ι → K')) :
    IsIsometric Φ.polar (natRep (StatedOmega Φ.Q)) := by
  intro h u v
  rw [natRep_apply, natRep_apply]
  exact Φ.polar_map_of_Q (g := Matrix.toLin' ((h : GL ι K') : Matrix ι ι K'))
    (fun w => orthGroup_preserves Φ.Q (statedOmega_le_orthGroup Φ.Q h.2) w) u v

end Matrix

end CFSG.LieType.BorelTits
