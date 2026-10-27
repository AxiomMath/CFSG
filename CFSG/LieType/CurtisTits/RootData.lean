module

public import Mathlib.GroupTheory.Coxeter.Length
public import Mathlib.Algebra.Module.LinearMap.End
public import TauCeti.GroupTheory.Coxeter.Parabolic

public section

namespace CFSG.LieType.CurtisTits

variable {I : Type*} {M : CoxeterMatrix I} {W : Type*} [Group W] (cs : CoxeterSystem M W)

structure IsCTRootSystem [DecidableEq I] (ρ : W →* Module.End ℤ (I → ℤ)) (Φ : Set (I → ℤ)) :
    Prop where
  single_mem : ∀ i, Pi.single i 1 ∈ Φ
  smul_mem : ∀ (w : W), ∀ γ ∈ Φ, ρ w γ ∈ Φ
  exists_eq : ∀ γ ∈ Φ, ∃ (w : W) (i : I) (c : ℤ), c ≠ 0 ∧ γ = c • ρ w (Pi.single i 1)
  simple_single : ∀ i, ρ (cs.simple i) (Pi.single i 1) = -Pi.single i 1
  simple_apply_of_ne : ∀ (i : I) (v : I → ℤ) (j : I), j ≠ i → ρ (cs.simple i) v j = v j
  not_isLeftDescent : ∀ (v : W) (k : I), 0 ≤ ρ v⁻¹ (Pi.single k 1) → ¬ cs.IsLeftDescent v k
  eq_single : ∀ (J : Set I) (u : W) (i : I), (∀ j ∈ J, ¬ cs.IsLeftDescent u j) →
    (∀ k ∉ J, ρ u (Pi.single i 1) k = 0) → ∃ m ∈ J, ρ u (Pi.single i 1) = Pi.single m 1
  exists_parabolic : ∀ (J : Set I) (w : W) (i : I), (∀ k ∉ J, ρ w (Pi.single i 1) k = 0) →
    ∃ z ∈ cs.parabolic J, ∃ m ∈ J, ρ z (ρ w (Pi.single i 1)) = Pi.single m 1

end CFSG.LieType.CurtisTits
