module

public import CFSG.Assembly.LowTwoRankDefs
public import CFSG.LocalAnalysis.QuasithinUnique.CompNormSylow

public section

namespace CFSG.QuasithinUnique.Ch1.AltSeven
open Equiv Equiv.Perm CFSG.Open CFSG.QuasithinUnique

@[expose] def fixCount (σ : Perm (Fin 7)) : ℕ :=
  (Finset.univ.filter fun i : Fin 7 => σ i = i).card

@[expose] def P22 (σ : Perm (Fin 7)) : Prop :=
  ∃ c : Perm (Fin 7), Perm.sign c = 1 ∧ c * c * c = 1 ∧ c ≠ 1 ∧ σ * c = c * σ ∧
    ∀ g : Perm (Fin 7), Perm.sign g = 1 → σ * g = g * σ → g * c * g⁻¹ = c ∨ g * c * g⁻¹ = c⁻¹

instance (σ : Perm (Fin 7)) : Decidable (P22 σ) := by unfold P22; infer_instance

@[expose] def Q2 (σ : Perm (Fin 7)) : Prop :=
  ∀ x : Perm (Fin 7), Perm.sign x = 1 → σ * x = x * σ → x * x = 1 → x ≠ 1 →
    ∃ g : Perm (Fin 7), Perm.sign g = 1 ∧ σ * g = g * σ ∧
      (x * (g * x * g⁻¹)) ^ 3 = 1 ∧ x * (g * x * g⁻¹) ≠ 1

instance (σ : Perm (Fin 7)) : Decidable (Q2 σ) := by unfold Q2; infer_instance

end CFSG.QuasithinUnique.Ch1.AltSeven
