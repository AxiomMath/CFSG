module

public import CFSG.LocalAnalysis.OddStandard.SmallF3.Omega.Sec4Defs

public section

namespace CFSG.OddStandard.SmallF3.Omega

open Equiv.Perm

theorem sec7l78_fix_all : ∀ v : Fin 5 → ZMod 2, ∑ i, v i = 0 →
    (∀ σ : Equiv.Perm (Fin 5), permVec σ v = v) → v = 0 := by
  decide +kernel

theorem sec7l78_two_cycles : ∃ τ₁ τ₂ : Equiv.Perm (Fin 5), τ₁ ^ 3 = 1 ∧ τ₂ ^ 3 = 1 ∧
    ∀ w : Fin 5 → ZMod 2, ∑ i, w i = 0 → permVec τ₁ w = w → permVec τ₂ w = w → w = 0 := by
  refine ⟨Equiv.swap 0 1 * Equiv.swap 1 2, Equiv.swap 2 3 * Equiv.swap 3 4, ?_, ?_, ?_⟩
  all_goals decide +kernel

@[expose] def Sec7L78Fix (τ₁ τ₂ : Equiv.Perm (Fin 5)) (w : Fin 5 → ZMod 2) : Prop :=
  ∑ i, w i = 0 ∧ permVec τ₁ w = w ∧ permVec τ₂ w = w

instance (τ₁ τ₂ : Equiv.Perm (Fin 5)) (w : Fin 5 → ZMod 2) : Decidable (Sec7L78Fix τ₁ τ₂ w) := by
  unfold Sec7L78Fix; infer_instance

theorem sec7l78_stab_eight : ∀ v : Fin 5 → ZMod 2, ∑ i, v i = 0 → v ≠ 0 →
    8 ∣ Fintype.card {σ : Equiv.Perm (Fin 5) // permVec σ v = v} →
      ∃ τ₁ τ₂ : Equiv.Perm (Fin 5), τ₁ ^ 3 = 1 ∧ τ₂ ^ 3 = 1 ∧ permVec τ₁ v = v ∧
        permVec τ₂ v = v ∧ ∀ w : Fin 5 → ZMod 2, ∑ i, w i = 0 →
          permVec τ₁ w = w → permVec τ₂ w = w → w = 0 ∨ w = v := by
  have h : ∀ v : Fin 5 → ZMod 2, ∑ i, v i = 0 → v ≠ 0 →
      8 ∣ Fintype.card {σ : Equiv.Perm (Fin 5) // permVec σ v = v} →
      ∃ τ₁ τ₂ : Equiv.Perm (Fin 5), τ₁ ^ 3 = 1 ∧ τ₂ ^ 3 = 1 ∧ permVec τ₁ v = v ∧
        permVec τ₂ v = v ∧ ∀ w : Fin 5 → ZMod 2, Sec7L78Fix τ₁ τ₂ w → w = 0 ∨ w = v := by
    decide +kernel
  intro v hv hv0 h8
  obtain ⟨τ₁, τ₂, h1, h2, h3, h4, h5⟩ := h v hv hv0 h8
  exact ⟨τ₁, τ₂, h1, h2, h3, h4, fun w hw hw1 hw2 => h5 w ⟨hw, hw1, hw2⟩⟩

theorem sec7l78_gen_pair : ∀ a b : Fin 5, a ≠ b → ∃ τ : Equiv.Perm (Fin 5), τ ^ 3 = 1 ∧
    ∃ w : Fin 5 → ZMod 2, ∑ i, w i = 0 ∧
      w + permVec τ w = (Pi.single a 1 + Pi.single b 1 : Fin 5 → ZMod 2) := by
  decide +kernel

theorem sec7l78_exists_pair : ∀ w : Fin 5 → ZMod 2, ∑ i, w i = 0 → w ≠ 0 →
    ∃ a b : Fin 5, a ≠ b ∧ w a = 1 ∧ w b = 1 := by
  decide +kernel

theorem sec7l78_reduce : ∀ (w : Fin 5 → ZMod 2) (a b : Fin 5), a ≠ b → w a = 1 → w b = 1 →
    vecWeight (w + (Pi.single a 1 + Pi.single b 1 : Fin 5 → ZMod 2)) < vecWeight w ∧
      (∑ i, w i = 0 → ∑ i, (w + (Pi.single a 1 + Pi.single b 1 : Fin 5 → ZMod 2)) i = 0) := by
  decide +kernel

end CFSG.OddStandard.SmallF3.Omega
