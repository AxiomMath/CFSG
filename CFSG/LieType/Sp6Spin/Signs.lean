module

public import CFSG.LieType.Sp6Spin.Sp6

public section

namespace CFSG.LieType.Sp6Spin

@[expose] def IsSrc (α : Fin 3 → ℤ) (σ : Fin 3 → Bool) : Prop :=
  ∀ i, (α i = 1 → σ i = false) ∧ (α i = -1 → σ i = true)

instance (α : Fin 3 → ℤ) (σ : Fin 3 → Bool) : Decidable (IsSrc α σ) := by
  unfold IsSrc
  infer_instance

@[expose] def flipAt (α : Fin 3 → ℤ) (σ : Fin 3 → Bool) : Fin 3 → Bool :=
  fun i => if α i = 0 then σ i else !σ i

theorem flipAt_flipAt (α : Fin 3 → ℤ) (σ : Fin 3 → Bool) : flipAt α (flipAt α σ) = σ := by
  funext i
  unfold flipAt
  split_ifs <;> simp

theorem flipAt_not (α : Fin 3 → ℤ) (σ : Fin 3 → Bool) :
    flipAt α (fun i => !σ i) = fun i => !flipAt α σ i := by
  funext i
  unfold flipAt
  split_ifs <;> rfl

theorem isSrc_not_flipAt_iff (α : Fin 3 → ℤ) (σ : Fin 3 → Bool) :
    IsSrc α (fun i => !flipAt α σ i) ↔ IsSrc α σ := by
  refine forall_congr' fun i => ?_
  unfold flipAt
  by_cases h1 : α i = 1
  · simp [h1]
  · by_cases h2 : α i = -1
    · simp [h2]
    · simp [h1, h2]

theorem exists_isSrc (α : Fin 3 → ℤ) : ∃ σ, IsSrc α σ :=
  ⟨fun i => decide (α i = -1), fun i => by
    refine ⟨fun h => ?_, fun h => by simp [h]⟩
    simp [h]⟩

open TauCeti.GLSymplecticFin CFSG.LieType.Universal.Symplectic in
theorem IsSrc.eq_or_eq {r : RootSubgroupIndex 3} (hr : IsShortIndex r) {σ τ : Fin 3 → Bool}
    (hσ : IsSrc (stdVec r) σ) (hτ : IsSrc (stdVec r) τ) :
    τ = σ ∨ τ = fun i => !flipAt (stdVec r) σ i := by
  revert σ τ
  rcases r with i | i | ⟨i, j, hij⟩ | ⟨i, j, hij⟩ | ⟨i, j, hij⟩
  · exact hr.elim
  · exact hr.elim
  all_goals
    clear hr
    revert hij
    fin_cases i <;> fin_cases j <;> decide

end CFSG.LieType.Sp6Spin
