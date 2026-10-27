module

public import CFSG.ClassicalInvolution.Q3.Q3AM289S4LCfg
import CFSG.ClassicalGroups.Orthogonal.Represents

public section

set_option linter.unusedSectionVars false

namespace CFSG.ClassicalInvolution.Q3.Q3AM.S4L

open QuadraticMap CFSG.ClassicalGroups.Orthogonal CFSG.ClassicalInvolution.Asc77.SPN

variable {F V : Type} [Field F] [AddCommGroup V] [Module F V] {Q : QuadraticForm F V}
  [Finite F] [FiniteDimensional F V]

theorem exists_isON (hodd : Odd (Nat.card F)) (hQ : (polarBilin Q).Nondegenerate) :
    ∀ n : ℕ, n + 1 ≤ Module.finrank F V → ∃ w : Fin n → V, IsON Q w := by
  have h2 : (2 : F) ≠ 0 := two_ne_zero_of_odd hodd
  intro n
  induction n with
  | zero => exact fun _ => ⟨Fin.elim0, ⟨fun i => i.elim0, fun i => i.elim0⟩⟩
  | succ n ih =>
    intro hn
    obtain ⟨w, hw⟩ := ih (by omega)
    have hS := polarNondegOn_Cmp hw h2 hQ
    have hdim : 2 ≤ Module.finrank F (Cmp w Q) := by
      have := finrank_Cmp hw h2
      omega
    obtain ⟨x, hxS, hQx⟩ := hS.exists_map_eq h2 hdim 1
    have hxw : ∀ j, polar Q x (w j) = 0 := fun j =>
      (mem_Cmp_iff.mp hxS) (w j) (w_mem_Sp (Finset.mem_univ j))
    refine ⟨Fin.snoc w x, ⟨fun i => ?_, fun i j hij => ?_⟩⟩
    · refine Fin.lastCases ?_ (fun j => ?_) i
      · simpa using hQx
      · simpa using hw.q j
    · rcases Fin.eq_castSucc_or_eq_last i with ⟨i', rfl⟩ | rfl <;>
        rcases Fin.eq_castSucc_or_eq_last j with ⟨j', rfl⟩ | rfl
      · have : i' ≠ j' := fun e => hij (by rw [e])
        simpa using hw.o i' j' this
      · simpa [polar_comm] using hxw i'
      · simpa using hxw j'
      · exact absurd rfl hij

theorem vFrames_of_regular (hodd : Odd (Nat.card F)) (h3 : (3 : F) = 0)
    (hQ : (polarBilin Q).Nondegenerate) (hdim : 7 ≤ Module.finrank F V) : VFrames Q := by
  obtain ⟨w, hw⟩ := exists_isON hodd hQ 6 hdim
  exact vFrames_of_orthonormal hodd h3 hQ hdim hw

end CFSG.ClassicalInvolution.Q3.Q3AM.S4L
