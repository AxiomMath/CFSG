module

public import CFSG.GH74.GLS.Stage2.Signalizer.Ivk8P4S55GenAct

public section

namespace CFSG.GH74.GLS.Stage2.Signalizer.Ivk8

open Subgroup

theorem evenParabolics_of_parity {p : ℕ} {Y : Type} [Group Y] [Finite Y]
    (h : ∀ (S : Sylow p Y) (M : Subgroup Y), M ≠ ⊤ →
      normalizer ((S : Subgroup Y) : Set Y) ≤ M →
        ∃ a m : ℕ, Nat.card ↥M ∣ a ∧ Nat.card Y = a * m ∧ 2 ∣ m) :
    EvenParabolics p Y := by
  intro S M hSM hM
  obtain ⟨a, m, ⟨e, he⟩, hYam, hm2⟩ := h S M hM hSM
  have hpos : 0 < Nat.card ↥M := Nat.card_pos
  have hidx : M.index = e * m := by
    apply Nat.eq_of_mul_eq_mul_left hpos
    rw [Subgroup.card_mul_index, hYam, he]
    ring
  rw [hidx]
  exact (even_iff_two_dvd.2 hm2).mul_left e

end CFSG.GH74.GLS.Stage2.Signalizer.Ivk8
