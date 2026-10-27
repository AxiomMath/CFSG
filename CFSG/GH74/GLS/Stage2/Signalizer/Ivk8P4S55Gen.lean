module

public import CFSG.GH74.GLS.Stage2.Signalizer.Ivk8P4S55Cross
public import CFSG.GH74.GLS.Stage2.Signalizer.Ivk8P4S55GenB

public section

namespace CFSG.GH74.GLS.Stage2.Signalizer.Ivk8

open Subgroup CFSG CFSG.Assembly.LowTwoRank CFSG.GH74.GLS.Stage12

@[expose] def OuterFalse (p : ℕ) (Y : Type) [Group Y] : Prop :=
  ∀ α : MulAut Y, α ∉ (MulAut.conj : Y →* MulAut Y).range → α ^ p = 1 →
    (∃ S : Sylow 2 Y, ∀ s ∈ S, α s = s) →
    (∀ r : ℕ, r.Prime → r ≠ 2 → r ≠ p → ∀ Q : Subgroup Y, IsPGroup r ↥Q →
      (∀ x ∈ Q, α x ∈ Q) → ∀ x ∈ Q, α x = x) → False

structure DefData (p : ℕ) (Y : Type) [Group Y] : Prop where
  bt : BorelTitsConcl p Y
  ep : EvenParabolics p Y
  outer : OuterFalse p Y

theorem def55_of_defData {Fd : ℕ → (Y : Type) → [Group Y] → Prop}
    (h : ∀ (p : ℕ) (Y : Type) [Group Y] [Finite Y], p.Prime → p ≠ 2 → center Y = ⊥ →
      Fd p Y → DefData p Y) :
    Def55 Fd := by
  intro k p Γ _ _ V _ _ _ ρ K a P R hf hFd
  exfalso
  have := hf.normal
  have hZ := center_quot_eq_bot hf.quasi
  have D := h p (K ⧸ center ↥K) hf.prime hf.odd hZ hFd
  by_cases hU : innerPart (K := K) P = ⊥
  · have hnotinn : actYHom (K := K) a ∉
        (MulAut.conj : (K ⧸ center ↥K) →* MulAut (K ⧸ center ↥K)).range := by
      rintro ⟨y, hy⟩
      have hyU : y ∈ innerPart (K := K) P := mem_innerPart.mpr ⟨a, hf.a_mem, hy.symm⟩
      rw [hU, Subgroup.mem_bot] at hyU
      apply hf.actYHom_ne_one
      rw [← hy, hyU, map_one]
    exact D.outer _ hnotinn hf.actYHom_pow (hf.exists_sylow_fixed hU)
      fun r hr hr2 hrp Q hQ hinv x hx => hf.actYHom_eq_of_invariant hr hr2 hrp hQ hinv hx
  · exact hf.false_of_innerPart_ne_bot D.bt D.ep hU

end CFSG.GH74.GLS.Stage2.Signalizer.Ivk8
