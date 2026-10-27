module

public import CFSG.LocalAnalysis.OddStandard.Solomon75Sec5Frac

public section

namespace CFSG.OddStandard.Solomon75

open Equiv Equiv.Perm Subgroup CFSG CFSG.GH74.GLS
open scoped commutatorElement

variable {X : Type} [Group X] [Finite X] {n : ℕ} {z : X} {Z : Subgroup X}
  {S : Sylow 2 ↥(normalizer (Z : Set X))}

theorem Sec5Data.exists_witness_Z (h : Sec5Data X n z Z S) {s : X} (hs : IsSec5Inv X Z s)
    {A : Subgroup X} (hA : Sec5Comp X n (normalizer (Z : Set X)) A)
    (hsA : s ∈ normalizer (A : Set X)) :
    ∃ u : X, IsIntrinsicIn X (normalizer (Z : Set X)) A u ∧ u ∈ Z ∧ u ≠ 1 ∧ u * s = s * u := by
  obtain ⟨u, hu⟩ := hA.1
  have hu2 : u * u = 1 := by
    rw [← sq]; have := pow_orderOf_eq_one u; rwa [hu.1] at this
  have hu1 : u ≠ 1 := by
    intro h1
    have := hu.1
    rw [h1, orderOf_one] at this
    exact absurd this (by norm_num)
  have huZ : u ∈ Z := h.mem_Z_of_comm_mem hA hu.2.1 hu2 (fun a ha => hu.comm_mem a ha)
  exact ⟨u, hu, huZ, hu1, h.comm_of_mem_Z_of_normalizes hs.mem hA hsA huZ hu.2.1 hu1⟩

end CFSG.OddStandard.Solomon75
