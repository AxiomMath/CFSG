module

public import CFSG.ClassicalInvolution.Q3.PhilipHall.Frame.Thm1RTwinDefs

public section

namespace CFSG.ClassicalInvolution.Q3.PhilipHall.Frame.TwinPerp

open CFSG CFSG.Open CFSG.ClassicalInvolution CFSG.ClassicalInvolution.Generic
  CFSG.ClassicalInvolution.Asc77 CFSG.ClassicalInvolution.Disconnected.AschTight
  CFSG.ClassicalInvolution.Q3 CFSG.ClassicalInvolution.Q3.PhilipHall.Frame

section Vocabulary

variable {Y : Type} [Group Y]

@[expose] def TwoTwins (R : Subgroup Y) : Prop :=
  ∀ A ∈ twinSet (CoreAssembly.conjClass (tightCore R)) (tightCore R),
    ∀ B ∈ twinSet (CoreAssembly.conjClass (tightCore R)) (tightCore R),
      ∀ C ∈ twinSet (CoreAssembly.conjClass (tightCore R)) (tightCore R), A = B ∨ A = C ∨ B = C

theorem twinSet_eq_pair {R : Subgroup Y} (h2 : TwoTwins R)
    {K' : Subgroup Y} (hK' : K' ∈ twinSet (CoreAssembly.conjClass (tightCore R)) (tightCore R))
    (hne : K' ≠ tightCore R) :
    twinSet (CoreAssembly.conjClass (tightCore R)) (tightCore R) = {tightCore R, K'} := by
  have hK0 : tightCore R ∈ twinSet (CoreAssembly.conjClass (tightCore R)) (tightCore R) := by
    obtain ⟨-, z, hz, -⟩ := hK'
    exact ⟨CoreAssembly.mem_conjClass_self _, z, hz, hz⟩
  ext J
  constructor
  · intro hJ
    rcases h2 _ hK0 _ hK' _ hJ with h | h | h
    · exact absurd h.symm hne
    · exact Or.inl h.symm
    · exact Or.inr h.symm
  · rintro (rfl | rfl)
    · exact hK0
    · exact hK'

theorem twoTwins_of_eq_pair {R : Subgroup Y} {K' : Subgroup Y}
    (hV : twinSet (CoreAssembly.conjClass (tightCore R)) (tightCore R) = {tightCore R, K'}) :
    TwoTwins R := by
  intro A hA B hB C hC
  rw [hV] at hA hB hC
  rcases hA with rfl | rfl <;> rcases hB with rfl | rfl <;> rcases hC with rfl | rfl <;> simp

end Vocabulary

end CFSG.ClassicalInvolution.Q3.PhilipHall.Frame.TwinPerp
