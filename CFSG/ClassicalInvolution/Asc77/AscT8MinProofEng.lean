module

public import CFSG.ClassicalInvolution.Asc77.AscT8Min

public section

namespace CFSG.ClassicalInvolution.Asc77

open CFSG.Open CFSG.ClassicalInvolution CFSG.ClassicalInvolution.Generic

namespace T8

variable {G : Type} [Group G] [Finite G]

theorem four_le_natCard_closure_pairE {z b : G} (hz : z * z = 1) (hz1 : z ≠ 1) (hb1 : b ≠ 1)
    (hne : z ≠ b) :
    4 ≤ Nat.card (Subgroup.closure ({z, b} : Set G)) := by
  have hzE : z ∈ Subgroup.closure ({z, b} : Set G) := Subgroup.subset_closure (by simp)
  have hbE : b ∈ Subgroup.closure ({z, b} : Set G) := Subgroup.subset_closure (by simp)
  have hzbE : z * b ∈ Subgroup.closure ({z, b} : Set G) := Subgroup.mul_mem _ hzE hbE
  have h1 : z * b ≠ 1 := mul_ne_one_of_ne hz hne
  have h2 : z * b ≠ z := fun h => hb1 (by simpa using h)
  have h3 : z * b ≠ b := fun h => hz1 (by simpa using h)
  let F : Fin 4 → Subgroup.closure ({z, b} : Set G) := ![⟨1, Subgroup.one_mem _⟩, ⟨z, hzE⟩,
    ⟨b, hbE⟩, ⟨z * b, hzbE⟩]
  have hF : Function.Injective F := by
    intro i j hij
    fin_cases i <;> fin_cases j <;>
      simp [F, Subtype.ext_iff, hz1, hb1, hne, h1, h2, h3, Ne.symm hz1, Ne.symm hb1, Ne.symm hne,
        Ne.symm h1, Ne.symm h2, Ne.symm h3] at hij ⊢
  have := Nat.card_le_card_of_injective F hF
  simpa using this

end T8

end CFSG.ClassicalInvolution.Asc77
