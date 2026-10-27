module

public import CFSG.ClassicalInvolution.Uniform.UExact
public import CFSG.ClassicalInvolution.Q3.Q3T6CoreRestr

public section

set_option linter.unusedSectionVars false

namespace CFSG.ClassicalInvolution.Q3.Q3T6

open CFSG.Open (classicalInvolutionOddCore)
open CFSG.ClassicalInvolution CFSG.ClassicalInvolution.Generic
  CFSG.ClassicalInvolution.Asc77 CFSG.ClassicalInvolution.Uniform
open scoped MatrixGroups

section Exact

variable {ι : Type} {X : Type} [Group X] {Φ : Set (Subgroup X)}

theorem oddCore_eq_bot_of_system (D : LieSystemDataU 3 1 ι X Φ)
    (hcl : ∀ L ∈ Φ, ∃ z, IsClassicalMemberU (.sl2 3 1) L z) :
    ∀ L ∈ Φ, classicalInvolutionOddCore ↥L = ⊥ := by
  intro L hL
  obtain ⟨z, hz⟩ := hcl L hL
  have hs : (MemberType.sl2 3 1).IsSolvableType := (by norm_num : (3 : ℕ) ^ 1 = 3)
  exact hz.oddCore_eq_bot_of_natCard_eq hs (D.card_eq rfl L hL)

end Exact

section Section

variable {Y₀ : Type} [Group Y₀] [Finite Y₀] {Λ₀ : Set (Subgroup Y₀)}

theorem sectionFamily_classical (hΩ : HypOmegaModU (.sl2 3 1) Λ₀) :
    ∀ L ∈ oddQuotientFamily (restrictFamily Λ₀ (omegaGen Λ₀)),
      ∃ z, IsClassicalMemberU (.sl2 3 1) L z := by
  rintro _ ⟨K, hK, rfl⟩
  obtain ⟨z, hz⟩ := (hypOmegaModU_restrict hΩ (omegaGen Λ₀)).classical K hK
  exact ⟨_, isClassicalMember3_iff_U.mp (isClassicalMember3_iff_U.mpr hz).map_oddQuotient⟩

end Section

end CFSG.ClassicalInvolution.Q3.Q3T6
