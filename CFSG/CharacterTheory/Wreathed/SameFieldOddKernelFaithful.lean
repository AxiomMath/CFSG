module

public import CFSG.CharacterTheory.Wreathed.OddKernelFixedSpaceCharacter
public import CFSG.Dihedral.DisconnectedInvolutionGraph.IrreducibleDegree
public import Mathlib.Order.CompletePartialOrder

public noncomputable section

namespace CFSG.Wreathed.SameFieldOddKernel

variable {G : Type*} [Group G] [IsSimpleGroup G]
variable {V : Type*} [AddCommGroup V] [Module ℂ V]

theorem representation_ker_eq_bot_of_simple (ρ : Representation ℂ G V)
    (hρ : ∃ g : G, ρ g ≠ 1) : MonoidHom.ker ρ = ⊥ := by
  rcases IsSimpleGroup.eq_bot_or_eq_top_of_normal (MonoidHom.ker ρ) with h | h
  · exact h
  · obtain ⟨g, hg⟩ := hρ
    exact False.elim (hg (MonoidHom.mem_ker.mp (h ▸ Subgroup.mem_top g)))

theorem irreducible_ker_eq_bot_of_degree_ne_one [FiniteDimensional ℂ V]
    (ρ : Representation ℂ G V) [ρ.IsIrreducible] (hdegree : ρ.character 1 ≠ 1) :
    MonoidHom.ker ρ = ⊥ := by
  apply representation_ker_eq_bot_of_simple ρ
  apply CFSG.DisconnectedInvolutionGraph.Helpers.irreducible_nonprincipal_action_nontrivial ρ
  intro h
  exact hdegree (congrFun h 1)

omit [IsSimpleGroup G] in
theorem subgroup_eq_bot_of_image_le_ker (ρ : Representation ℂ G V)
    (hρ : MonoidHom.ker ρ = ⊥) (K : Subgroup G) (O : Subgroup K)
    (hO : O.map K.subtype ≤ MonoidHom.ker ρ) : O = ⊥ := by
  apply le_bot_iff.mp
  intro o ho
  have hmem : (o : G) ∈ MonoidHom.ker ρ := hO ⟨o, ho, rfl⟩
  have hone : (o : G) = 1 := Subgroup.mem_bot.mp (hρ ▸ hmem)
  exact Subgroup.mem_bot.mpr (Subtype.ext hone)

section FixedSpace

variable {G V : Type} [Group G] [IsSimpleGroup G]
variable [AddCommGroup V] [Module ℂ V] [FiniteDimensional ℂ V]

omit [IsSimpleGroup G] in
theorem oddKernel_eq_bot_of_fixedSpace_finrank (ρ : Representation ℂ G V)
    (hρ : MonoidHom.ker ρ = ⊥) (K : Subgroup G) (O : Subgroup K)
    (hfixed : Module.finrank ℂ
      (Representation.invariants ((ρ.comp K.subtype).comp O.subtype)) =
        Module.finrank ℂ V) : O = ⊥ := by
  apply subgroup_eq_bot_of_image_le_ker ρ hρ K O
  rw [Subgroup.map_le_iff_le_comap, MonoidHom.comap_ker]
  exact (finrank_invariants_eq_finrank_iff (ρ.comp K.subtype) O).mp hfixed

theorem oddKernel_eq_bot_of_fixedSpace_character_degree (ρ : Representation ℂ G V)
    [ρ.IsIrreducible] (hdegree : ρ.character 1 ≠ 1)
    (K : Subgroup G) (O : Subgroup K) [O.Normal]
    (hfixed : (fixedSpaceQuotientRepresentation ρ K O).character 1 = ρ.character 1) :
    O = ⊥ := by
  apply oddKernel_eq_bot_of_fixedSpace_finrank ρ
    (irreducible_ker_eq_bot_of_degree_ne_one ρ hdegree) K O
  rw [fixedSpaceQuotientRepresentation_character_one, Representation.char_one,
    Nat.cast_inj] at hfixed
  exact hfixed

end FixedSpace

end CFSG.Wreathed.SameFieldOddKernel
