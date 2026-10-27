module

public import CFSG.ClassicalInvolution.Q3.Q3T6LinEquiv
public import CFSG.ClassicalInvolution.Q3.Basic

public section

namespace CFSG.ClassicalInvolution.Q3.Q3T6

open CFSG.Open CFSG.ClassicalInvolution
open scoped MatrixGroups

variable {Y : Type} [Group Y] [Finite Y] {L : Subgroup Y} {z : Y}

theorem quaternion_sylow_of_isClassicalMember3 (h : IsClassicalMember3 L z) (T : Sylow 2 L) :
    Nonempty ((T : Subgroup L) ≃* QuaternionGroup 2) := by
  obtain ⟨e⟩ := h.nonempty_equiv
  exact exists_quaternion_of_quotEquiv_sl2Three e T

theorem quaternion_sylow_of_isClassicalMember3' (h : IsClassicalMember3 L z) (T : Sylow 2 L) :
    ∃ r : ℕ, 3 ≤ r ∧ Nonempty ((T : Subgroup L) ≃* QuaternionGroup (2 ^ (r - 2))) :=
  ⟨3, le_rfl, quaternion_sylow_of_isClassicalMember3 h T⟩

omit [Finite Y] in
theorem isSolvable_oddCoreQuotient_of_isClassicalMember3 (h : IsClassicalMember3 L z) :
    Group.IsSolvable (L ⧸ classicalInvolutionOddCore L) := by
  obtain ⟨e⟩ := h.nonempty_equiv
  exact isSolvable_of_equiv_sl2Three e

theorem mem_commutator_of_isClassicalMember3 (h : IsClassicalMember3 L z) {g : L}
    (hg : ∃ n : ℕ, g ^ 2 ^ n = 1) : g ∈ commutator L := by
  obtain ⟨e⟩ := h.nonempty_equiv
  let φ : ↥L →* SL(2, ZMod 3) :=
    e.toMonoidHom.comp (QuotientGroup.mk' (classicalInvolutionOddCore L))
  have hker : φ.ker = classicalInvolutionOddCore L := by
    ext x
    simp only [φ, MonoidHom.mem_ker, MonoidHom.comp_apply, MulEquiv.coe_toMonoidHom,
      MulEquiv.map_eq_one_iff, QuotientGroup.mk'_apply, QuotientGroup.eq_one_iff]
  refine mem_commutator_of_two_element_of_oddKernel φ
    (e.surjective.comp (QuotientGroup.mk'_surjective _)) ?_ hg
  rw [hker]
  exact CFSG.ComponentClassification.OddCore.odd_card L

end CFSG.ClassicalInvolution.Q3.Q3T6
