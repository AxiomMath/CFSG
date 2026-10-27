module

public import CFSG.ClassicalInvolution.SolvableCase.Structure
public import CFSG.ClassicalInvolution.SolvableCase.Tight
public import CFSG.Adapters.ProjectiveSpecialLinear

public section

namespace CFSG.ClassicalInvolution.Q3

open CFSG CFSG.Open CFSG.ClassicalInvolution
open scoped MatrixGroups

universe u

theorem nonempty_mulEquiv_sl2Three_of_normal_odd_index {J : Type u} [Group J] [Finite J]
    [Group.IsSolvable J] (L : Subgroup J) [L.Normal] (hL : Odd L.index) (T : Sylow 2 L)
    (hT : Nonempty ((T : Subgroup L) ≃* QuaternionGroup 2))
    (hnot : ¬ IsPGroup 2 (J ⧸ oddCore J)) :
    Nonempty ((J ⧸ oddCore J) ≃* SL(2, ZMod 3)) := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  obtain ⟨P⟩ : Nonempty (Sylow 2 J) := inferInstance
  obtain ⟨e1⟩ := nonempty_mulEquiv_sylow_of_normal_odd_index L hL T P
  obtain ⟨e2⟩ := hT
  have hP : Nonempty ((P : Subgroup J) ≃* QuaternionGroup (2 ^ (3 - 2))) :=
    ⟨e1.symm.trans e2⟩
  rcases solvable_quaternion_oddCore_quotient P (r := 3) le_rfl hP with h | ⟨-, h⟩ | ⟨h4, -⟩
  · exfalso
    obtain ⟨e3⟩ := h
    apply hnot
    have hcard : Nat.card (QuaternionGroup (2 ^ (3 - 2))) = 2 ^ 3 := by
      rw [Nat.card_eq_fintype_card, QuaternionGroup.card]
      norm_num
    have : IsPGroup 2 (QuaternionGroup (2 ^ (3 - 2))) :=
      IsPGroup.of_card (n := 3) hcard
    exact this.of_equiv e3.symm
  · exact h
  · omega

end CFSG.ClassicalInvolution.Q3
