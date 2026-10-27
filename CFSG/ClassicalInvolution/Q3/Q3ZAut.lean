module

public import CFSG.ClassicalInvolution.Q3.Q3ZAutAbs

public section

namespace CFSG.ClassicalInvolution.Q3.Q3Z

open CFSG.Assembly.LowTwoRank CFSG.ClassicalInvolution.Models.SymplecticPairs
open scoped MatrixGroups

theorem aut_dichotomy (α : SL(2, ZMod 3) ≃* SL(2, ZMod 3)) :
    (∃ B : StatedSp 2 (ZMod 3),
        (∀ A : SL(2, ZMod 3),
          B * shortBlock (ZMod 3) (zero_ne_one : (0 : Fin 2) ≠ 1) A * B⁻¹ =
            shortBlock (ZMod 3) zero_ne_one (α A)) ∧
        (∀ A : SL(2, ZMod 3),
          (∃ A' : SL(2, ZMod 3),
            B * longBlock (ZMod 3) 2 1 A * B⁻¹ = longBlock (ZMod 3) 2 1 A') ∧
          (∃ A'' : SL(2, ZMod 3),
            B⁻¹ * longBlock (ZMod 3) 2 1 A * B = longBlock (ZMod 3) 2 1 A''))) ∨
    (∃ k : Fin 24, gluingComplete k = false ∧
        α autXp = evalW gluingAssign (gluingA k) ∧ α autXm = evalW gluingAssign (gluingB k)) := by
  obtain ⟨k, hp, hm⟩ := aut_pair_cases α
  by_cases hk : k.val < 4
  · left
    obtain ⟨j, rfl⟩ : ∃ j : Fin 4, Fin.castLE (by norm_num) j = k :=
      ⟨⟨k.val, hk⟩, Fin.ext rfl⟩
    rw [evalW_gluingA_castLE] at hp
    rw [evalW_gluingB_castLE] at hm
    exact absorbed_of_pair j α hp hm
  · right
    exact ⟨k, decide_eq_false hk, hp, hm⟩

end CFSG.ClassicalInvolution.Q3.Q3Z
