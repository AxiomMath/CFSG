module

public import CFSG.LieType.Chevalley.RankOneGaussian

public section

namespace CFSG.HardMathSupport.Solomon.Coordinator.YS08.LieQ

open CFSG.LieType.Chevalley

theorem sl2_odd_order_card_two {K : Type} [Field K] [Finite K] (hK : Nat.card K = 2)
    (g : SL2 K) (hg : Nat.Coprime (orderOf g) 2) (hne : g ≠ 1) :
    g = uSL 1 * WSL ∨ g = (uSL 1 * WSL)⁻¹ := by
  have hdich : ∀ x : K, x = 0 ∨ x = 1 := by
    obtain ⟨y, -, huniq⟩ := (Nat.card_eq_two_iff' (0 : K)).mp hK
    intro x
    by_cases hx : x = 0
    · exact Or.inl hx
    · exact Or.inr ((huniq x hx).trans (huniq 1 one_ne_zero).symm)
  have h2 : (1 : K) + 1 = 0 := by
    rcases hdich (1 + 1) with h | h
    · exact h
    · have h10 : (1 : K) = 0 := by linear_combination h
      exact absurd h10 one_ne_zero
  have hneg : (-1 : K) = 1 := by linear_combination (-1 : K) * h2
  have h2' : (2 : K) = 0 := by linear_combination h2
  have hsq : g ^ 2 ≠ 1 := fun h2g =>
    hne (orderOf_eq_one_iff.mp (Nat.eq_one_of_dvd_coprimes hg (dvd_refl _)
      (orderOf_dvd_of_pow_eq_one h2g)))
  have hdet := det_SL2 g
  rcases hdich ((g : Matrix (Fin 2) (Fin 2) K) 0 0) with e00 | e00 <;>
    rcases hdich ((g : Matrix (Fin 2) (Fin 2) K) 0 1) with e01 | e01 <;>
    rcases hdich ((g : Matrix (Fin 2) (Fin 2) K) 1 0) with e10 | e10 <;>
    rcases hdich ((g : Matrix (Fin 2) (Fin 2) K) 1 1) with e11 | e11
  all_goals
    first
      | exfalso
        rw [e00, e01, e10, e11] at hdet
        norm_num [hneg] at hdet
        done
      | exfalso
        refine hsq ?_
        rw [sq]
        refine SL2_ext ?_ ?_ ?_ ?_ <;>
          simp [Matrix.SpecialLinearGroup.coe_mul, Matrix.mul_apply, Fin.sum_univ_two,
            Matrix.one_apply, e00, e01, e10, e11, h2, h2']
        done
      | left
        refine SL2_ext ?_ ?_ ?_ ?_ <;>
          simp [coe_uSL, coe_WSL, Matrix.SpecialLinearGroup.coe_mul, Matrix.mul_apply,
            Fin.sum_univ_two, e00, e01, e10, e11, h2, h2', hneg]
        done
      | right
        apply eq_inv_of_mul_eq_one_left
        refine SL2_ext ?_ ?_ ?_ ?_ <;>
          simp [coe_uSL, coe_WSL, Matrix.SpecialLinearGroup.coe_mul, Matrix.mul_apply,
            Fin.sum_univ_two, Matrix.one_apply, e00, e01, e10, e11, h2, h2', hneg]
        done

end CFSG.HardMathSupport.Solomon.Coordinator.YS08.LieQ
