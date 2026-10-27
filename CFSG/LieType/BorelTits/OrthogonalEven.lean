module

public import CFSG.LieType.BorelTits.OrthogonalSingular

public section

namespace CFSG.LieType.BorelTits

open Matrix CFSG.Assembly.LowTwoRank

theorem holds_statedOmega_of_five_le_card {ι : Type} [Fintype ι] [DecidableEq ι] {K : Type}
    [Field K] [Finite K] (p : ℕ) [Fact p.Prime] [CharP K p] (Φ : QuadForm K (ι → K))
    (hι : 5 ≤ Fintype.card ι) : Holds (StatedOmega Φ.Q) p := by
  refine holds_of_quadForm_singular Φ p (by rw [Module.finrank_fintype_fun_eq_card]; omega)
    (fun h v => ?_) (natRep_injective _) (fun x y hx hxy => ?_) fun h Z hZ a ha hQa => ?_
  · rw [natRep_apply]
    exact orthGroup_preserves Φ.Q (statedOmega_le_orthGroup Φ.Q h.2) v
  · obtain ⟨A, hA, hAv⟩ := exists_mem_statedOmega_eichler' Φ hι hx hxy
    exact ⟨⟨A, hA⟩, fun v => by rw [natRep_apply]; exact hAv v⟩
  · simp only [natRep_apply]
    exact not_reflection_on_quotient_of_mem_statedOmega Φ h.2 hZ ha hQa

variable (n : ℕ) (K : Type) [Field K] [Finite K]

section AnyCharacteristic

variable (p : ℕ) [Fact p.Prime] [CharP K p]

theorem holds_statedOmega_quadPlus_of_three_le (hn : 3 ≤ n) :
    Holds (StatedOmega (StatedQuadPlus n K)) p := by
  have hι : 5 ≤ Fintype.card (Fin n ⊕ Fin n) := by
    simp only [Fintype.card_sum, Fintype.card_fin]
    omega
  exact holds_statedOmega_of_five_le_card p (quadPlusForm n K) hι

theorem holds_statedOmega_quadMinus_of_three_le (hn : 3 ≤ n) (b c : K)
    (hirr : ∀ s : K, s ^ 2 + b * s + c ≠ 0) :
    Holds (StatedOmega (StatedQuadMinus n K b c)) p := by
  have hι : 5 ≤ Fintype.card (Fin (n - 1) ⊕ Fin (n - 1) ⊕ Fin 2) := by
    simp only [Fintype.card_sum, Fintype.card_fin]
    omega
  exact holds_statedOmega_of_five_le_card p (quadMinusForm n K b c hirr) hι

theorem holds_statedProj_statedOmega_quadPlus_of_three_le (hn : 3 ≤ n) :
    Holds (StatedProj (StatedOmega (StatedQuadPlus n K))) p :=
  Holds.statedProj _ (holds_statedOmega_quadPlus_of_three_le n K p hn)

theorem holds_statedProj_statedOmega_quadMinus_of_three_le (hn : 3 ≤ n) (b c : K)
    (hirr : ∀ s : K, s ^ 2 + b * s + c ≠ 0) :
    Holds (StatedProj (StatedOmega (StatedQuadMinus n K b c))) p :=
  Holds.statedProj _ (holds_statedOmega_quadMinus_of_three_le n K p hn b c hirr)

end AnyCharacteristic

variable [CharP K 2]

theorem holds_statedOmega_quadPlus_two (hn : 3 ≤ n) :
    Holds (StatedOmega (StatedQuadPlus n K)) 2 :=
  holds_statedOmega_quadPlus_of_three_le n K 2 hn

theorem holds_statedOmega_quadMinus_two (hn : 3 ≤ n) (b c : K)
    (hirr : ∀ s : K, s ^ 2 + b * s + c ≠ 0) :
    Holds (StatedOmega (StatedQuadMinus n K b c)) 2 :=
  holds_statedOmega_quadMinus_of_three_le n K 2 hn b c hirr

theorem holds_statedProj_statedOmega_quadPlus_two (hn : 3 ≤ n) :
    Holds (StatedProj (StatedOmega (StatedQuadPlus n K))) 2 :=
  holds_statedProj_statedOmega_quadPlus_of_three_le n K 2 hn

theorem holds_statedProj_statedOmega_quadMinus_two (hn : 3 ≤ n) (b c : K)
    (hirr : ∀ s : K, s ^ 2 + b * s + c ≠ 0) :
    Holds (StatedProj (StatedOmega (StatedQuadMinus n K b c))) 2 :=
  holds_statedProj_statedOmega_quadMinus_of_three_le n K 2 hn b c hirr

end CFSG.LieType.BorelTits
