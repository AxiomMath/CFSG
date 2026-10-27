module

public import CFSG.HardMathSupport.Cooperstein.StructureLie.OrthMinusNodeZero
public import CFSG.HardMathSupport.Cooperstein.Coordinator.LieInput.OrthMinus
public import CFSG.HardMathSupport.Cooperstein.StructureLie.OrthMinusNode

public section

namespace CFSG.HardMathSupport.Cooperstein.StructureLie

open CFSG.HardMathSupport.Cooperstein.Coordinator.LieInput CFSG.LieType.Universal.Spin
  CFSG.LieType.Universal.Spin.Twisted CFSG.AGLEmbeddingD2.ParabLevi

theorem ne_zero_of_irr {F : Type} [Field F] [Finite F] [CharP F 2] {b c : F}
    (hirr : ∀ s : F, s ^ 2 + b * s + c ≠ 0) : b ≠ 0 := by
  rintro rfl
  obtain ⟨s, hs⟩ := isSquare_of_charTwo' c
  apply hirr s
  have h2 : (2 : F) = 0 := CharTwo.two_eq_zero
  rw [hs]
  linear_combination (s * s) * h2

theorem orthMinusCentOb_proved : OrthMinusCentOb := by
  intro n f F _ _ _ b c hirr hadm _hcard I hI
  classical
  have hb : b ≠ 0 := ne_zero_of_irr hirr
  have hN : 3 ≤ n - 1 := by
    have := hadm.2.2
    simp only at this
    omega
  obtain ⟨j, hj⟩ : ∃ j : Fin (n - 1), j ∉ I := by
    by_contra h
    push Not at h
    exact hI (Set.eq_univ_of_forall h)
  intro k hk
  have hkr : ∀ u ∈ CFSG.AGLEmbedding.LieOut.radical (minusDatum n hirr) j, k * u = u * k :=
    fun u hu => hk u (radical_le_leviRad hj hu)
  have hmem : k ∈ CFSG.AGLEmbedding.LieOut.radical (minusDatum n hirr) j := by
    by_cases hj0 : j.val = 0
    · exact mem_radical_of_comm_node_zero hirr hb hN j hj0 k hkr
    · exact mem_radical_of_comm_node hirr hb hN j (by omega) k hkr
  exact Subgroup.mem_sup_left (radical_le_leviRad hj hmem)

end CFSG.HardMathSupport.Cooperstein.StructureLie
