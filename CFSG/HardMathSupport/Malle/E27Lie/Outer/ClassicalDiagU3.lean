module

public import CFSG.HardMathSupport.Malle.E27Lie.Outer.ClassicalDiagU3Cube
public import CFSG.HardMathSupport.Malle.E27Lie.Outer.ClassicalDiagU3Torsion

public section

open Polynomial Module Matrix CFSG.RankThree.PartOne.KCPrimary CFSG.RankThree.PartOne.KCUnitary
  CFSG.RankThree.PartOne.KCUnitaryModel CFSG.RankThree.PartOne.FOC CFSG.RankThree.PartOne
  CFSG.LocalAnalysis.ComponentInitial CFSG.LocalAnalysis.ComponentInitial.UnitaryHigher
  CFSG.ClassicalGroups.UnitaryFlag CFSG.HardMathSupport.Curtis.Coordinator CFSG.Open

namespace CFSG.HardMathSupport.Malle.E27Lie

theorem unitary_three_diag_false {ℓ f : ℕ} {F : Type} [Field F] [Finite F]
    (h : UnitaryFieldData ℓ f F) (hℓ3 : ℓ ≠ 3) (hq : 4 ≤ ℓ ^ f) (hg : 3 ∣ ℓ ^ f + 1)
    (y : primeFormUnitary h (idGram F 3)) (c : Fˣ)
    (hyc : (y : GL (Fin 3) F) ^ 3 = GeneralLinearGroup.scalar (Fin 3) c)
    (hout : ∀ k, primeFormConjHom h (idGram F 3) y ≠ MulAut.conj k)
    (ha : ∀ D : Subgroup (primeFormP h (idGram F 3)),
      (∀ x ∈ D, primeFormConjHom h (idGram F 3) y x = x) → ⁅D, D⁆ = D → ¬ 3 ∣ Nat.card D)
    (hT : ∃ T : Subgroup (primeFormP h (idGram F 3)),
      (∀ x ∈ T, primeFormConjHom h (idGram F 3) y x = x) ∧ IsElemAbelian 3 T ∧
        Nat.card T = 9) : False := by
  rcases unitary_three_block_or_det hℓ3 hq y c hyc with ⟨R, hR1, hR2, hR3⟩ | hdet
  · exact ha R (fun x hx => (mem_autFix _ _).1 (hR1 hx)) hR2 hR3
  · by_cases hcube : ∃ b : F, b ^ 3 = c
    · obtain ⟨b, hb⟩ := hcube
      obtain ⟨k, hk⟩ := primeFormConjHom_inner_of_cube hg y c hdet b hb
      exact hout k hk
    · push Not at hcube
      obtain ⟨T, hTfix, hTe, hT9⟩ := hT
      have := card_le_three_of_fixed_exponent_three_U hg y c hyc hcube T hTfix hTe.2
      omega

end CFSG.HardMathSupport.Malle.E27Lie
