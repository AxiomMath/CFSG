module

public import CFSG.ClassicalInvolution.SmallOrth.Orth3Main
public import CFSG.ClassicalInvolution.Q3.ModelClassicalMemberExact

public section

namespace CFSG.ClassicalInvolution.Q3

open QuadraticMap CFSG.ClassicalGroups.Orthogonal CFSG.ClassicalGroups.Orthogonal.Small
  CFSG.LieType.Universal CFSG.LieType.Universal.Spin CFSG.ClassicalInvolution.Generic
  CFSG.ClassicalInvolution.Balance CFSG.Assembly.LowTwoRank

section Dimensions

variable (F : Type) [Field F]

theorem finrank_quadPlusSpace (n : ℕ) : Module.finrank F (Fin n ⊕ Fin n → F) = 2 * n := by
  rw [Module.finrank_fintype_fun_eq_card, Fintype.card_sum, Fintype.card_fin]
  ring

theorem finrank_quadOddSpace (n : ℕ) :
    Module.finrank F (Fin n ⊕ Fin n ⊕ Unit → F) = 2 * n + 1 := by
  rw [Module.finrank_fintype_fun_eq_card, Fintype.card_sum, Fintype.card_sum, Fintype.card_fin,
    Fintype.card_unit]
  ring

theorem finrank_quadMinusSpace (n : ℕ) :
    Module.finrank F (Fin (n - 1) ⊕ Fin (n - 1) ⊕ Fin 2 → F) = 2 * (n - 1) + 2 := by
  rw [Module.finrank_fintype_fun_eq_card, Fintype.card_sum, Fintype.card_sum, Fintype.card_fin,
    Fintype.card_fin]
  ring

end Dimensions

section Tags

private theorem card_galoisField_three (hp : Nat.Prime 3) : Nat.card (GaloisField 3 1) = 3 := by
  have : Fact (Nat.Prime 3) := ⟨hp⟩
  simpa using GaloisField.card 3 1 one_ne_zero

private theorem nonempty_mulEquiv_of_eq {M : LieUniversal} {G : Type} [Group G]
    {D : UniversalRootDatum G} (hM : M = ⟨G, D⟩) : Nonempty (M.K ≃* G) := by
  subst hM
  exact ⟨MulEquiv.refl G⟩

theorem simpleOddCentralizerFreeTag_POmegaPlus : SimpleOddCentralizerFreeTag .POmegaPlus := by
  intro n hp hadm s hs
  have hn : 4 ≤ n := hadm.2.2
  have hF := card_galoisField_three hp
  have : Fact (Nat.Prime 3) := ⟨hp⟩
  have hM : modelUniv .POmegaPlus n 3 1 hp = ⟨spinGroup (Spin.quadPlus n (GaloisField 3 1)),
      Spin.plusDatum n (GaloisField 3 1) (by omega)⟩ := by
    simp only [modelUniv, lieUniversal, show 3 ≤ n by omega, ↓reduceDIte]
  obtain ⟨eK⟩ := nonempty_mulEquiv_of_eq hM
  have hdim : 6 ≤ Module.finrank (GaloisField 3 1) (Fin n ⊕ Fin n → GaloisField 3 1) := by
    rw [finrank_quadPlusSpace]
    omega
  have hQ := nondegenerate_polarBilin_quadPlus n (GaloisField 3 1)
  exact involutionOddCore_eq_bot_of_mulEquiv hF hQ hdim
    (commutator_orthogonalGroup_quadPlus (by omega)).le
    ((QuotientGroup.congr _ _ eK (Subgroup.map_center_eq eK)).trans
      (((spinQuotientCenterEquivQuadPlus (K := GaloisField 3 1) (n := n) (by omega)).trans
        (statedProjEquiv (coe_quadPlus n (GaloisField 3 1))
          (commutator_orthogonalGroup_quadPlus (by omega)))).trans
        (projElementaryEquivCenter hF hQ (by omega)))) s hs

theorem simpleOddCentralizerFreeTag_POmegaOdd : SimpleOddCentralizerFreeTag .POmegaOdd := by
  intro n hp hadm s hs
  have hn : 3 ≤ n := hadm.2.2.1
  have hF := card_galoisField_three hp
  have : Fact (Nat.Prime 3) := ⟨hp⟩
  have h2 : (2 : GaloisField 3 1) ≠ 0 := (three_eq_zero_two_ne_zero_of_card_eq_three hF).2
  have hM : modelUniv .POmegaOdd n 3 1 hp = ⟨spinGroup (Spin.quadOdd n (GaloisField 3 1)),
      Spin.oddDatum n (GaloisField 3 1)⟩ := by
    simp only [modelUniv, lieUniversal]
  obtain ⟨eK⟩ := nonempty_mulEquiv_of_eq hM
  have hdim : 6 ≤ Module.finrank (GaloisField 3 1) (Fin n ⊕ Fin n ⊕ Unit → GaloisField 3 1) := by
    rw [finrank_quadOddSpace]
    omega
  have hQ := nondegenerate_polarBilin_quadOdd n (GaloisField 3 1) h2
  exact involutionOddCore_eq_bot_of_mulEquiv hF hQ hdim
    (commutator_orthogonalGroup_quadOdd h2 hn).le
    ((QuotientGroup.congr _ _ eK (Subgroup.map_center_eq eK)).trans
      (((spinQuotientCenterEquivQuadOdd (K := GaloisField 3 1) (n := n) h2 hn).trans
        (statedProjEquiv (coe_quadOdd n (GaloisField 3 1))
          (commutator_orthogonalGroup_quadOdd h2 hn))).trans
        (projElementaryEquivCenter hF hQ (by omega)))) s hs

theorem simpleOddCentralizerFreeTag_POmegaMinus : SimpleOddCentralizerFreeTag .POmegaMinus := by
  intro n hp hadm s hs
  have hn : 4 ≤ n := hadm.2.2
  have hF := card_galoisField_three hp
  have : Fact (Nat.Prime 3) := ⟨hp⟩
  have hirr := minusCoeffs_irr 3 1
  have hM : modelUniv .POmegaMinus n 3 1 hp = ⟨spinGroup (Spin.quadMinus n (GaloisField 3 1)
      (minusCoeffs 3 1).1 (minusCoeffs 3 1).2), Spin.Twisted.minusDatum n hirr⟩ := by
    simp only [modelUniv, lieUniversal]
  obtain ⟨eK⟩ := nonempty_mulEquiv_of_eq hM
  have hdim : 6 ≤ Module.finrank (GaloisField 3 1)
      (Fin (n - 1) ⊕ Fin (n - 1) ⊕ Fin 2 → GaloisField 3 1) := by
    rw [finrank_quadMinusSpace]
    omega
  have hQ := nondegenerate_polarBilin_quadMinus_of_finite n (GaloisField 3 1) hirr
  exact involutionOddCore_eq_bot_of_mulEquiv hF hQ hdim
    (commutator_orthogonalGroup_quadMinus hn hirr).le
    ((QuotientGroup.congr _ _ eK (Subgroup.map_center_eq eK)).trans
      (((spinQuotientCenterEquivQuadMinus (K := GaloisField 3 1) hn hirr).trans
        (statedProjEquiv (coe_quadMinus n (GaloisField 3 1) (minusCoeffs 3 1).1
          (minusCoeffs 3 1).2) (commutator_orthogonalGroup_quadMinus hn hirr))).trans
        (projElementaryEquivCenter hF hQ (by omega)))) s hs

theorem oddCentralizerFreeTag_POmegaOdd : OddCentralizerFreeTag .POmegaOdd :=
  oddCentralizerFreeTag_of_simple _ simpleOddCentralizerFreeTag_POmegaOdd

theorem oddCentralizerFreeTag_POmegaPlus : OddCentralizerFreeTag .POmegaPlus :=
  oddCentralizerFreeTag_of_simple _ simpleOddCentralizerFreeTag_POmegaPlus

theorem oddCentralizerFreeTag_POmegaMinus : OddCentralizerFreeTag .POmegaMinus :=
  oddCentralizerFreeTag_of_simple _ simpleOddCentralizerFreeTag_POmegaMinus

end Tags

end CFSG.ClassicalInvolution.Q3
