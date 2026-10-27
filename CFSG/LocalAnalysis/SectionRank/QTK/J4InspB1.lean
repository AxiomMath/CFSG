module

public import CFSG.LocalAnalysis.SectionRank.QTK.J4InspA6
public import CFSG.LocalAnalysis.ComponentClassification.CatLeafProofLieOrder
public import CFSG.LocalAnalysis.SeitzReduction.CrossCharEven
public import CFSG.LocalAnalysis.SectionRank.QTK.J4InspA4

public section

namespace CFSG.SectionRank.QTK

open CFSG.Open CFSG.Blueprint CFSG.Assembly.LowTwoRank CFSG.ComponentClassification.CatLeaf

theorem two_part_of_l34 {t : StatedLieTag} {n f : ℕ} (hadm : StatedLieAdmissible t n 2 f)
    (hM : 20160 * lieOrderDivisor t n (2 ^ f) = lieOrderNumerator t n (2 ^ f)) :
    lieSylowExponent t n * f = 6 := by
  have hT := CFSG.SeitzReduction.CrossChar.ordProj_two_eq_of_two hadm hM
  rw [show (20160 : ℕ) = 2 ^ 6 * 315 by norm_num,
    CFSG.SeitzReduction.RankOne.LieOdd.ordProj_two_pow_mul_odd (by decide)] at hT
  exact (Nat.pow_right_injective le_rfl hT).symm

theorem sp6TwoOrder_holds :
    Sp6TwoOrder := by
  intro H _ hH
  have hLM : CFSG.Blueprint.LieModel H .PSp 3 2 1 := Or.inl ⟨by decide, hH⟩
  have hM := (CFSG.ComponentClassification.CatLeafProof.lieOrderFormulasInput H .PSp 3 2 1
    hH.1 hLM).2.1
  have hd : lieOrderDivisor .PSp 3 (2 ^ 1) = 1 := by decide
  have hn : lieOrderNumerator .PSp 3 (2 ^ 1) = 1451520 := by decide
  rw [hd, hn, Nat.mul_one] at hM
  exact hM

theorem l34NotLeviFamily_holds :
    L34NotLeviFamily := by
  intro H _ hH hLevi
  have hcard : Nat.card H = 20160 := CFSG.Quasithin.H13.A5.card_of_isPSL34 hH
  unfold Char2LeviPred at hLevi
  rcases hLevi with ⟨a, ha⟩ | ⟨f, hf⟩ | ⟨a, ha⟩
  ·
    have hLM : CFSG.Blueprint.LieModel H .PSL 2 2 a := Or.inl ⟨by decide, ha⟩
    have hM := (CFSG.ComponentClassification.CatLeafProof.lieOrderFormulasInput H .PSL 2 2 a
      ha.1 hLM).2.1
    rw [hcard] at hM
    have hN := two_part_of_l34 ha.1 hM
    have ha6 : a = 6 := by
      norm_num [lieSylowExponent] at hN
      omega
    subst ha6
    revert hM
    decide
  ·
    have hLM : CFSG.Blueprint.LieModel H .twistedB2 0 2 f :=
      Or.inr (Or.inr (Or.inr ⟨rfl, rfl, hf⟩))
    have hadm : StatedLieAdmissible .twistedB2 0 2 f := by
      obtain ⟨-, a, ha1, K, _, _, hfa, -, -⟩ := hf
      show Nat.Prime 2 ∧ 1 ≤ f ∧ (0 = 0 ∧ 2 = 2 ∧ Odd f ∧ 3 ≤ f)
      exact ⟨Nat.prime_two, by omega, rfl, rfl, ⟨a, hfa⟩, by omega⟩
    have hM := (CFSG.ComponentClassification.CatLeafProof.lieOrderFormulasInput H .twistedB2 0 2 f
      hadm hLM).2.1
    rw [hcard] at hM
    have hN := two_part_of_l34 hadm hM
    have hf3 : f = 3 := by
      norm_num [lieSylowExponent] at hN
      omega
    subst hf3
    revert hM
    decide
  ·
    have hLM : CFSG.Blueprint.LieModel H .PSU 3 2 a := Or.inl ⟨by decide, ha⟩
    have hM := (CFSG.ComponentClassification.CatLeafProof.lieOrderFormulasInput H .PSU 3 2 a
      ha.1 hLM).2.1
    rw [hcard] at hM
    have hN := two_part_of_l34 ha.1 hM
    have ha2 : a = 2 := by
      norm_num [lieSylowExponent] at hN
      omega
    subst ha2
    revert hM
    decide

end CFSG.SectionRank.QTK
