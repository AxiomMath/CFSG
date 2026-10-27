module

public import CFSG.LocalAnalysis.ComponentClassification.CatLeafProofLieOrderArith
public import CFSG.Timmesfeld.Orders.Classical
public import CFSG.RankThree.PartOne.KC.OrthogonalSubfieldFixed

public section

namespace CFSG.LocalAnalysis.RankFourTheoremC.PEmpty

namespace KFAE

open CFSG.Assembly.LowTwoRank (StatedLieTag StatedLieAdmissible StatedClassicalModel)
open CFSG.ComponentClassification.CatLeaf (lieOrderNumerator lieOrderDivisor)
open CFSG.ComponentClassification.CatalogueBOrthogonalSemilinear
open CFSG.RankThree.PartOne.KCOrthogonalSubfield

theorem card_mul_lieOrderDivisor_of_orthogonalModel {X : Type} [Group X] {t : StatedLieTag}
    {n p f : ℕ} (ht : t = .POmegaOdd ∨ t = .POmegaPlus ∨ t = .POmegaMinus)
    (hadm : StatedLieAdmissible t n p f) (h : StatedClassicalModel X t n p f) :
    Nat.card X * lieOrderDivisor t n (p ^ f) = lieOrderNumerator t n (p ^ f) := by
  have hp : p.Prime := hadm.1
  have hdvd := CFSG.ComponentClassification.CatLeafProof.lieOrderDivisor_dvd_numerator hadm
  have hc : Nat.card X = lieOrderNumerator t n (p ^ f) / lieOrderDivisor t n (p ^ f) := by
    rcases ht with rfl | rfl | rfl
    · obtain ⟨-, -, hn, hp2⟩ := hadm
      have hc := (CFSG.ClassicalInvolution.card_statedClassicalModel_of_ne_two hp2 h).2.2.2.1 rfl
      have hodd : Odd (p ^ f) := (hp.eq_two_or_odd'.resolve_left hp2).pow
      rw [hc, CFSG.Open.ordBC, CFSG.ClassicalInvolution.gcd_two_sub_one_of_odd hodd, ← sq]
      rfl
    · obtain ⟨-, -, hn⟩ := hadm
      have hc : Nat.card X = CFSG.Open.ordD n (p ^ f) := by
        by_cases hp2 : p = 2
        · subst hp2
          exact (CFSG.Timmesfeld.card_statedClassicalModel_two h).2.2.2.1 rfl
        · exact (CFSG.ClassicalInvolution.card_statedClassicalModel_of_ne_two hp2 h).2.2.2.2.1
            rfl
      rw [hc, CFSG.Open.ordD]
      rfl
    · obtain ⟨-, -, hn⟩ := hadm
      have hc : Nat.card X = CFSG.Open.ordTwistedD n (p ^ f) := by
        by_cases hp2 : p = 2
        · subst hp2
          exact (CFSG.Timmesfeld.card_statedClassicalModel_two h).2.2.2.2 rfl
        · exact (CFSG.ClassicalInvolution.card_statedClassicalModel_of_ne_two hp2 h).2.2.2.2.2
            rfl
      rw [hc, CFSG.Open.ordTwistedD]
      rfl
  rw [hc]
  exact Nat.div_mul_cancel hdvd

theorem card_matrixProjectiveDerived_dvd_subfieldFixedGroup {K : Type} [Field K] (k : Subfield K)
    {d : ℕ} {Q₀ : QuadraticForm k (Fin d → k)} {Q : QuadraticForm K (Fin d → K)}
    (hext : IsExtension k Q₀ Q) (hd : 0 < d) :
    Nat.card (matrixProjectiveDerived Q₀) ∣ Nat.card (subfieldFixedGroup k Q₀ Q) := by
  have h1 := Subgroup.card_dvd_of_le (subfieldDerivedImage_le k hext)
  rwa [← Nat.card_congr (inclEquiv k hext hd).toEquiv] at h1

end KFAE

end CFSG.LocalAnalysis.RankFourTheoremC.PEmpty
