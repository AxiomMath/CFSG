module

public import CFSG.LocalAnalysis.AGLEmbedding.KFactProofs.AlphaSound
public import CFSG.LocalAnalysis.AGLEmbedding.KFactProofs.AlphaOf
public import CFSG.RankThree.PartOne.CTP.SporadicNoncomm
public import CFSG.Sporadic.ON
public import CFSG.Sporadic.Schreier.SteinbergBIONOuterTwo
public import Certificates.Certificate9590
public import CFSG.LocalAnalysis.AGLEmbedding.KFactProofs.RankThreeDefs

public section

namespace CFSG.AGLEmbedding

open CFSG.ComponentClassification.OuterAutomorphisms CFSG.RankThree.PartOne.StrongP
  CFSG.RankThree.PartOne.CTP CFSG.SectionRank CFSG.SectionRank.Native CFSG.Blueprint
  CFSG.AGLEmbedding.R3 CFSG.AGLEmbedding.R3.AlphaON

theorem qMat_det_unit_ON : IsUnit (qMat 3 4 onQ).det := by
  have h : (qMat 3 4 onQ).det = 1 := by
    have e : qMat 3 4 onQ = !![0, 1, 0, 2; 2, 0, 1, 1; 0, 2, 0, 2; 1, 2, 1, 0] := by
      ext i j
      fin_cases i <;> fin_cases j <;> rfl
    rw [e]
    simp [Matrix.det_succ_row_zero, Fin.sum_univ_succ]
    decide
  rw [h]
  exact isUnit_one

theorem abelianSylowDatum_ON_three :
    AbelianSylowDatum NativeSporadic.ON 3 := by
  refine abelianSylowDatum_of_absCheck (spec3 154) Nat.prime_three
    Certificates.certificate9590 qMat_det_unit_ON ?_
  rw [CFSG.Sporadic.ON.card_ON]
  show ¬ 3 ^ 5 ∣ 460815505920
  norm_num

theorem sporadicAlphaData_ONan :
    SporadicAlphaData (NativeSporadic.Carrier .ONan) := by
  have hOut : Nat.card (Outer (NativeSporadic.Carrier .ONan)) ≤ 2 :=
    Nat.le_of_dvd (by norm_num) (CFSG.Sporadic.SteinbergBI.cti_on_outer_order_divides_two
    ⟨MulEquiv.refl _⟩)
  refine sporadicAlphaData_of_card CFSG.Sporadic.ON.card_ON (by norm_num) hOut ?_
  have hpf : Nat.primeFactors 460815505920 = {2, 3, 5, 7, 11, 19, 31} := by
    norm_num [Nat.primeFactors]
  rw [hpf]
  simp only [Finset.mem_insert, Finset.mem_singleton, forall_eq_or_imp, forall_eq]
  exact ⟨fun h => absurd rfl h,
    fun _ => Or.inr (Or.inr (Or.inr (Or.inl abelianSylowDatum_ON_three))),
    fun _ => Or.inl (by norm_num), fun _ => Or.inr (Or.inl ⟨by norm_num, hasNoncommPair_ON⟩),
    fun _ => Or.inl (by norm_num), fun _ => Or.inl (by norm_num), fun _ => Or.inl (by norm_num)⟩

end CFSG.AGLEmbedding
