module

public import CFSG.LocalAnalysis.ComponentClassification.GrSLitL34Sec4End43N
public import CFSG.LocalAnalysis.ComponentClassification.GrSLitL34Sec4End43H2
public import CFSG.LocalAnalysis.ComponentClassification.GrSLitHeldFixHeFacts
public import CFSG.LocalAnalysis.ComponentClassification.GrSLitL34Sec4Single
public import CFSG.LocalAnalysis.ComponentClassification.GrSLitL34Sec5Rank
public import CFSG.LocalAnalysis.ComponentClassification.GrSLitL34Sec5Normal
public import CFSG.LocalAnalysis.ComponentClassification.Sol78PSp4
public import Certificates.Kernel.ThCent.Leaves
public import CFSG.LocalAnalysis.ComponentClassification.GrSLitL34Sec4InputsEnd43N

public section

namespace CFSG.ComponentClassification.GrSLit

open CFSG Subgroup CFSG.ComponentClassification.UnbalancedLayer
  CFSG.ComponentClassification.UnbalancedCorr

theorem l34Lemma43HeldAutStep_of_inputs
    (hNorm : L34Lemma43HeldNormalStep) (hMax : MaximalTwoComponentInput) :
    L34Lemma43HeldAutStep := by
  intro G _ _ a x J S A hset hcent hrun h3 W hW hWodd hWB hNJ K hKM hKc he hJK
  have hKN := hNorm G a x J S A hset hcent hrun h3 W hW hWodd hWB hNJ K hKM hKc he hJK
  refine ⟨hKN, fun hxK => ?_⟩
  obtain ⟨e⟩ := he
  obtain ⟨hbase, hU3, hL34, hmax, hS, -, hxS⟩ := id hset
  obtain ⟨hsimple, hnab, hK, -, hUo, -, -, -⟩ := hbase
  obtain ⟨ha2, hx2, -, hJa, hJc, hclx, hcld⟩ := hU3
  have hgs : GSMaximalSetting G a J := ⟨hsimple, hnab, hK, hUo, ha2, hJa, hJc,
    hmax, GrS5.three_le_pRank_of_l34 hL34, Sol78.not_psp4_of_l34 hL34, Or.inl ⟨hL34, hset.1⟩⟩
  set M : Subgroup G := normalizer (W : Set G) with hM
  have hCa : centralizer ({a} : Set G) ≤ M :=
    (GrS4.centralizer_le_normalizer_of_gsMaximalSetting hMax hgs).trans hNJ
  have hxM : x ∈ M := hNJ (hS.1 hxS)
  have hxN : x ∈ normalizer (K : Set G) := hKN hxM
  have hxx : x * x = 1 := by rw [← pow_two, ← hx2, pow_orderOf_eq_one]
  have hJodd : ¬ J ≤ oddIn M := by
    intro hJO
    obtain ⟨F, hFJ, hF, hF8⟩ :=
      exists_isElemTwo_of_three_le_pRank (GrS5.three_le_pRank_of_l34 hL34)
    have hodd : Odd (Nat.card F) :=
      (odd_card_map_pPrimeCore M).of_dvd_nat (card_dvd_of_le (hFJ.trans hJO))
    have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
    obtain ⟨k, hk⟩ := hF.isPGroup.exists_card_eq
    rw [hk] at hodd hF8
    have hk0 : k ≠ 0 := by
      rintro rfl
      norm_num at hF8
    exact (Nat.not_even_iff_odd.mpr hodd) ((Nat.even_pow' hk0).mpr even_two)
  apply hJodd
  by_cases hx1 : x ∈ coreActionKernel K
  · refine hclx.symm.le.trans ((closure_le _).mpr ?_)
    rintro _ ⟨j, hj, rfl⟩
    exact GrS4.commutator_mem_oddIn hKM hKc hxM hx1 (hJK hj)
  · refine hcld.symm.le.trans ((closure_le _).mpr ?_)
    rintro _ ⟨j, hj, d, hd, rfl⟩
    have hdM : d ∈ M := hCa (mem_inf.mp hd).2
    have hdK := GrS4.mem_coreActionKernel_of_oddCore e hxN hxx hxK hx1 (mem_inf.mp hd).1
      (hKN hdM)
    exact GrS4.commutator_mem_oddIn hKM hKc hdM hdK (hJK hj)

end CFSG.ComponentClassification.GrSLit
