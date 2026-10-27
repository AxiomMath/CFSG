module

public import CFSG.LocalAnalysis.GLTheoremA.CatA.T158MShNormDefs
public import CFSG.LocalAnalysis.GLTheoremA.CatA.I112Types
public import CFSG.LocalAnalysis.GLTheoremA.CatA.T1428Trans

public section

namespace CFSG.LocalAnalysis.GLTheoremA.T158

open CFSG.Open CFSG.Yardstones.Md0ec50421ce4 CFSG.LocalAnalysis.GLTheoremB
open CFSG.LocalAnalysis.GLTheoremA CFSG.LocalAnalysis.GLTheoremA.S10
open CFSG.HardMathSupport.Timmesfeld.ComponentBalance CFSG.HardMathSupport.Solomon.Coordinator
open CFSG.HardMathSupport.Solomon.LocalBalance

theorem t158Norm_of_tables (T : Tables112) (TL : TableL2) (TT : Tables112Types)
    (hC : T158NormCat) (hL : T158NormL3) : T158Norm := by
  intro X _ _ p K B x₁ x₂ L₁ L₂ hcat hH hInn
  by_contra hB
  obtain ⟨⟨hKG, hKcomp, hBel, -, hrank, -, -, -, -, -, -, -, -⟩, -, -⟩ := hH.hyp
  have hp : p.Prime := hH.prime
  have hp2 : p ≠ 2 := hH.odd
  haveI : Fact p.Prime := ⟨hp⟩
  let B' : Subgroup ↥(⊤ : Subgroup X) := B.subgroupOf ⊤
  let K' : Subgroup ↥(⊤ : Subgroup X) := K.subgroupOf ⊤
  have hBpg : IsPGroup p B := hBel.isPGroup
  obtain ⟨k, hk⟩ := hBpg.exists_card_eq
  have hBcard : Nat.card ↥B' = Nat.card ↥B :=
    Nat.card_congr (Subgroup.subgroupOfEquivOfLe le_top).toEquiv
  have hk' : Nat.card ↥B' = p ^ k := by rw [hBcard, hk]
  have hB' : IsElemAbelian p B' :=
    CFSG.LocalAnalysis.GLTheoremB.isElemAbelian_subgroupOf hBel ⊤
  have hk_le : k ≤ CFSG.Open.pRank p B' :=
    CFSG.SectionRank.le_pRank hp.one_lt le_rfl hB' hk'
  have hr : GLATwoLocalRank p (↥(⊤ : Subgroup X)) ≤ CFSG.Open.pRank p B' := by
    have h1 : p ^ GLATwoLocalRank p (↥(⊤ : Subgroup X)) ≤ p ^ k := by
      rw [← hk', hBcard]
      exact hrank
    exact ((Nat.pow_le_pow_iff_right hp.one_lt).1 h1).trans hk_le
  have hK' : GLAPComponent p (⊤ : Subgroup ↥(⊤ : Subgroup X)) K' :=
    glaPComponent_top hKcomp
  have hnL' : ¬ B' ≤ Subgroup.normalizer (K' : Set ↥(⊤ : Subgroup X)) := by
    intro hle
    apply hB
    intro b hb
    exact (T1428.mem_normalizer_subgroupOf_iff (X := ⊤) (K := K) le_top
      (Subgroup.mem_top b)).1 (hle (Subgroup.mem_subgroupOf.2 hb))
  obtain ⟨hp3, -, htypes⟩ :=
    i112_types_of_isKGroup T TL TT hp hp2 hKG hB' hr hK' hnL'
  subst p
  obtain ⟨eP⟩ := nonempty_pQuot_equiv_subgroupOf 3 (H := ⊤) (K := K) le_top
  have htypes' : IsLTwoOddPow (PQuot 3 K) ∨
      IsHatSix (PQuot 3 K) ∨ IsHatSeven (PQuot 3 K) ∨
      IsHatMTwentyTwo (PQuot 3 K) ∨ IsSLThreeExc (PQuot 3 K) ∨ IsSUThreeExc (PQuot 3 K) := by
    rcases htypes with h | h | h | h | h | h
    · exact Or.inl (i112f_isLTwoOddPow_of_mulEquiv eP h)
    · exact Or.inr (Or.inl (i112f_isHatSix_of_mulEquiv eP h))
    · exact Or.inr (Or.inr (Or.inl (i112f_isHatSeven_of_mulEquiv eP h)))
    · exact Or.inr (Or.inr (Or.inr (Or.inl (i112f_isHatMTwentyTwo_of_mulEquiv eP h))))
    · exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inl
        (i112f_isSLThreeExc_of_mulEquiv eP h)))))
    · exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inr
        (i112f_isSUThreeExc_of_mulEquiv eP h)))))
  have hq : CFSG.Open.IsQuasisimple (PQuot 3 K) :=
    isQuasisimple_pQuot_of_glaPComponent Nat.prime_three hKcomp
  exact hL X K B x₁ x₂ L₁ L₂ hH hInn (hC (PQuot 3 K) hq htypes' hcat)

end CFSG.LocalAnalysis.GLTheoremA.T158

end
