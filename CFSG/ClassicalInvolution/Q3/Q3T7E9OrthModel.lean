module

public import CFSG.ClassicalInvolution.Q3.Q3T7E9OrthCore
public import CFSG.ClassicalInvolution.Q3.Q3T7E9Dim4
public import CFSG.ClassicalInvolution.Asc77.AscE189Orth
public import CFSG.ClassicalInvolution.Asc77.AscE189D4Model
public import CFSG.ClassicalInvolution.RouteD.ExoticTwinProofOrthBridge
public import CFSG.ClassicalInvolution.RouteD.GapsOrthSpin
public import CFSG.ClassicalInvolution.Asc77.AscR10E5
public import CFSG.ClassicalInvolution.Balance.LayerGenerationInner
public import CFSG.ClassicalInvolution.Balance.LayerGenerationTriple
public import CFSG.ClassicalInvolution.ModelFacts.ClassicalIsFundamentalE6
public import CFSG.ClassicalInvolution.ModelFacts.ClassicalIsFundamentalE7
public import CFSG.ClassicalInvolution.ModelFacts.PairFrameExcF4Main
public import CFSG.ClassicalInvolution.ModelFacts.StandardPairDichotomyExcA2UnitaryCocycleGen
public import CFSG.ClassicalInvolution.ModelFacts.StandardPairDichotomyExcA2UnitaryHom
public import CFSG.LocalAnalysis.ComponentClassification.BadTwoComponentSubgroup

public section

set_option linter.unusedSectionVars false

namespace CFSG.ClassicalInvolution.Q3.Q3T7E9

open CFSG.ClassicalInvolution.Models.OrthogonalPairs CFSG.ClassicalGroups.Orthogonal QuadraticMap
open CFSG.ClassicalInvolution.Generic CFSG.Assembly.LowTwoRank CFSG.LieType.Universal
open CFSG.LieType.Universal.Spin
open CFSG.ClassicalInvolution.RouteD CFSG.ClassicalInvolution.RouteD.Exotic
open CFSG.ClassicalInvolution.Asc77
open CFSG.ClassicalInvolution.ModelFacts (Gen3 gen3_of_equiv_sl2
  nonempty_equiv_sl2_of_mem_fundamentalSubgroups)
open CFSG.ClassicalInvolution.Models.Transfer
open CFSG.ClassicalInvolution.RouteD.Gaps (fundSet)
open scoped MatrixGroups


section Gen

theorem gen3_of_mem_fundamentalSubgroups_three {t : StatedLieTag} {n : ℕ} (hfund : IsFundTag t)
    (hadm : StatedLieAdmissible t n 3 1) (hG2 : t ≠ .G2) (hD4 : t ≠ .trialityD4)
    {R : Subgroup (modelUniv t n 3 1 Fact.out).K}
    (hR : R ∈ fundamentalSubgroups t (modelUniv t n 3 1 Fact.out).D) : Gen3 R := by
  obtain ⟨φ⟩ := nonempty_equiv_sl2_of_mem_fundamentalSubgroups (by norm_num) hfund hadm hG2 hD4 hR
  exact gen3_of_equiv_sl2 φ

end Gen

section Odd

variable {p f : ℕ} [Fact p.Prime]

theorem fundCorr_odd_of_odd (hp2 : p ≠ 2) (hf : 1 ≤ f) {n : ℕ}
    (hadm : StatedLieAdmissible .POmegaOdd n p f) :
    (∀ R ∈ fundamentalSubgroups .POmegaOdd (oddDatum n (GaloisField p f)),
        R.map (spinAction (quadOdd n (GaloisField p f))) ∈
          fundSet (quadOdd n (GaloisField p f))) ∧
      ∀ L ∈ fundSet (quadOdd n (GaloisField p f)),
        ∃ R ∈ fundamentalSubgroups .POmegaOdd (oddDatum n (GaloisField p f)),
          R.map (spinAction (quadOdd n (GaloisField p f))) = L := by
  have hn3 : 3 ≤ n := hadm.2.2.1
  have hodd := odd_card_galoisField_of_ne_two (p := p) hp2 hf
  have hlong := ModelFacts.isLongestRoot_single .POmegaOdd n p f Fact.out trivial hadm
  have hsc := ModelFacts.fundamentalSingleClass .POmegaOdd n p f Fact.out trivial hadm
    (by decide) (by decide)
  have hk : (0 : ℕ) + 1 < n := by omega
  set k₀ : Fin n := ⟨0, by omega⟩ with hk₀
  set j₀ : Fin n := ⟨0 + 1, hk⟩ with hj₀
  have hij : k₀ ≠ j₀ := Fin.ne_of_val_ne (by simp [hk₀, hj₀])
  have hR : CFSG.LieType.CurtisTits.rankOne (oddRootGroup n (GaloisField p f)) k₀ =
      ((oddFrame n (GaloisField p f)).toHypFrame.longSL2 hij true false).range := by
    have h1 : CFSG.LieType.CurtisTits.rankOne (oddRootGroup n (GaloisField p f)) k₀ =
        (rankOneB (GaloisField p f) k₀).range :=
      le_antisymm (OddCT.rankOne_le_range k₀) (by
        rintro _ ⟨M, rfl⟩
        exact OddCT.rankOneB_mem_rankOne k₀ M)
    rw [h1, rankOneB_of_lt (GaloisField p f) hk rfl hij]
  have hR₀ : CFSG.LieType.CurtisTits.rankOne (oddRootGroup n (GaloisField p f)) k₀ ∈
      fundamentalSubgroups .POmegaOdd (oddDatum n (GaloisField p f)) :=
    ⟨1, Pi.single k₀ 1, Or.inl (hlong k₀ (by show 0 + 1 < n; omega)), by
      rw [conjSub_one]; rfl⟩
  have hdim : Module.finrank (GaloisField p f) (Fin n ⊕ Fin n ⊕ Unit → GaloisField p f) =
      2 * n + 1 := by
    rw [Module.finrank_fintype_fun_eq_card, Fintype.card_sum, Fintype.card_sum, Fintype.card_fin,
      Fintype.card_unit]
    ring
  have hperp : 2 ≤ Module.finrank (GaloisField p f)
      ((oddFrame n (GaloisField p f)).toHypFrame.toFrame hij true false).perp := by
    have := ModelFacts.finrank_perp_add_four
      ((oddFrame n (GaloisField p f)).toHypFrame.toFrame hij true false)
    omega
  have himg : (CFSG.LieType.CurtisTits.rankOne (oddRootGroup n (GaloisField p f)) k₀).map
      (spinAction (quadOdd n (GaloisField p f))) =
      ((oddFrame n (GaloisField p f)).toHypFrame.toFrame hij true false).La.range := by
    rw [hR]
    exact ModelFacts.map_longSL2_range (oddFrame n (GaloisField p f)).toHypFrame hij true false
  exact spin_fund_correspondence hodd
    (nondegenerate_polarBilin_quadOdd n (GaloisField p f)
      (ModelFacts.two_ne_zero_galoisField f hp2))
    hR₀ (fun R hR g => conjSub_mem_fundamentalSubgroups hR g)
    (fun R hR => hsc _ hR₀ R hR) _ himg hperp

end Odd

section Minus

variable {p f : ℕ} [Fact p.Prime]

theorem fundCorr_minus_of_odd (hp2 : p ≠ 2) (hf : 1 ≤ f) {n : ℕ}
    (hadm : StatedLieAdmissible .POmegaMinus n p f) :
    (∀ R ∈ fundamentalSubgroups .POmegaMinus (Twisted.minusDatum n (minusCoeffs_irr p f)),
        R.map (spinAction (quadMinus n (GaloisField p f) (minusCoeffs p f).1
          (minusCoeffs p f).2)) ∈
          fundSet (quadMinus n (GaloisField p f) (minusCoeffs p f).1 (minusCoeffs p f).2)) ∧
      ∀ L ∈ fundSet (quadMinus n (GaloisField p f) (minusCoeffs p f).1 (minusCoeffs p f).2),
        ∃ R ∈ fundamentalSubgroups .POmegaMinus (Twisted.minusDatum n (minusCoeffs_irr p f)),
          R.map (spinAction (quadMinus n (GaloisField p f) (minusCoeffs p f).1
            (minusCoeffs p f).2)) = L := by
  have hn4 : 4 ≤ n := hadm.2.2
  have hodd := odd_card_galoisField_of_ne_two (p := p) hp2 hf
  have hlong := ModelFacts.isLongestRoot_single .POmegaMinus n p f Fact.out trivial hadm
  have hsc := ModelFacts.fundamentalSingleClass .POmegaMinus n p f Fact.out trivial hadm
    (by decide) (by decide)
  have hk : (0 : ℕ) + 1 < n - 1 := by omega
  set k₀ : Fin (n - 1) := ⟨0, by omega⟩ with hk₀
  have hij := Twisted.succ_ne_of_lt n (k := k₀) hk
  have hR := Twisted.rankOne_minusRootGroup_of_lt n (minusCoeffs_irr p f) (k := k₀) hk
  have hR₀ : CFSG.LieType.CurtisTits.rankOne (Twisted.minusRootGroup n (minusCoeffs_irr p f)) k₀ ∈
      fundamentalSubgroups .POmegaMinus (Twisted.minusDatum n (minusCoeffs_irr p f)) :=
    ⟨1, Pi.single k₀ 1, Or.inl (hlong k₀ (by show 0 + 2 < n; omega)), by
      rw [conjSub_one]; rfl⟩
  have hdim : Module.finrank (GaloisField p f)
      (Fin (n - 1) ⊕ Fin (n - 1) ⊕ Fin 2 → GaloisField p f) = 2 * (n - 1) + 2 := by
    rw [Module.finrank_fintype_fun_eq_card, Fintype.card_sum, Fintype.card_sum, Fintype.card_fin,
      Fintype.card_fin]
    ring
  have hperp : 2 ≤ Module.finrank (GaloisField p f)
      ((Twisted.minusFrame n (minusCoeffs p f).1 (minusCoeffs p f).2).toHypFrame.toFrame hij
        true false).perp := by
    have := ModelFacts.finrank_perp_add_four
      ((Twisted.minusFrame n (minusCoeffs p f).1 (minusCoeffs p f).2).toHypFrame.toFrame hij
        true false)
    omega
  have himg : (CFSG.LieType.CurtisTits.rankOne (Twisted.minusRootGroup n (minusCoeffs_irr p f))
        k₀).map (spinAction (quadMinus n (GaloisField p f) (minusCoeffs p f).1
          (minusCoeffs p f).2)) =
      ((Twisted.minusFrame n (minusCoeffs p f).1 (minusCoeffs p f).2).toHypFrame.toFrame hij
        true false).La.range := by
    rw [hR]
    exact ModelFacts.map_longSL2_range
      (Twisted.minusFrame n (minusCoeffs p f).1 (minusCoeffs p f).2).toHypFrame hij true false
  exact spin_fund_correspondence hodd
    (nondegenerate_polarBilin_quadMinus_of_finite n (GaloisField p f) (minusCoeffs_irr p f))
    hR₀ (fun R hR g => conjSub_mem_fundamentalSubgroups hR g)
    (fun R hR => hsc _ hR₀ R hR) _ himg hperp

end Minus

section Plus

variable {p f : ℕ} [Fact p.Prime]

theorem fundCorr_plus_of_odd (hp2 : p ≠ 2) (hf : 1 ≤ f) {n : ℕ}
    (hadm : StatedLieAdmissible .POmegaPlus n p f) (hn : 4 ≤ n) :
    (∀ R ∈ fundamentalSubgroups .POmegaPlus (plusDatum n (GaloisField p f) (by omega)),
        R.map (spinAction (quadPlus n (GaloisField p f))) ∈
          fundSet (quadPlus n (GaloisField p f))) ∧
      ∀ L ∈ fundSet (quadPlus n (GaloisField p f)),
        ∃ R ∈ fundamentalSubgroups .POmegaPlus (plusDatum n (GaloisField p f) (by omega)),
          R.map (spinAction (quadPlus n (GaloisField p f))) = L := by
  have hn3 : 3 ≤ n := by omega
  have hodd := odd_card_galoisField_of_ne_two (p := p) hp2 hf
  have hsc : FundamentalSingleClass .POmegaPlus (plusDatum n (GaloisField p f) hn3) := by
    have := ModelFacts.fundamentalSingleClass .POmegaPlus n p f Fact.out trivial hadm
      (by decide) (by decide)
    have e := ModelFacts.modelUniv_POmegaPlus (p := p) (f := f) hn3
    rw [e] at this
    exact this
  exact ⟨fun R hR => Gaps.map_mem_fundSet hn3 hsc hR, fun L hL => Gaps.exists_map_eq hn3 hodd hL⟩

end Plus

end CFSG.ClassicalInvolution.Q3.Q3T7E9
