module

public import CFSG.ClassicalInvolution.Asc77.AscR10E22
public import CFSG.ClassicalInvolution.Asc77.AscR10E23
public import CFSG.ClassicalInvolution.Asc77.AscR10E7
public import CFSG.ClassicalInvolution.Asc77.AscR10D3e

public section

set_option linter.unusedSectionVars false

namespace CFSG.ClassicalInvolution.ModelFacts

open CFSG.Assembly.LowTwoRank CFSG.LieType.Universal CFSG.ClassicalInvolution.Generic
  CFSG.ClassicalInvolution.Models.OrthogonalPairs CFSG.ClassicalGroups.Orthogonal QuadraticMap
open CFSG.ClassicalInvolution.WeakCT (LinearBlockStandardPair)
open CFSG.ClassicalInvolution.Phan (UnitaryBlockStandardPair Su B12 B23)
open CFSG.LieType.Universal.Spin
open CFSG.ClassicalInvolution.Asc77.T3CII (ne_two_of_pow_eq_three neZero_of_pow_eq_three
  StdDich3)
open scoped commutatorElement MatrixGroups



section Tags

variable {p : ℕ} [Fact p.Prime]

theorem spinCtx3_pOmegaPlus {n e : ℕ} (hn : 4 ≤ n) (h3 : p ^ e = 3) :
    SpinCtx3 p e (quadPlus n (GaloisField p e))
      (longestFundamental (plusDatum n (GaloisField p e) (by omega))) := by
  have hp2 := ne_two_of_pow_eq_three h3
  have hm3 : 3 ≤ n := by omega
  have hf1 : 1 ≤ e := Nat.one_le_iff_ne_zero.2 (neZero_of_pow_eq_three h3).ne
  have hadm : StatedLieAdmissible .POmegaPlus n p e := ⟨Fact.out, hf1, hn⟩
  have : NeZero n := ⟨by omega⟩
  have : Finite (spinGroup (quadPlus n (GaloisField p e))) :=
    finite_spinGroup_of_ker _ coe_ker_spinMatrix_quadPlus
  have eq' := RouteD.modelUniv_POmegaPlus_eq (p := p) (f := e) hm3
  have hsc : FundamentalSingleClass .POmegaPlus (Generic.modelUniv .POmegaPlus n p e Fact.out).D :=
    fundamentalSingleClass .POmegaPlus n p e Fact.out trivial hadm (by decide) (by decide)
  have hsc' : FundamentalSingleClass .POmegaPlus (plusDatum n (GaloisField p e) hm3) := by
    revert hsc
    rw [eq']
    exact id
  obtain ⟨-, W₁, hW₁⟩ := standardPair_plusDatum (F := GaloisField p e) hm3 hn
  have hcentral := RouteD.central_of_stdPair (p := p) (f := e)
    (Y := ⟨spinGroup (quadPlus n (GaloisField p e)), plusDatum n (GaloisField p e) hm3⟩) hsc'
    (RouteD.rankOne_mem_fundamentalSubgroups_plusDatum hm3
      (⟨0, by show 0 < n; omega⟩ : Fin n)) hW₁
  have hker := ker_spinAction_le_center (quadPlus n (GaloisField p e))
  exact
    { h3 := h3, hQ := nondegenerate_polarBilin_quadPlus n (GaloisField p e),
      fin := inferInstance, hker2 := OrthAut.plus_hker2 n,
      hC := RouteD.Gaps.not_dvd_card_center_plus hp2 hm3,
      inj := fun R hR r hr h1 => hcentral R (longestFundamental_subset .POmegaPlus _ hR) r hr
        (hker (MonoidHom.mem_ker.mpr h1)),
      map := fun R hR => RouteD.Gaps.map_mem_fundSet hm3 hsc'
        (longestFundamental_subset .POmegaPlus _ hR) }

theorem spinCtx3_pOmegaOdd {n e : ℕ} (hadm : StatedLieAdmissible .POmegaOdd n p e)
    (h3 : p ^ e = 3) :
    SpinCtx3 p e (quadOdd n (GaloisField p e))
      (longestFundamental (oddDatum n (GaloisField p e))) := by
  have hp2 := ne_two_of_pow_eq_three h3
  have hm3 : 3 ≤ n := hadm.2.2.1
  have h2 : (2 : GaloisField p e) ≠ 0 := two_ne_zero_galoisField e hp2
  have : Finite (spinGroup (quadOdd n (GaloisField p e))) :=
    finite_spinGroup_of_ker _ (coe_ker_spinMatrix_quadOdd h2)
  have hsc : FundamentalSingleClass .POmegaOdd (Generic.modelUniv .POmegaOdd n p e Fact.out).D :=
    fundamentalSingleClass .POmegaOdd n p e Fact.out trivial hadm (by decide) (by decide)
  have hsc' : FundamentalSingleClass .POmegaOdd (oddDatum n (GaloisField p e)) := hsc
  obtain ⟨W₁, hW₁⟩ := RouteD.standardPair_oddDatum_edge (F := GaloisField p e) hm3 (i := 0)
    (by omega)
  have hmem := RouteD.rankOne_mem_fundamentalSubgroups_oddDatum (K := GaloisField p e) hm3
    (i := (⟨0, by show 0 < n; omega⟩ : Fin n)) (by show 0 + 1 < n; omega)
  have hcentral := RouteD.central_of_stdPair (p := p) (f := e)
    (Y := ⟨spinGroup (quadOdd n (GaloisField p e)), oddDatum n (GaloisField p e)⟩) hsc' hmem hW₁
  have hker := ker_spinAction_le_center (quadOdd n (GaloisField p e))
  exact
    { h3 := h3, hQ := nondegenerate_polarBilin_quadOdd n (GaloisField p e) h2,
      fin := inferInstance, hker2 := OrthAut.odd_hker2 h2 n,
      hC := RouteD.Gaps.not_dvd_card_center_odd hp2 hm3,
      inj := fun R hR r hr h1 => hcentral R (longestFundamental_subset .POmegaOdd _ hR) r hr
        (hker (MonoidHom.mem_ker.mpr h1)),
      map := fun R hR => RouteD.Gaps.map_mem_fundSet_odd hm3 hsc'
        (longestFundamental_subset .POmegaOdd _ hR) }

theorem spinCtx3_pOmegaMinus {n e : ℕ} (hadm : StatedLieAdmissible .POmegaMinus n p e)
    (h3 : p ^ e = 3) :
    SpinCtx3 p e (quadMinus n (GaloisField p e) (minusCoeffs p e).1 (minusCoeffs p e).2)
      (longestFundamental (Spin.Twisted.minusDatum n (minusCoeffs_irr p e))) := by
  have hp2 := ne_two_of_pow_eq_three h3
  have hn : 4 ≤ n := hadm.2.2
  have hirr := minusCoeffs_irr p e
  have hF := RouteD.Exotic.fundCorr_minus3 (p := p) (f := e) h3 hadm
  have hsc : FundamentalSingleClass .POmegaMinus
      (Generic.modelUniv .POmegaMinus n p e Fact.out).D :=
    fundamentalSingleClass .POmegaMinus n p e Fact.out trivial hadm (by decide) (by decide)
  have hk0 : (⟨0, by omega⟩ : Fin (n - 1)).val + 1 < n - 1 := by simp only; omega
  have hR₀ := RouteD.rankOne_mem_fund_minus hirr hk0
  obtain ⟨W₁, hW₁⟩ := CFSG.ClassicalInvolution.WeakCT.linearBlockStandardPair_minusDatum hirr
    (two_ne_zero_galoisField e hp2) hn
    (i := ⟨0, by omega⟩) (j := ⟨1, by omega⟩) rfl (by simp only; omega)
  have hcentral := RouteD.central_of_stdPair hsc hR₀ hW₁
  have : Finite (spinGroup (quadMinus n (GaloisField p e) (minusCoeffs p e).1
      (minusCoeffs p e).2)) := finite_spinGroup_of_ker _ (coe_ker_spinMatrix_quadMinus hirr)
  have hker := ker_spinAction_le_center
    (quadMinus n (GaloisField p e) (minusCoeffs p e).1 (minusCoeffs p e).2)
  have hC : ¬ p ∣ Nat.card (Subgroup.center (spinGroup (quadMinus n (GaloisField p e)
      (minusCoeffs p e).1 (minusCoeffs p e).2))) := by
    intro hdvd
    obtain ⟨ζ, hζ⟩ := exists_prime_orderOf_dvd_card' p hdvd
    have hζp : (ζ : spinGroup (quadMinus n (GaloisField p e) (minusCoeffs p e).1
        (minusCoeffs p e).2)) ^ p = 1 := by
      have h1 := pow_orderOf_eq_one ζ
      rw [hζ] at h1
      simpa using congrArg (fun x : Subgroup.center (spinGroup (quadMinus n (GaloisField p e)
        (minusCoeffs p e).1 (minusCoeffs p e).2)) => (x : spinGroup (quadMinus n (GaloisField p e)
          (minusCoeffs p e).1 (minusCoeffs p e).2))) h1
    have h1 := (OrthAut.minus_center_facts hirr hp2 hn).1 _ ζ.2 hζp
    have h0 : ζ = 1 := Subtype.ext h1
    rw [h0, orderOf_one] at hζ
    exact (Fact.out : p.Prime).one_lt.ne hζ
  exact
    { h3 := h3,
      hQ := nondegenerate_polarBilin_quadMinus_of_finite n (GaloisField p e) hirr,
      fin := inferInstance, hker2 := OrthAut.minus_hker2 hirr, hC := hC,
      inj := fun R hR r hr h1 => hcentral R (longestFundamental_subset .POmegaMinus _ hR) r hr
        (hker (MonoidHom.mem_ker.mpr h1)),
      map := fun R hR => hF.1 R (longestFundamental_subset .POmegaMinus _ hR) }

theorem stdDich3Gen_pOmegaPlus {n e : ℕ} (hadm : StatedLieAdmissible .POmegaPlus n p e) :
    StdDich3Gen p .POmegaPlus n e := by
  have hn : 4 ≤ n := hadm.2.2
  unfold StdDich3Gen
  rw [RouteD.modelUniv_POmegaPlus_eq (p := p) (f := e) (by omega : 3 ≤ n)]
  intro h3 R₁ hR₁ R₂ hR₂ c₁ c₂ hc₁ hc₂ ho₁ ho₂ hc
  exact (spinCtx3_pOmegaPlus hn h3).dichotomy hR₁ hR₂ hc₁ hc₂ ho₁ ho₂ hc

theorem stdDich3Gen_pOmegaOdd {n e : ℕ} (hadm : StatedLieAdmissible .POmegaOdd n p e) :
    StdDich3Gen p .POmegaOdd n e := by
  intro h3 R₁ hR₁ R₂ hR₂ c₁ c₂ hc₁ hc₂ ho₁ ho₂ hc
  exact (spinCtx3_pOmegaOdd hadm h3).dichotomy hR₁ hR₂ hc₁ hc₂ ho₁ ho₂ hc

theorem stdDich3Gen_pOmegaMinus {n e : ℕ} (hadm : StatedLieAdmissible .POmegaMinus n p e) :
    StdDich3Gen p .POmegaMinus n e := by
  intro h3 R₁ hR₁ R₂ hR₂ c₁ c₂ hc₁ hc₂ ho₁ ho₂ hc
  exact (spinCtx3_pOmegaMinus hadm h3).dichotomy hR₁ hR₂ hc₁ hc₂ ho₁ ho₂ hc

end Tags

theorem stdDich3Orth : CFSG.ClassicalInvolution.Asc77.T3CII.StdDich3Orth := by
  intro t n hadm ht
  rcases ht with rfl | rfl | rfl
  · exact stdDich3_of_gen (stdDich3Gen_pOmegaOdd hadm)
  · exact stdDich3_of_gen (stdDich3Gen_pOmegaPlus hadm)
  · exact stdDich3_of_gen (stdDich3Gen_pOmegaMinus hadm)

end CFSG.ClassicalInvolution.ModelFacts
