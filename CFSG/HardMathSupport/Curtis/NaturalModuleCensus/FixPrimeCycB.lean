module

public import CFSG.HardMathSupport.Curtis.NaturalModuleCensus.FixPrimeBar
public import CFSG.HardMathSupport.Curtis.NaturalModuleCensus.Symplectic.Main
public import CFSG.LocalAnalysis.AGLEmbedding.ToralCensusHubPrime
public import CFSG.LocalAnalysis.AGLEmbedding.ToralCensusCent

public section

namespace CFSG.HardMathSupport.Curtis.NaturalModuleCensus

open CFSG.Open CFSG.QuasithinUnique CFSG.AGLEmbedding CFSG.Assembly.LowTwoRank

theorem fixPrimeCycTorus_b : FixPrimeCycTorus IdxB := by
  intro Y _ _ L J p u h hX
  exfalso
  obtain ⟨l, c, -, -, -, hbar⟩ := exists_fixBarData_of_fixPrimeHyp h
  obtain ⟨⟨d, hv⟩, hPd, hnt, ⟨e⟩⟩ := hX
  cases d with
  | B r q =>
    have hq2 : q.p = 2 := hPd
    have hnt' : q.card ≠ 2 ∧ p ∣ q.card - 1 := by
      simpa [IndexTorusFree] using hnt
    have hr : 2 ≤ r := (TauCeti.LieTypeIndex.inStandardRange_iff _).1
      ((TauCeti.LieTypeIndex.valid_iff _).1 hv).1 |>.1
    have hq4 : 4 ≤ q.card := by
      rcases ToralCensus.card_eq_two_or_four_le_of_p_eq_two hq2 with h2 | h4
      · exact absurd h2 hnt'.1
      · exact h4
    have hmodel : StatedClassicalModel (↥L ⧸ Subgroup.center ↥L) .PSp r 2 q.exponent := by
      by_cases h2 : r = 2
      · subst h2
        have hm := CFSG.QuasithinUnique.SQTK.statedClassicalModel_typeB2 q hv e
        rwa [hq2] at hm
      · have hm := CFSG.RankThree.PartTwo.Census.statedClassicalModel_typeB_even r q hv hq2
          (by omega) e
        rwa [hq2] at hm
    obtain ⟨-, K, hK, hKfin, hcard, ⟨e'⟩⟩ := hmodel
    have hcardK : Nat.card K = q.card := by
      rw [hcard, TauCeti.PrimePower.card_def, hq2]
    have hf1 : 1 ≤ q.exponent := q.exponent_pos
    have : CharP K 2 :=
      CFSG.LocalAnalysis.ComponentInitial.finite_field_prime_power_characteristic Nat.prime_two hf1
        hcard
    have : NeZero r := ⟨by omega⟩
    have hbij := (CFSG.LocalAnalysis.ComponentInitial.UnitaryHigher.even_symplectic_semilinear_normal_form
      (r := r) (K := K) hf1 hcard).1
    let π : StatedSp r K ≃* StatedProj (StatedSp r K) := MulEquiv.ofBijective _ hbij
    have hfin : Finite (StatedSp r K) := by
      have : Finite (StatedProj (StatedSp r K)) := Finite.of_equiv _ e'.toEquiv
      exact Finite.of_equiv _ π.toEquiv.symm
    let ee : (↥L ⧸ Subgroup.center ↥L) ≃* StatedSp r K := e'.trans π.symm
    exact false_of_fixBarData_symplectic (by omega) (by omega) h.prime h.five_le
      (by rw [hcardK]; exact hnt'.2) (hbar.map_mulEquiv ee)
  | _ => exact hPd.elim

end CFSG.HardMathSupport.Curtis.NaturalModuleCensus
