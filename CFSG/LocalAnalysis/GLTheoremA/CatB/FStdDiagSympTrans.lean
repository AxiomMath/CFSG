module

import CFSG.LocalAnalysis.GLTheoremA.CatA.Y10GInnSympRed
import CFSG.LocalAnalysis.GLTheoremA.CatA.Y10GFldSympMark
public import CFSG.Blueprint.SourceClassicalTransportLinear
public import CFSG.HardMathSupport.Solomon.LocalBalance.Lemma53
public import CFSG.HardMathSupport.Solomon.LocalBalance.Lemma54
public import CFSG.LocalAnalysis.GLTheoremA.CatA.Y10GField
public import CFSG.Quasithin.Vol2.Ch10SecKGA318
import CFSG.ClassicalInvolution.SmallCases.UpgradeCoverClassical
import CFSG.RankThree.PartTwo.Sec4.Census.Item44TwoCoverModels

public section

namespace CFSG.LocalAnalysis.GLTheoremA.FStdDiag

open CFSG.Open CFSG.Assembly CFSG.Yardstones.Md0ec50421ce4
open CFSG.LocalAnalysis.ComponentInitial.SymplecticHigher
open CFSG.LocalAnalysis.ComponentInitial.SymplecticFlag
open CFSG.LocalAnalysis.GLTheoremA.Y10GField (InnDiagKind)

theorem fstdSymp_transport {S : Type} [Group S] [Finite S] {labK : GLALabel} {α : MulAut S}
    (hcen : Subgroup.center S = ⊥) (hFam : labK.tag = .B ∨ labK.tag = .C) (hα3 : α ^ 3 = 1)
    (hin : InnDiagKind S labK α) :
    ∃ (K : Type) (_ : Field K) (_ : Finite K) (n m : ℕ) (x : StatedSp m K)
      (e : S ≃* StatedProj (StatedSp m K)), 1 ≤ n ∧ Nat.card K = 2 ^ n ∧ 2 ≤ m ∧
      ¬(m = 2 ∧ n = 1) ∧ x ^ 3 = 1 ∧ MulAut.congr e α = MulAut.conj (proj m K x) := by
  unfold InnDiagKind CFSG.Assembly.LargeEvenMarking at hin
  obtain ⟨-, lab', hlam, hraw⟩ := hin
  obtain ⟨_, _, _, _, hQ⟩ := CFSG.StandardType.Canonical.largeEvenRawDatum_exists hraw
  obtain ⟨-, -, -, hlab, -⟩ := hQ
  subst lab'
  rcases hFam with ht | ht
  all_goals
    have hmn : 2 ≤ labK.rank ∧ (labK.rank = 2 → 2 ≤ labK.n) := by
      have h := hlam
      simp only [LargeEvenInLambda2, ht] at h
      exact h.2
    unfold LargeEvenRawDatum at hraw
    simp only [ht] at hraw
    unfold LargeEvenRecipeSymplectic at hraw
    obtain ⟨K, hK, hKf, hcard, hQ'⟩ := hraw
    obtain ⟨-, -, θ, -, u, hu, hind⟩ := hQ'
    obtain ⟨A, hA⟩ :=
      CFSG.LocalAnalysis.GLTheoremA.Y10GFldSympMark.exists_conjAut_eq_of_mem_matConjImage hu
    let e : S ≃* StatedProj (StatedSp labK.rank K) :=
      ((QuotientGroup.quotientMulEquivOfEq hcen).trans
        QuotientGroup.quotientBot).symm.trans θ
    have hαu : ∀ l : S, e (α l) = conjAut labK.rank K A (e l) := by
      intro l
      rw [hA]
      exact (hind l (α l) rfl).symm
    have hc : (canonLabel labK).n = labK.n := by simp [canonLabel, ht]
    have hcard' : Nat.card K = 2 ^ (canonLabel labK).n := by rw [hc]; exact hcard
    have hn : 1 ≤ (canonLabel labK).n := by
      rcases Nat.eq_zero_or_pos (canonLabel labK).n with h0 | h0
      · exfalso
        rw [h0, pow_zero] at hcard'
        have : 1 < Nat.card K := Finite.one_lt_card
        omega
      · exact h0
    have h2 : (2 : K) = 0 := by
      haveI := Fintype.ofFinite K
      obtain ⟨q, hq, k, hqp, hqcard⟩ := FiniteField.card' K
      have hc2 := hcard'
      rw [Nat.card_eq_fintype_card, hqcard] at hc2
      have hdvd : q ∣ 2 ^ (canonLabel labK).n := by
        rw [← hc2]
        exact dvd_pow_self q (PNat.ne_zero k)
      have hq2 : q = 2 :=
        (Nat.prime_dvd_prime_iff_eq hqp Nat.prime_two).mp (hqp.dvd_of_dvd_pow hdvd)
      subst hq2
      exact_mod_cast CharP.cast_eq_zero K 2
    obtain ⟨x, hx⟩ := Y10GInnSympRed.exists_conjAut_eq_conj h2 A
    have hMEq : MulAut.congr e α = MulAut.conj (proj labK.rank K x) := by
      rw [← hx]
      ext r
      have h1 := hαu (e.symm r)
      rw [MulEquiv.apply_symm_apply] at h1
      exact h1
    have hZ : Subgroup.center (StatedProj (StatedSp labK.rank K)) = ⊥ := by
      rw [eq_bot_iff]
      intro z hz
      have hz' : e.symm z ∈ Subgroup.center S := by
        rw [Subgroup.mem_center_iff] at hz ⊢
        intro g
        apply e.injective
        simp only [map_mul, MulEquiv.apply_symm_apply]
        exact hz (e g)
      rw [hcen, Subgroup.mem_bot] at hz'
      rw [Subgroup.mem_bot]
      simpa using congrArg e hz'
    have hpow : MulAut.conj (proj labK.rank K x) ^ 3 = 1 := by
      rw [← hMEq, ← map_pow, hα3, map_one]
    have hxp : x ^ 3 = 1 := Y10GInnSympRed.pow_eq_one_of_conj_pow_eq_one h2 hZ hpow
    have hmne : ¬(labK.rank = 2 ∧ (canonLabel labK).n = 1) := fun h => by
      have := hmn.2 h.1
      omega
    exact ⟨K, hK, hKf, (canonLabel labK).n, labK.rank, x, e, hn, hcard', hmn.1, hmne, hxp, hMEq⟩

end CFSG.LocalAnalysis.GLTheoremA.FStdDiag

end
