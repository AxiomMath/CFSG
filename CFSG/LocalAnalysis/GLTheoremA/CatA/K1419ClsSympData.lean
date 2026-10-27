module

import CFSG.LocalAnalysis.GLTheoremA.CatA.Y10GInnSympRed
import CFSG.LocalAnalysis.GLTheoremA.CatA.Y10GFldSympMark
import CFSG.LocalAnalysis.GLTheoremA.CatA.Y10GU64Glue
public import CFSG.ClassicalInvolution.SmallCases.UpgradeCoverClassical
public import CFSG.HardMathSupport.Solomon.LocalBalance.Lemma53
public import CFSG.HardMathSupport.Solomon.LocalBalance.Lemma54
public import CFSG.LocalAnalysis.GLTheoremA.CatA.Y10GField
public import CFSG.LocalAnalysis.GLTheoremA.PartI.Transfer
public import CFSG.Quasithin.Vol2.Ch10SecKGA318
public import CFSG.RankThree.PartTwo.Sec4.Census.Item44TwoCoverModels

public section

namespace CFSG.LocalAnalysis.GLTheoremA.K1419

open CFSG.Open CFSG.Open.StatedAPI CFSG.Assembly CFSG.Yardstones.Md0ec50421ce4
  CFSG.LocalAnalysis.GLTheoremB CFSG.LocalAnalysis.GLTheoremA
  CFSG.LocalAnalysis.ComponentInitial.SymplecticHigher
  CFSG.LocalAnalysis.ComponentInitial.SymplecticFlag
open CFSG.HardMathSupport.Solomon.Coordinator (fixSubgroup)
open CFSG.LocalAnalysis.GLTheoremA.Y10GField (InnDiagKind)

theorem k1419ClsSympData {S : Type} [Group S] [Finite S] {labK : GLALabel} {α : MulAut S}
    (hcen : Subgroup.center S = ⊥) (hFam : labK.tag = .B ∨ labK.tag = .C) (hα3 : α ^ 3 = 1)
    (hα1 : α ≠ 1) (hin : InnDiagKind S labK α) {J : Subgroup S}
    (hJ : GLAPComponent 3 (fixSubgroup α) J) :
    ∃ (K : Type) (_ : Field K) (_ : Finite K) (n m : ℕ) (x : StatedSp m K)
      (J' : Subgroup (StatedProj (StatedSp m K))),
      1 ≤ n ∧ Nat.card K = 2 ^ n ∧ (2 : K) = 0 ∧ 2 ≤ m ∧ x ^ 3 = 1 ∧ x ≠ 1 ∧
      GLAPComponent 3 (fixSubgroup (MulAut.conj (proj m K x))) J' ∧
      Nonempty (PQuot 3 J ≃* PQuot 3 J') := by
  unfold InnDiagKind CFSG.Assembly.LargeEvenMarking at hin
  obtain ⟨-, lab', hlam, hraw⟩ := hin
  obtain ⟨_, _, _, _, hQ⟩ := CFSG.StandardType.Canonical.largeEvenRawDatum_exists hraw
  obtain ⟨-, -, -, hlab, -⟩ := hQ
  subst lab'
  rcases hFam with ht | ht
  all_goals
    have hm : 2 ≤ labK.rank := by
      have h := hlam
      simp only [LargeEvenInLambda2, ht] at h
      exact h.2.1
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
    have hxp : x ^ 3 = 1 :=
      Y10GInnSympRed.pow_eq_one_of_conj_pow_eq_one h2 hZ hpow
    have hx1 : x ≠ 1 := by
      intro hx1
      apply hα1
      ext s
      have h := hαu s
      rw [hx, hx1, map_one, MulAut.conj_apply, inv_one, mul_one, one_mul] at h
      simpa using e.injective h
    have hJ' : GLAPComponent 3 (fixSubgroup (MulAut.conj (proj labK.rank K x)))
        (J.map e.toMonoidHom) := by
      have h := CFSG.LocalAnalysis.GLTheoremA.Y10F.glaPComponent_transport e α hJ
      rwa [hMEq] at h
    have hkerbot : e.toMonoidHom.ker = ⊥ := (MonoidHom.ker_eq_bot_iff _).2 e.injective
    have hequiv : Nonempty (PQuot 3 J ≃* PQuot 3 (J.map e.toMonoidHom)) := by
      refine nonempty_pQuot_equiv_map Nat.prime_three (ψ := e.toMonoidHom) ?_ J
      rw [hkerbot, Subgroup.card_bot]
      norm_num
    exact ⟨K, hK, hKf, (canonLabel labK).n, labK.rank, x, J.map e.toMonoidHom,
      hn, hcard', h2, hm, hxp, hx1, hJ', hequiv⟩

end CFSG.LocalAnalysis.GLTheoremA.K1419
