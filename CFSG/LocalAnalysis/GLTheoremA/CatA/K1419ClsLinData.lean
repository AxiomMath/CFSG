module

import CFSG.LocalAnalysis.GLTheoremA.CatA.Y10GInnLinRed
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
  CFSG.LocalAnalysis.GLTheoremB CFSG.LocalAnalysis.GLTheoremA Matrix
open CFSG.HardMathSupport.Solomon.Coordinator (fixSubgroup)
open CFSG.LocalAnalysis.GLTheoremA.Y10GField (FamLin InnDiagKind)

theorem k1419ClsLinData {S : Type} [Group S] [Finite S] {labK : GLALabel} {α : MulAut S}
    (hcen : Subgroup.center S = ⊥) (hFam : FamLin labK) (hα3 : α ^ 3 = 1) (hα1 : α ≠ 1)
    (hin : InnDiagKind S labK α) {J : Subgroup S} (hJ : GLAPComponent 3 (fixSubgroup α) J) :
    ∃ (K : Type) (_ : Field K) (_ : Finite K) (d : ℕ) (A : GL (Fin d) K)
      (u : MulAut (LargeEvenProj (StatedSL d K))) (J' : Subgroup (LargeEvenProj (StatedSL d K))),
      (2 : K) = 0 ∧ 1 ≤ d ∧ (∃ k : ℕ, Nat.card K = 2 ^ k) ∧
      (∀ h h' : ↥(StatedSL d K), (h' : GL (Fin d) K) = A * (h : GL (Fin d) K) * A⁻¹ →
        u (LargeEvenProjMk (StatedSL d K) h) = LargeEvenProjMk (StatedSL d K) h') ∧
      u ^ 3 = 1 ∧
      (∀ c : K, (A : Matrix (Fin d) (Fin d) K) ≠ c • (1 : Matrix (Fin d) (Fin d) K)) ∧
      GLAPComponent 3 (fixSubgroup u) J' ∧ Nonempty (PQuot 3 J ≃* PQuot 3 J') := by
  obtain ⟨K, hK, hKf, d, hd, hcard, A, u, e, hαu, hgraph⟩ :=
    CFSG.LocalAnalysis.GLTheoremA.Y10GInnLin.innDiag_linear_data hcen hFam hin
  have h2 : (2 : K) = 0 := by
    haveI := Fintype.ofFinite K
    obtain ⟨q, hq, n, hqp, hqcard⟩ := FiniteField.card' K
    rw [Nat.card_eq_fintype_card, hqcard] at hcard
    have hdvd : q ∣ 2 ^ (canonLabel labK).n := by
      rw [← hcard]
      exact dvd_pow_self q (PNat.ne_zero n)
    have hq2 : q = 2 :=
      (Nat.prime_dvd_prime_iff_eq hqp Nat.prime_two).mp (hqp.dvd_of_dvd_pow hdvd)
    subst hq2
    exact_mod_cast CharP.cast_eq_zero K 2
  have hMEq : MulAut.congr e α = u := by
    ext r
    have h1 := hαu (e.symm r)
    rw [MulEquiv.apply_symm_apply] at h1
    exact h1
  have hpow : u ^ 3 = 1 := by
    rw [← hMEq, ← map_pow, hα3, map_one]
  have hJ' : GLAPComponent 3 (fixSubgroup u) (J.map e.toMonoidHom) := by
    rw [← hMEq]
    exact CFSG.LocalAnalysis.GLTheoremA.Y10F.glaPComponent_transport e α hJ
  have hkerbot : e.toMonoidHom.ker = ⊥ := (MonoidHom.ker_eq_bot_iff _).2 e.injective
  have hequiv : Nonempty (PQuot 3 J ≃* PQuot 3 (J.map e.toMonoidHom)) := by
    refine nonempty_pQuot_equiv_map Nat.prime_three (ψ := e.toMonoidHom) ?_ J
    rw [hkerbot, Subgroup.card_bot]
    norm_num
  have hAns : ∀ c : K,
      (A : Matrix (Fin d) (Fin d) K) ≠ c • (1 : Matrix (Fin d) (Fin d) K) := by
    intro c hc
    have hAcenter : A ∈ Subgroup.center (GL (Fin d) K) := by
      rw [Matrix.GeneralLinearGroup.mem_center_iff_val_mem_range_scalar]
      exact ⟨c, by rw [hc, Matrix.scalar_apply, Matrix.smul_one_eq_diagonal]⟩
    have hconj : ∀ h : ↥(StatedSL d K),
        (h : GL (Fin d) K) = A * (h : GL (Fin d) K) * A⁻¹ := by
      intro h
      have hcomm : (h : GL (Fin d) K) * A = A * (h : GL (Fin d) K) :=
        Subgroup.mem_center_iff.mp hAcenter (h : GL (Fin d) K)
      rw [← hcomm]
      group
    have hu1 : u = 1 := by
      ext x
      obtain ⟨h, rfl⟩ := QuotientGroup.mk'_surjective
        (N := (LargeEvenScalars (Fin d) K).subgroupOf (StatedSL d K)) x
      simpa using hgraph h h (hconj h)
    apply hα1
    ext l
    have h := hαu l
    rw [hu1, MulAut.one_apply] at h
    simpa using e.injective h
  exact ⟨K, hK, hKf, d, A, u, J.map e.toMonoidHom, h2, hd,
    ⟨(canonLabel labK).n, hcard⟩, hgraph, hpow, hAns, hJ', hequiv⟩

end CFSG.LocalAnalysis.GLTheoremA.K1419
