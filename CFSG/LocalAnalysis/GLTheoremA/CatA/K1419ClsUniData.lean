module

public import CFSG.LocalAnalysis.GLTheoremA.CatA.Y10GInnUniData
import CFSG.LocalAnalysis.GLTheoremA.CatA.Y10GU64Glue
public import CFSG.ClassicalInvolution.SmallCases.UpgradeCoverClassical
public import CFSG.HardMathSupport.Solomon.LocalBalance.Lemma53
public import CFSG.HardMathSupport.Solomon.LocalBalance.Lemma54
public import CFSG.LocalAnalysis.GLTheoremA.PartI.Transfer
public import CFSG.Quasithin.Vol2.Ch10SecKGA318
public import CFSG.RankThree.PartTwo.Sec4.Census.Item44TwoCoverModels

public section

namespace CFSG.LocalAnalysis.GLTheoremA.K1419

open CFSG.Open CFSG.Open.StatedAPI CFSG.Assembly CFSG.Yardstones.Md0ec50421ce4
  CFSG.LocalAnalysis.GLTheoremB CFSG.LocalAnalysis.GLTheoremA Matrix
open CFSG.HardMathSupport.Solomon.Coordinator (fixSubgroup)
open CFSG.LocalAnalysis.GLTheoremA.Y10GField (FamUni InnDiagKind)
open CFSG.LieType.SemisimpleCentralizers.Held (heldGU)

theorem k1419ClsUniData {S : Type} [Group S] [Finite S] {labK : GLALabel} {α : MulAut S}
    (hcen : Subgroup.center S = ⊥) (hFam : FamUni labK) (hα3 : α ^ 3 = 1) (hα1 : α ≠ 1)
    (hin : InnDiagKind S labK α) {J : Subgroup S} (hJ : GLAPComponent 3 (fixSubgroup α) J) :
    ∃ (K : Type) (_ : Field K) (_ : Finite K) (k d : ℕ) (τ : K ≃+* K) (hτ : ∀ x, τ (τ x) = x)
      (A : GL (Fin d) K) (u : MulAut (LargeEvenProj (StatedSU d (2 ^ k) K)))
      (J' : Subgroup (LargeEvenProj (StatedSU d (2 ^ k) K))),
      (∀ x, τ x = x ^ 2 ^ k) ∧ Nat.card K = (2 ^ k) ^ 2 ∧ 3 ≤ d ∧ (d, 2 ^ k) ≠ (3, 2) ∧
      A ∈ heldGU d K τ hτ ∧
      (∀ h h' : ↥(StatedSU d (2 ^ k) K), (h' : GL (Fin d) K) = A * (h : GL (Fin d) K) * A⁻¹ →
        u (LargeEvenProjMk (StatedSU d (2 ^ k) K) h) = LargeEvenProjMk (StatedSU d (2 ^ k) K) h') ∧
      u ^ 3 = 1 ∧
      (∀ c : K, (A : Matrix (Fin d) (Fin d) K) ≠ c • (1 : Matrix (Fin d) (Fin d) K)) ∧
      GLAPComponent 3 (fixSubgroup u) J' ∧ Nonempty (PQuot 3 J ≃* PQuot 3 J') := by
  obtain ⟨K, hK, hKf, d, τ, hτ, hτq, hcard, hd3, hd3n, A, u, e, hA, hαu, hgraph⟩ :=
    CFSG.LocalAnalysis.GLTheoremA.Y10GInnUni.innDiag_unitary_data hcen hFam hin
  have hdQ : (d, 2 ^ labK.n) ≠ (3, 2) := by
    intro h
    obtain ⟨hd, hQ⟩ := Prod.mk.inj h
    have h2n : 2 ≤ labK.n := hd3n hd
    have : 2 ^ 2 ≤ 2 ^ labK.n := Nat.pow_le_pow_right (by norm_num) h2n
    omega
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
    have hconj : ∀ h : ↥(StatedSU d (2 ^ labK.n) K),
        (h : GL (Fin d) K) = A * (h : GL (Fin d) K) * A⁻¹ := by
      intro h
      have hcomm : (h : GL (Fin d) K) * A = A * (h : GL (Fin d) K) :=
        Subgroup.mem_center_iff.mp hAcenter (h : GL (Fin d) K)
      rw [← hcomm]
      group
    have hu1 : u = 1 := by
      ext x
      obtain ⟨h, rfl⟩ := QuotientGroup.mk'_surjective
        (N := (LargeEvenScalars (Fin d) K).subgroupOf (StatedSU d (2 ^ labK.n) K)) x
      simpa using hgraph h h (hconj h)
    apply hα1
    ext l
    have h := hαu l
    rw [hu1, MulAut.one_apply] at h
    simpa using e.injective h
  exact ⟨K, hK, hKf, labK.n, d, τ, hτ, A, u, J.map e.toMonoidHom, hτq, hcard, hd3, hdQ,
    hA, hgraph, hpow, hAns, hJ', hequiv⟩

end CFSG.LocalAnalysis.GLTheoremA.K1419
