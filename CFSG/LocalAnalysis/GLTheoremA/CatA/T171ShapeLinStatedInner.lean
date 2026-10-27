module

public import CFSG.LocalAnalysis.GLTheoremA.CatA.T171ShapeLinStatedMain
public import CFSG.LocalAnalysis.GLTheoremA.CatA.T171ShapeFamClRed
import CFSG.LocalAnalysis.GLTheoremA.CatA.T171ShapeFamInLUComp
import CFSG.LocalAnalysis.GLTheoremA.CatA.T171ShapeFamInLinTransComm
import CFSG.LocalAnalysis.GLTheoremA.CatA.T171ShapeFamOutBase
import CFSG.LocalAnalysis.GLTheoremA.CatA.T171ShapeGLMark

public section

namespace CFSG.LocalAnalysis.GLTheoremA.T171Sh

open CFSG.Open CFSG.Assembly CFSG.StandardType CFSG.LocalAnalysis.ComponentInitial
  CFSG.Yardstones.Md0ec50421ce4
open CFSG.LocalAnalysis.GLTheoremA.S10 CFSG.LocalAnalysis.GLTheoremA.KD264Lie
open CFSG.LocalAnalysis.GLTheoremA.I2015
open scoped commutatorElement

theorem innerCompNonShapeW_linear_charTwo :
    InnerCompNonShapeW fun i => KD264Lie.isLinearIdx i ∧ i.characteristic = 2 := by
  intro G _ _ p L J A d b hS hcat hshape _hin
  obtain ⟨d₀, hv, hP, ⟨e⟩⟩ := CFSG.LocalAnalysis.GLTheoremA.CatB.exists_lieIndex hcat
  have hdA : ∃ r q, d₀ = .A r q := by
    cases d₀ <;> simp [KD264Lie.isLinearIdx] at hP
    exact ⟨_, _, rfl⟩
  obtain ⟨r, q, rfl⟩ := hdA
  have hq2 : q.p = 2 := by
    have h := hP.2
    rwa [TauCeti.LieTypeIndex.characteristic_A] at h
  have hcardq : q.card = 2 ^ q.exponent := by
    rw [TauCeti.PrimePower.card_def, hq2]
  have hcatA : catalogIs (PSimple p L) (onLie fun i =>
      ∃ q' : TauCeti.PrimePower, i = .A ((r + 1) - 1) q' ∧ q'.card = 2 ^ q.exponent) :=
    ⟨.lie ⟨.A r q, hv⟩, ⟨q, by simp, hcardq⟩, ⟨e⟩⟩
  obtain ⟨K, hK, hKfin, hKcard, θ, hact⟩ :=
    linMarking_holds G p L J A d b (r + 1) q.exponent hS hcatA
  letI : Field K := hK
  letI : Finite K := hKfin
  have hN2 : 2 ≤ r + 1 := by
    have h := ((TauCeti.LieTypeIndex.inStandardRange_iff _).mp
      ((TauCeti.LieTypeIndex.valid_iff _).mp hv).1).1
    omega
  have hnot : ¬ (p ∣ r + 1 ∧ p ∣ Nat.card K - 1) := by
    rintro ⟨hpN, hpK⟩
    apply hshape
    refine ⟨.lie ⟨.A r q, hv⟩, ⟨hq2, ?_⟩, ⟨e⟩⟩
    rw [Nat.dvd_gcd_iff]
    refine ⟨hpN, ?_⟩
    have hqK : q.card = Nat.card K := by
      rw [TauCeti.PrimePower.card_def, hq2, hKcard]
    rwa [hqK]
  have hHnorm : ∀ x : GL (Fin (r + 1)) K,
      x ∈ Subgroup.normalizer
        (LargeEvenSLGroup (Fin (r + 1)) K : Set (GL (Fin (r + 1)) K)) := by
    intro x
    rw [Subgroup.normalizer_eq_top_iff.mpr
      (inferInstance : (LargeEvenSLGroup (Fin (r + 1)) K).Normal)]
    exact Subgroup.mem_top x
  have hmat : ∀ a ∈ A, ∃ (Da : GL (Fin (r + 1)) K)
      (hDa : Da ∈ Subgroup.normalizer
        (LargeEvenSLGroup (Fin (r + 1)) K : Set (GL (Fin (r + 1)) K))),
      LargeEvenInduces θ (conjRel a)
        (TableB.projConj (LargeEvenSLGroup (Fin (r + 1)) K) ⟨Da, hDa⟩) := by
    intro a ha
    obtain ⟨φ, hφ, hφind⟩ := hact a ha
    obtain ⟨M, -, rfl⟩ := TableB.exists_eq_projConj
      (H := LargeEvenSLGroup (Fin (r + 1)) K) (S := Set.univ)
      (fun x _ => hHnorm x) hφ
    exact ⟨M, hHnorm M, hφind⟩
  obtain ⟨D, hD, hDind⟩ := hmat d hS.d_mem
  obtain ⟨B, hB, hBind⟩ := hmat b hS.b_mem
  have hdp : d ^ p = 1 := hS.elem.2 d hS.d_mem
  have hbp : b ^ p = 1 := hS.elem.2 b hS.b_mem
  have hdN : d ∈ Subgroup.normalizer (L : Set G) :=
    CFSG.LocalAnalysis.GLTheoremA.S171.normalizer_of_innerDiagMarking hS.idiag hS.d_mem
  have hbN : b ∈ Subgroup.normalizer (L : Set G) :=
    CFSG.LocalAnalysis.GLTheoremA.S171.normalizer_of_innerDiagMarking hS.idiag hS.b_mem
  have hDpow : LinearFlag.conjAut (r + 1) K D ^ p = 1 := by
    rw [← projConj_recipe D hD, ← map_pow,
      largeEvenInduces_pow_eq_one hdN hDind hdp, map_one]
  have hBpow : LinearFlag.conjAut (r + 1) K B ^ p = 1 := by
    rw [← projConj_recipe B hB, ← map_pow,
      largeEvenInduces_pow_eq_one hbN hBind hbp, map_one]
  have hdb : d * b = b * d :=
    CFSG.LocalAnalysis.GLTheoremA.isElemAbelian_commute hS.elem hS.d_mem hS.b_mem
  have hcomm_proj : TableB.projConj (LargeEvenSLGroup (Fin (r + 1)) K) ⟨D, hD⟩ *
      TableB.projConj (LargeEvenSLGroup (Fin (r + 1)) K) ⟨B, hB⟩ =
      TableB.projConj (LargeEvenSLGroup (Fin (r + 1)) K) ⟨B, hB⟩ *
        TableB.projConj (LargeEvenSLGroup (Fin (r + 1)) K) ⟨D, hD⟩ := by
    refine largeEvenInduces_unique
      (largeEvenInduces_mul hdN hbN hdb hDind hBind) ?_
      (conjRel_total (mul_mem hdN hbN))
    have h1 : LargeEvenInduces θ (conjRel (b * d))
        (TableB.projConj (LargeEvenSLGroup (Fin (r + 1)) K) ⟨B, hB⟩ *
          TableB.projConj (LargeEvenSLGroup (Fin (r + 1)) K) ⟨D, hD⟩) :=
      largeEvenInduces_mul hbN hdN hdb.symm hBind hDind
    rwa [← hdb] at h1
  have hcomm_aut : LinearFlag.conjAut (r + 1) K D * LinearFlag.conjAut (r + 1) K B =
      LinearFlag.conjAut (r + 1) K B * LinearFlag.conjAut (r + 1) K D := by
    calc LinearFlag.conjAut (r + 1) K D * LinearFlag.conjAut (r + 1) K B
        = MulAut.congr (linRecipeEquiv (r + 1) K).symm
            (TableB.projConj (LargeEvenSLGroup (Fin (r + 1)) K) ⟨D, hD⟩) *
          MulAut.congr (linRecipeEquiv (r + 1) K).symm
            (TableB.projConj (LargeEvenSLGroup (Fin (r + 1)) K) ⟨B, hB⟩) := by
          rw [projConj_recipe D hD, projConj_recipe B hB]
      _ = MulAut.congr (linRecipeEquiv (r + 1) K).symm
            (TableB.projConj (LargeEvenSLGroup (Fin (r + 1)) K) ⟨D, hD⟩ *
              TableB.projConj (LargeEvenSLGroup (Fin (r + 1)) K) ⟨B, hB⟩) :=
          (map_mul _ _ _).symm
      _ = MulAut.congr (linRecipeEquiv (r + 1) K).symm
            (TableB.projConj (LargeEvenSLGroup (Fin (r + 1)) K) ⟨B, hB⟩ *
              TableB.projConj (LargeEvenSLGroup (Fin (r + 1)) K) ⟨D, hD⟩) := by
          rw [hcomm_proj]
      _ = MulAut.congr (linRecipeEquiv (r + 1) K).symm
            (TableB.projConj (LargeEvenSLGroup (Fin (r + 1)) K) ⟨B, hB⟩) *
          MulAut.congr (linRecipeEquiv (r + 1) K).symm
            (TableB.projConj (LargeEvenSLGroup (Fin (r + 1)) K) ⟨D, hD⟩) :=
          map_mul _ _ _
      _ = LinearFlag.conjAut (r + 1) K B * LinearFlag.conjAut (r + 1) K D := by
          rw [projConj_recipe B hB, projConj_recipe D hD]
  obtain ⟨D', B', hD'p, hB'p, hD'B', hD'eq, hB'eq⟩ :=
    exists_commuting_pow_one_lifts (K := K) (N := r + 1) hS.prime hN2 hnot
      hDpow hBpow hcomm_aut
  have hD'norm : D' ∈ Subgroup.normalizer
      (LargeEvenSLGroup (Fin (r + 1)) K : Set (GL (Fin (r + 1)) K)) := hHnorm D'
  have hB'norm : B' ∈ Subgroup.normalizer
      (LargeEvenSLGroup (Fin (r + 1)) K : Set (GL (Fin (r + 1)) K)) := hHnorm B'
  have hEqD : TableB.projConj (LargeEvenSLGroup (Fin (r + 1)) K) ⟨D', hD'norm⟩ =
      TableB.projConj (LargeEvenSLGroup (Fin (r + 1)) K) ⟨D, hD⟩ := by
    apply (MulAut.congr (linRecipeEquiv (r + 1) K).symm).injective
    rw [projConj_recipe D' hD'norm, projConj_recipe D hD, hD'eq]
  have hEqB : TableB.projConj (LargeEvenSLGroup (Fin (r + 1)) K) ⟨B', hB'norm⟩ =
      TableB.projConj (LargeEvenSLGroup (Fin (r + 1)) K) ⟨B, hB⟩ := by
    apply (MulAut.congr (linRecipeEquiv (r + 1) K).symm).injective
    rw [projConj_recipe B' hB'norm, projConj_recipe B hB, hB'eq]
  have hD'ind : LargeEvenInduces θ (conjRel d)
      (TableB.projConj (LargeEvenSLGroup (Fin (r + 1)) K) ⟨D', hD'norm⟩) := by
    rw [hEqD]
    exact hDind
  have hB'ind : LargeEvenInduces θ (conjRel b)
      (TableB.projConj (LargeEvenSLGroup (Fin (r + 1)) K) ⟨B', hB'norm⟩) := by
    rw [hEqB]
    exact hBind
  exact (linBlockInnDiag_of_stated linBlockInnDiagStated_holds) G p L J A d b (r + 1)
    q.exponent K hKcard hS θ D' B' hD'norm hB'norm hD'p hD'B' hD'ind hB'ind

theorem innerCompNonShape_linear_charTwo :
    InnerCompNonShape fun i => KD264Lie.isLinearIdx i ∧ i.characteristic = 2 :=
  innerCompNonShape_of_W innerCompNonShapeW_linear_charTwo

end CFSG.LocalAnalysis.GLTheoremA.T171Sh

end
