module

public import CFSG.LocalAnalysis.GLTheoremA.CatA.T171ShapeBlockDefs
public import CFSG.LocalAnalysis.GLTheoremA.CatA.T171ShapeFamClRed
public import CFSG.LocalAnalysis.GLTheoremA.CatA.T171ShapeGLMark
import CFSG.LocalAnalysis.GLTheoremA.CatA.T171ShapeFamOutBase
import CFSG.LocalAnalysis.GLTheoremA.CatA.S171Basic
import CFSG.LocalAnalysis.GLTheoremA.CatA.T171ShapeUniInnerLift
import CFSG.LocalAnalysis.GLTheoremA.CatB.Bridges
import CFSG.Blueprint.LieModelAPI
import CFSG.LargeExtraspecial.OfFStar
import CFSG.LocalAnalysis.AGLEmbedding.KFactProofs.ONanChevInnerCover
import CFSG.Models.Transport

public section

namespace CFSG.LocalAnalysis.GLTheoremA.T171Sh

open CFSG.Open CFSG.Assembly CFSG.StandardType CFSG.LocalAnalysis.ComponentInitial
  CFSG.Yardstones.Md0ec50421ce4 CFSG.ClassicalGroups.UnitaryFlag
open CFSG.LocalAnalysis.GLTheoremA.S10 CFSG.LocalAnalysis.GLTheoremA.KD264Lie
open scoped commutatorElement

theorem innerCompNonShapeW_unitary_charTwo_of_block
    (hUB : UniBlockInnDiag) :
    InnerCompNonShapeW fun i => KD264Lie.isUnitaryIdx i ∧ i.characteristic = 2 := by
  intro G _ _ p L J A d b hS hcat hshape _hin
  obtain ⟨d₀, hv, hP, ⟨e⟩⟩ := CFSG.LocalAnalysis.GLTheoremA.CatB.exists_lieIndex hcat
  have hdA : ∃ r q, d₀ = .twistedA r q := by
    cases d₀ <;> simp [KD264Lie.isUnitaryIdx] at hP
    exact ⟨_, _, rfl⟩
  obtain ⟨r, q, rfl⟩ := hdA
  have hq2 : q.p = 2 := by
    have h := hP.2
    rwa [TauCeti.LieTypeIndex.characteristic_twistedA] at h
  have hcardq : q.card = 2 ^ q.exponent := by
    rw [TauCeti.PrimePower.card_def, hq2]
  have hcatA : catalogIs (PSimple p L) (onLie fun i =>
      ∃ q' : TauCeti.PrimePower, i = .twistedA ((r + 1) - 1) q' ∧
        q'.card = 2 ^ q.exponent) :=
    ⟨.lie ⟨.twistedA r q, hv⟩, ⟨q, by simp, hcardq⟩, ⟨e⟩⟩
  obtain ⟨K, hK, hKfin, hfield, θ, hact⟩ :=
    uniMarking_holds G p L J A d b (r + 1) q.exponent hS hcatA
  letI : Field K := hK
  letI : Finite K := hKfin
  have hrange : 2 ≤ r ∧ (r = 2 → 3 ≤ q.card) := by
    have h := (TauCeti.LieTypeIndex.valid_iff _).mp hv |>.1
    simpa only [TauCeti.LieTypeIndex.inStandardRange_iff] using h
  have hN3 : 3 ≤ r + 1 := by omega
  have hNq : (r + 1, 2 ^ q.exponent) ≠ (3, 2) := by
    intro h
    obtain ⟨h1, h2⟩ := (Prod.mk.injEq _ _ _ _).mp h
    have hq3 : 3 ≤ q.card := hrange.2 (by omega)
    rw [hcardq] at hq3
    omega
  have hnot : ¬ (p ∣ r + 1 ∧ p ∣ 2 ^ q.exponent + 1) := by
    rintro ⟨hpN, hpK⟩
    apply hshape
    refine ⟨.lie ⟨.twistedA r q, hv⟩, ⟨hq2, ?_⟩, ⟨e⟩⟩
    rw [Nat.dvd_gcd_iff]
    refine ⟨hpN, ?_⟩
    rwa [← hcardq] at hpK
  have hmat : ∀ a ∈ A, ∃ (Da : GL (Fin (r + 1)) K)
      (hDa : Da ∈ LargeEvenGUSet (Fin (r + 1)) K (2 ^ q.exponent))
      (hDaN : Da ∈ Subgroup.normalizer
        (unitarySU 2 q.exponent K (r + 1) : Set (GL (Fin (r + 1)) K))),
      LargeEvenInduces θ (conjRel a)
        (TableB.projConj (unitarySU 2 q.exponent K (r + 1)) ⟨Da, hDaN⟩) := by
    intro a ha
    obtain ⟨φ, hφ, hφind⟩ := hact a ha
    obtain ⟨M, hM, rfl⟩ := TableB.exists_eq_projConj
      (H := unitarySU 2 q.exponent K (r + 1))
      (S := LargeEvenGUSet (Fin (r + 1)) K (2 ^ q.exponent))
      (TableBUE.gu_subset_normalizer hfield) hφ
    exact ⟨M, hM, TableBUE.gu_subset_normalizer hfield hM, hφind⟩
  obtain ⟨D, hDgu, hDN, hDind⟩ := hmat d hS.d_mem
  obtain ⟨B, hBgu, hBN, hBind⟩ := hmat b hS.b_mem
  have hdp : d ^ p = 1 := hS.elem.2 d hS.d_mem
  have hbp : b ^ p = 1 := hS.elem.2 b hS.b_mem
  have hdN : d ∈ Subgroup.normalizer (L : Set G) :=
    CFSG.LocalAnalysis.GLTheoremA.S171.normalizer_of_innerDiagMarking hS.idiag hS.d_mem
  have hbN : b ∈ Subgroup.normalizer (L : Set G) :=
    CFSG.LocalAnalysis.GLTheoremA.S171.normalizer_of_innerDiagMarking hS.idiag hS.b_mem
  have hDpow : (TableB.projConj (unitarySU 2 q.exponent K (r + 1)) ⟨D, hDN⟩) ^ p = 1 :=
    largeEvenInduces_pow_eq_one hdN hDind hdp
  have hBpow : (TableB.projConj (unitarySU 2 q.exponent K (r + 1)) ⟨B, hBN⟩) ^ p = 1 :=
    largeEvenInduces_pow_eq_one hbN hBind hbp
  have hdb : d * b = b * d :=
    CFSG.LocalAnalysis.GLTheoremA.isElemAbelian_commute hS.elem hS.d_mem hS.b_mem
  have hcomm_proj : TableB.projConj (unitarySU 2 q.exponent K (r + 1)) ⟨D, hDN⟩ *
      TableB.projConj (unitarySU 2 q.exponent K (r + 1)) ⟨B, hBN⟩ =
      TableB.projConj (unitarySU 2 q.exponent K (r + 1)) ⟨B, hBN⟩ *
        TableB.projConj (unitarySU 2 q.exponent K (r + 1)) ⟨D, hDN⟩ := by
    refine largeEvenInduces_unique
      (largeEvenInduces_mul hdN hbN hdb hDind hBind) ?_
      (conjRel_total (mul_mem hdN hbN))
    have h1 : LargeEvenInduces θ (conjRel (b * d))
        (TableB.projConj (unitarySU 2 q.exponent K (r + 1)) ⟨B, hBN⟩ *
          TableB.projConj (unitarySU 2 q.exponent K (r + 1)) ⟨D, hDN⟩) :=
      largeEvenInduces_mul hbN hdN hdb.symm hBind hDind
    rwa [← hdb] at h1
  obtain ⟨D', B', hD'gu, hB'gu, hD'N, hB'N, hD'p, hB'p, hD'B', hD'proj, hB'proj⟩ :=
    exists_commuting_pow_one_gu_lifts_of_not_shape hfield hN3 hNq hS.prime
      (not_and_or.mp hnot) hDgu hBgu hDN hBN hDpow hBpow hcomm_proj
  have hD'ind : LargeEvenInduces θ (conjRel d)
      (TableB.projConj (unitarySU 2 q.exponent K (r + 1)) ⟨D', hD'N⟩) := by
    rw [hD'proj]
    exact hDind
  have hB'ind : LargeEvenInduces θ (conjRel b)
      (TableB.projConj (unitarySU 2 q.exponent K (r + 1)) ⟨B', hB'N⟩) := by
    rw [hB'proj]
    exact hBind
  exact hUB G p L J A d b (r + 1) q.exponent K hfield hN3 hNq hS θ D' B'
    hD'gu hB'gu hD'N hB'N hD'p hD'B' hD'ind hB'ind

theorem innerCompNonShape_unitary_charTwo_of_block
    (hUB : UniBlockInnDiag) :
    InnerCompNonShape fun i => KD264Lie.isUnitaryIdx i ∧ i.characteristic = 2 :=
  innerCompNonShape_of_W (innerCompNonShapeW_unitary_charTwo_of_block hUB)

end CFSG.LocalAnalysis.GLTheoremA.T171Sh

end
