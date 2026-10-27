module

public import CFSG.Assembly.Defs
public import CFSG.Open.FusionDefs
public import CFSG.Open.UniquenessCaseRankThreeMilestoneDefs
public import CFSG.Open.UniquenessExclusionRankFourMilestoneDefs
public import CFSG.Open.AschbacherProperTwoGeneratedCoreMilestoneDefs
public import CFSG.LocalAnalysis.SectionRank.SQT
public import CFSG.LocalAnalysis.RankThreeCoreUniqueness.CoprimeQuotientRank
import CFSG.LocalAnalysis.ProperTwoGeneratedCore.NormalizerClosure

public section

namespace CFSG.Foundations.SteinbergCA

theorem pRank_coe_eq_open_pRank {X : Type*} [Group X] [Finite X] {p : ℕ} (hp : p.Prime)
    (Q : Subgroup X) : CFSG.pRank p Q = CFSG.Open.pRank p Q := by
  rw [CFSG.SectionRank.pRank_eq_open_pRank_top,
    ← CFSG.RankThreeCoreUniqueness.Helpers.pRank_subgroup_eq_internal_top p hp.one_lt]

theorem kGeneratedPCore_eq {X : Type*} [Group X] [Finite X] {p : ℕ} (hp : p.Prime) (k : ℕ)
    (P : Subgroup X) :
    CFSG.Open.rankThreeGamma k p P = Subgroup.closure
        (⋃ (Q : Subgroup X) (_ : Q ≤ P ∧ k ≤ CFSG.pRank p Q),
          (Subgroup.normalizer (Q : Set X) : Set X)) ∧
      ((∀ Q : Subgroup X, Q ≤ P → CFSG.pRank p Q < k) → CFSG.Open.rankThreeGamma k p P = ⊥) ∧
      CFSG.Open.uniqueThreeGamma k p P = CFSG.Open.rankThreeGamma k p P ∧
      CFSG.Open.uniqueFourGamma p P = CFSG.Open.rankThreeGamma 2 p P ∧
      CFSG.Open.properTwoGenCoreGamma P k = CFSG.Open.rankThreeGamma k 2 P := by
  unfold CFSG.Open.rankThreeGamma CFSG.Open.GLBCore
  refine ⟨?_, fun h => ?_, rfl, rfl, ?_⟩
  · apply le_antisymm
    · refine sSup_le fun N hN => ?_
      obtain ⟨Q, hQP, hQk, rfl⟩ := hN
      intro x hx
      refine Subgroup.subset_closure (Set.mem_iUnion₂.mpr ⟨Q, ⟨hQP, ?_⟩, hx⟩)
      rwa [pRank_coe_eq_open_pRank hp]
    · rw [Subgroup.closure_le]
      intro x hx
      obtain ⟨Q, ⟨hQP, hQk⟩, hxQ⟩ := Set.mem_iUnion₂.mp hx
      rw [pRank_coe_eq_open_pRank hp] at hQk
      refine Subgroup.mem_sSup_of_mem ?_ hxQ
      exact ⟨Q, hQP, hQk, rfl⟩
  · refine le_antisymm (sSup_le fun N hN => ?_) bot_le
    obtain ⟨Q, hQP, hQk, -⟩ := hN
    rw [← pRank_coe_eq_open_pRank hp] at hQk
    exact absurd hQk (not_le.mpr (h Q hQP))
  · exact CFSG.ProperTwoGeneratedCore.gamma_eq_rankThreeGamma P k

theorem oddCoreCenterPreimage_eq (X : Type*) [Group X] :
    CFSG.Open.fusionOddCore X = CFSG.oddCore X ∧
      CFSG.Assembly.oddCore X = CFSG.oddCore X ∧
      CFSG.Open.fusionZStar X =
        (Subgroup.center (X ⧸ CFSG.oddCore X)).comap (QuotientGroup.mk' (CFSG.oddCore X)) ∧
      ∀ x : X, x ∈ CFSG.Open.fusionZStar X ↔
        (QuotientGroup.mk x : X ⧸ CFSG.oddCore X) ∈ Subgroup.center (X ⧸ CFSG.oddCore X) :=
  ⟨rfl, rfl, rfl, fun _ => Iff.rfl⟩

theorem semidihedralGroup_presentation (n : ℕ) :
    CFSG.Open.semidihedralRels n =
        ({FreeGroup.of 0 ^ (2 ^ (n - 1)), FreeGroup.of 1 ^ 2,
          FreeGroup.of 1 * FreeGroup.of 0 * (FreeGroup.of 1)⁻¹ *
            (FreeGroup.of 0 ^ (2 ^ (n - 2) - 1))⁻¹} : Set (FreeGroup (Fin 2))) ∧
      (PresentedGroup.of 0 : CFSG.Open.SemidihedralGroup n) ^ (2 ^ (n - 1)) = 1 ∧
      (PresentedGroup.of 1 : CFSG.Open.SemidihedralGroup n) ^ 2 = 1 ∧
      (PresentedGroup.of 1 * PresentedGroup.of 0 * (PresentedGroup.of 1)⁻¹ :
        CFSG.Open.SemidihedralGroup n) = PresentedGroup.of 0 ^ (2 ^ (n - 2) - 1) ∧
      ∀ {H : Type} [Group H] (a b : H), a ^ (2 ^ (n - 1)) = 1 → b ^ 2 = 1 →
        b * a * b⁻¹ = a ^ (2 ^ (n - 2) - 1) →
        ∃! φ : CFSG.Open.SemidihedralGroup n →* H,
          φ (PresentedGroup.of 0) = a ∧ φ (PresentedGroup.of 1) = b := by
  have hof : ∀ i : Fin 2, (PresentedGroup.of i : CFSG.Open.SemidihedralGroup n) =
      PresentedGroup.mk _ (FreeGroup.of i) := fun _ => rfl
  have hmem1 : FreeGroup.of 0 ^ (2 ^ (n - 1)) ∈ CFSG.Open.semidihedralRels n :=
    Set.mem_insert _ _
  have hmem2 : FreeGroup.of 1 ^ 2 ∈ CFSG.Open.semidihedralRels n :=
    Set.mem_insert_of_mem _ (Set.mem_insert _ _)
  have hmem3 : FreeGroup.of 1 * FreeGroup.of 0 * (FreeGroup.of 1)⁻¹ *
      (FreeGroup.of 0 ^ (2 ^ (n - 2) - 1))⁻¹ ∈ CFSG.Open.semidihedralRels n :=
    Set.mem_insert_of_mem _ (Set.mem_insert_of_mem _ rfl)
  refine ⟨rfl, ?_, ?_, ?_, fun {H} _ a b ha hb hab => ?_⟩
  · rw [hof, ← map_pow]
    exact PresentedGroup.one_of_mem hmem1
  · rw [hof, ← map_pow]
    exact PresentedGroup.one_of_mem hmem2
  · have h := PresentedGroup.one_of_mem hmem3
    rw [map_mul, map_inv, map_mul, map_mul, map_inv, map_pow] at h
    rw [hof, hof]
    exact mul_inv_eq_one.mp h
  · have hrels : ∀ r ∈ CFSG.Open.semidihedralRels n, FreeGroup.lift ![a, b] r = 1 := by
      rintro r (rfl | rfl | rfl)
      · simpa using ha
      · simpa using hb
      · simp only [map_mul, map_inv, map_pow, FreeGroup.lift_apply_of, Matrix.cons_val_zero,
          Matrix.cons_val_one, Matrix.cons_val_fin_one]
        rw [hab, mul_inv_cancel]
    refine ⟨PresentedGroup.toGroup hrels, ⟨?_, ?_⟩, fun ψ hψ => ?_⟩
    · exact (PresentedGroup.toGroup.of hrels).trans (by simp)
    · exact (PresentedGroup.toGroup.of hrels).trans (by simp)
    · apply PresentedGroup.ext
      intro i
      fin_cases i
      · exact hψ.1.trans ((PresentedGroup.toGroup.of hrels).trans (by simp)).symm
      · exact hψ.2.trans ((PresentedGroup.toGroup.of hrels).trans (by simp)).symm

end CFSG.Foundations.SteinbergCA
