module

public import CFSG.LocalAnalysis.ComponentClassification.GrSLitL34Sec4KSwSwitch
public import CFSG.LocalAnalysis.ComponentClassification.GrSLitSingleSFLZOneR
import CFSG.LocalAnalysis.ComponentClassification.GrSLitL34Sec4DiagMem
import CFSG.LocalAnalysis.ComponentClassification.GrSLitSingleSFL
import CFSG.LocalAnalysis.ComponentClassification.GrSLitSingleRank
public import Certificates.Kernel.ThCent.Leaves

public section

namespace CFSG.ComponentClassification.GrSLit

open CFSG Subgroup CFSG.ComponentClassification.UnbalancedLayer
  CFSG.ComponentClassification.UnbalancedCorr CFSG.ComponentClassification.UnbalancedGS GrS4
open CFSG.LocalAnalysis.ComponentInitial (SchreierFor)

@[expose] def L34Lemma43KSylowMemStep : Prop :=
  ∀ (G : Type) [Group G] [Finite G] (a x : G) (J S A : Subgroup G), L34Sec4Setting G a x J S →
    (∀ s ∈ S, s * a = a * s) → L34Sec4Running J A → IsThreeConnected (S ⊓ withKernel J) →
    S ⊓ zStarIn J ≠ ⊥ → a ∈ S ⊓ zStarIn J →
    ∀ W : Subgroup G, W ≠ ⊥ → Odd (Nat.card W) →
      (∀ B : Subgroup G, B ≤ S ⊓ withKernel J → IsAbelianTwoOfRank 3 B → wGroup B = W) →
      normalizer (J : Set G) ≤ normalizer (W : Set G) →
      ∀ K : Subgroup G, K ≤ normalizer (W : Set G) →
        IsPComponent 2 (K.subgroupOf (normalizer (W : Set G))) →
        IsL34Type (K ⧸ Open.fusionZStar K) →
        J ⊔ oddIn (normalizer (W : Set G)) = K ⊔ oddIn (normalizer (W : Set G)) →
        normalizer (W : Set G) ≤ normalizer (K : Set G) →
        IsSylowTwoIn S (normalizer (W : Set G))

theorem l34Lemma43KSylowStep_of_zOne
    (hMax : MaximalTwoComponentInput)
    (hS : SchreierFor Blueprint.Catalog) (hFixL : SolomonFixedLayerStep)
    (hHS : RankThree.PartTwo.Sec21.HoltUniqueFixedPointSimple) (hZ1 : L34Lemma43ZOneStep)
    (hMem : L34Lemma43KSylowMemStep) : L34Lemma43KSylowStep := by
  intro G _ _ a x J S A hset hcent hZ hrun h3 W hW hWodd hWB hNJ K hKM hKc hKL hcase
  obtain ⟨hbase, hU3, hL34, hmax, -, -, -⟩ := id hset
  obtain ⟨hsimple, hnab, hK, -, hUo, -, -, -⟩ := hbase
  have : IsSimpleGroup G := hsimple
  have ha2 : orderOf a = 2 := hU3.1
  have hJa : J ≤ centralizer ({a} : Set G) := hU3.2.2.2.1
  have hJc := hU3.2.2.2.2.1
  set M : Subgroup G := normalizer (W : Set G) with hM
  have hgs : GSMaximalSetting G a J := ⟨hsimple, hnab, hK, hUo, ha2, hJa, hJc,
    hmax, GrS5.three_le_pRank_of_l34 hL34, Sol78.not_psp4_of_l34 hL34, Or.inl ⟨hL34, hset.1⟩⟩
  have hMtop : M ≠ ⊤ := normalizer_ne_top_of_odd hW hWodd ha2
  have hCaM : centralizer ({a} : Set G) ≤ M :=
    (centralizer_le_normalizer_of_gsMaximalSetting hMax hgs).trans hNJ
  have haM : a ∈ M := hCaM (mem_centralizer_singleton_iff.mpr rfl)
  have hKN : M ≤ normalizer (K : Set G) := by
    by_cases hZ1' : S ⊓ zStarIn J = ⊥
    · exact hZ1 G a x J S A hset hcent hrun h3 hZ1' W hW hWodd hWB hNJ K hKM hKc hKL hcase
    · have haJ : a ∈ J := (map_subtype_le _ : zStarIn J ≤ J) (mem_inf.mp (hZ hZ1')).2
      rcases hcase with hsup | ⟨hKa, hJKK⟩
      · have hsc : SingleComponentSetting G a J W K :=
          { toGSMaximalSetting := hgs, ne_bot := hW, odd_card := hWodd, normalizer_le := hNJ,
            normalizer_ne_top := hMtop, le_normalizer := hKM, isPComponent_K := hKc,
            sup_eq := hsup }
        exact Single.normalizer_le_of_mem hMax hFixL hsc hL34 hset.1 haJ
      · exact (diagonal_false_of_mem hKM hKc haM hKa hJKK haJ).elim
  refine ⟨hKN, ?_⟩
  have hsup : J ⊔ oddIn M = K ⊔ oddIn M := by
    rcases hcase with hsup | ⟨hKa, -⟩
    · exact hsup
    · exact (hKa (Single.conjugate_eq_of_mem_normalizer (hKN haM))).elim
  by_cases hZ1' : S ⊓ zStarIn J = ⊥
  · exact (KSw.false_of_zOne_normal hMax hS hHS hset hZ1' hW hWodd hWB hNJ hKM hKc hsup
      hKN).elim
  · exact hMem G a x J S A hset hcent hrun h3 hZ1' (hZ hZ1') W hW hWodd hWB hNJ K hKM hKc hKL
      hsup hKN

theorem l34KSylowStep_of_zOne
    (hMax : MaximalTwoComponentInput)
    (hS : SchreierFor Blueprint.Catalog) (hFixL : SolomonFixedLayerStep)
    (hHS : RankThree.PartTwo.Sec21.HoltUniqueFixedPointSimple)
    (hZ1R : L34Lemma43ZOneResidue) (hMem : L34Lemma43KSylowMemStep)
    (hF46 : L34Lemma46FrattiniStep) : L34KSylowStep :=
  ⟨l34Lemma43KSylowStep_of_zOne hMax hS hFixL hHS
    (l34Lemma43ZOneStep_of_residue hMax hFixL hZ1R) hMem, hF46⟩

@[expose] def L34KSylowRestStep : Prop := L34Lemma43KSylowMemStep ∧ L34Lemma46FrattiniStep

theorem l34KSylowStep_of_rest
    (hMax : MaximalTwoComponentInput)
    (hS : SchreierFor Blueprint.Catalog) (hFixL : SolomonFixedLayerStep)
    (hHS : RankThree.PartTwo.Sec21.HoltUniqueFixedPointSimple)
    (hZ1R : L34Lemma43ZOneResidue) (hR : L34KSylowRestStep) : L34KSylowStep :=
  l34KSylowStep_of_zOne hMax hS hFixL hHS hZ1R hR.1 hR.2

end CFSG.ComponentClassification.GrSLit
