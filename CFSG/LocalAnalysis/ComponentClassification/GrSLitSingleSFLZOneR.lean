module

public import CFSG.LocalAnalysis.ComponentClassification.GrSLitSingleSFLZOne
public import CFSG.LocalAnalysis.ComponentClassification.GrSLitSingleSFLZOneRConj
public import CFSG.LocalAnalysis.ComponentClassification.GrSLitSingleSFLZOneRDiag
public import Certificates.Kernel.ThCent.Leaves

public section

namespace CFSG.ComponentClassification.GrSLit

open CFSG Subgroup CFSG.ComponentClassification.UnbalancedLayer
  CFSG.ComponentClassification.UnbalancedCorr CFSG.ComponentClassification.UnbalancedGS GrS4

@[expose] def L34Lemma43ZOneResidue : Prop :=
  ∀ (G : Type) [Group G] [Finite G] (a x : G) (J S A : Subgroup G), L34Sec4Setting G a x J S →
    (∀ s ∈ S, s * a = a * s) → L34Sec4Running J A → IsThreeConnected (S ⊓ withKernel J) →
    S ⊓ zStarIn J = ⊥ →
    ∀ W : Subgroup G, W ≠ ⊥ → Odd (Nat.card W) →
      (∀ B : Subgroup G, B ≤ S ⊓ withKernel J → IsAbelianTwoOfRank 3 B → wGroup B = W) →
      normalizer (J : Set G) ≤ normalizer (W : Set G) →
      ∀ K : Subgroup G, K ≤ normalizer (W : Set G) →
        IsPComponent 2 (K.subgroupOf (normalizer (W : Set G))) →
        IsL34Type (K ⧸ Open.fusionZStar K) →
        ((J ⊔ oddIn (normalizer (W : Set G)) = K ⊔ oddIn (normalizer (W : Set G)) ∧
            ∀ g ∈ normalizer (W : Set G), g⁻¹ * a * g ∈ coreActionKernel K →
              Odd (orderOf (a * (g⁻¹ * a * g) * (a * (g⁻¹ * a * g)))) →
                g ∈ normalizer (K : Set G)) ∨
          (conjugate K a ≠ K ∧ J ≤ K ⊔ conjugate K a ⊔ oddIn (normalizer (W : Set G)) ∧
            ∀ T : Subgroup G, T ≤ centralizer (J : Set G) → IsPGroup 2 T → Nat.card T < 4)) →
        normalizer (W : Set G) ≤ normalizer (K : Set G)

theorem l34Lemma43ZOneStep_of_residue
    (hMax : MaximalTwoComponentInput) (hFixL : SolomonFixedLayerStep)
    (hR : L34Lemma43ZOneResidue) : L34Lemma43ZOneStep := by
  intro G _ _ a x J S A hset hcent hrun h3c hZ1 W hW hWodd hWB hNJ K hKM hKc hKL hcase
  obtain ⟨hbase, hU3, hL34, hmax, -, -, -⟩ := id hset
  obtain ⟨hsimple, hnab, hK, -, hUo, -, -, -⟩ := hbase
  have : IsSimpleGroup G := hsimple
  have ha2 : orderOf a = 2 := hU3.1
  have hJa : J ≤ centralizer ({a} : Set G) := hU3.2.2.2.1
  have hJc := hU3.2.2.2.2.1
  have hgs : GSMaximalSetting G a J := ⟨hsimple, hnab, hK, hUo, ha2, hJa, hJc,
    hmax, GrS5.three_le_pRank_of_l34 hL34, Sol78.not_psp4_of_l34 hL34, Or.inl ⟨hL34, hset.1⟩⟩
  have hMtop : normalizer (W : Set G) ≠ ⊤ := normalizer_ne_top_of_odd hW hWodd ha2
  refine hR G a x J S A hset hcent hrun h3c hZ1 W hW hWodd hWB hNJ K hKM hKc hKL ?_
  rcases hcase with hsup | ⟨hKa, hJKK⟩
  · have hsc : SingleComponentSetting G a J W K :=
      { toGSMaximalSetting := hgs, ne_bot := hW, odd_card := hWodd, normalizer_le := hNJ,
        normalizer_ne_top := hMtop, le_normalizer := hKM, isPComponent_K := hKc, sup_eq := hsup }
    refine Or.inl ⟨hsup, fun g hg hb hodd => ?_⟩
    by_contra hgN
    exact Single.false_of_conj_mem_coreActionKernel hMax hFixL hsc hL34 hset.1 hg
      (fun h => hgN (UnbalancedLayer.mem_normalizer_of_conjugate_eq h)) hb hodd
  · refine Or.inr ⟨hKa, hJKK, fun T hTC hT2 => ?_⟩
    by_contra h4
    exact Single.diagonal_false_of_two_subgroup hMax hgs hNJ hKM hKc hKa hJKK hTC hT2
      (not_lt.mp h4)

theorem l34Lemma43ZOneResidue_of_step (h : L34Lemma43ZOneStep) : L34Lemma43ZOneResidue :=
  fun G _ _ a x J S A hset hcent hrun h3 hZ1 W hW hWodd hWB hNJ K hKM hKc hKL hcase =>
    h G a x J S A hset hcent hrun h3 hZ1 W hW hWodd hWB hNJ K hKM hKc hKL
      (hcase.imp (fun h => h.1) (fun h => ⟨h.1, h.2.1⟩))

end CFSG.ComponentClassification.GrSLit
