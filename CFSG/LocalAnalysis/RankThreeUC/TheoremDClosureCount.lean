module

public import CFSG.LocalAnalysis.RankThreeUC.TheoremDStrongOrbit

public section

namespace CFSG.LocalAnalysis.RankThreeUC

open CFSG.Open CFSG.RankThreeCoreUniqueness.Helpers Subgroup
open CFSG.RankThree.PartOne (IsStronglyPEmbedded)

variable {G : Type} [Group G] [Finite G]

namespace IsWitness

variable {p : ℕ} {P : Sylow p G} {M : Subgroup G}

theorem _root_.CFSG.LocalAnalysis.RankThreeUC.IsWitnessGen.normalizer_le_of_ncard_lt
    (hw : IsWitnessGen p P M)
    (hSE : IsStronglyPEmbedded p M) {T V : Subgroup G} (hV : IsElemAbelian 2 V)
    (hNV : normalizer (T : Set G) ≤ normalizer (V : Set G))
    (hcard : ({a | a ∈ V ∧ a ≠ 1 ∧ ¬ p ∣ Nat.card ↥(M ⊓ centralizer ({a} : Set G))} :
        Set G).ncard <
      ({a | a ∈ V ∧ a ≠ 1 ∧ 2 ≤ CFSG.Open.pRank p (M ⊓ centralizer ({a} : Set G))} :
        Set G).ncard) :
    normalizer (T : Set G) ≤ M := by
  intro n hn
  by_contra hnM
  refine absurd hcard (not_lt.mpr ?_)
  refine Set.ncard_le_ncard_of_injOn (fun a => n * a * n⁻¹) ?_ ?_ (Set.toFinite _)
  · rintro a ⟨haV, ha1, hag⟩
    refine ⟨(mem_normalizer_iff.mp (hNV hn) a).mp haV, ?_, ?_⟩
    · intro h
      exact ha1 (by simpa using h)
    · exact hw.not_dvd_card_inf_centralizer_conj hSE ha1 (hV.2 a haV) hag hnM
  · intro a _ b _ hab
    simpa using hab

end IsWitness

end CFSG.LocalAnalysis.RankThreeUC
