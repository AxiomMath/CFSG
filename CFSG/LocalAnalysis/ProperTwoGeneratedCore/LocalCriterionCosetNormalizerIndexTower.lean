module

public import CFSG.LocalAnalysis.ProperTwoGeneratedCore.LocalCriterionCosetNormalizerIndexOrbit
public import CFSG.LocalAnalysis.ProperTwoGeneratedCore.LocalCriterionCosetNormalizerIndexFixedOrbit

public section

namespace CFSG.ProperTwoGeneratedCore.LocalCriterionCosetNormalizerIndex

open CFSG.ShultStronglyClosedTI
open CFSG.ProperTwoGeneratedCore.LocalCriterionGeometry
open CFSG.ProperTwoGeneratedCore.LocalCriterionInvariantNormalizer

universe u

variable {G : Type u} [Group G]

theorem normalizer_index_tower (N D : Subgroup G) (u : G)
    (hinter : N ⊓ D = (N ⊓ Subgroup.centralizer ({u} : Set G)) ⊓ D) :
    D.relIndex N = (Subgroup.centralizer ({u} : Set G)).relIndex N *
      D.relIndex (N ⊓ Subgroup.centralizer ({u} : Set G)) := by
  let A : Subgroup G := N ⊓ Subgroup.centralizer ({u} : Set G)
  calc
    _ = (A ⊓ D).relIndex N := by rw [← hinter, Subgroup.inf_relIndex_left]
    _ = (A ⊓ D).relIndex A * A.relIndex N :=
      (Subgroup.relIndex_mul_relIndex (A ⊓ D) A N inf_le_left inf_le_left).symm
    _ = _ := by rw [Subgroup.inf_relIndex_left, Subgroup.inf_relIndex_left, mul_comm]

theorem translated_coset_normalizer_index_from_full_orbits [Finite G]
    {H : Subgroup G} {z u : G} (h : InvolutionPointLocalEmbedding H z)
    (beta : pointRightCosetSpace H) (hbeta : beta ≠ rightCosetMk H 1)
    (huD : u ∈ pairPointStabilizer H beta)
    (hNH : Subgroup.normalizer (translatedCosetUnitSet H z u) ≤ H)
    (hconj : ∀ s ∈ translatedCosetUnitSet H z u,
      ∀ t ∈ translatedCosetUnitSet H z u,
        ∃ n : Subgroup.normalizer (translatedCosetUnitSet H z u),
          CFSG.BenderSuzuki.PFAppendixIII.rightConjugateElem s (n : G) = t)
    (hoffbase : ∀ omega ∈ cosetFixedSet H u, omega ≠ rightCosetMk H 1 →
      ∃ a : ((Subgroup.normalizer (translatedCosetUnitSet H z u) ⊓
        Subgroup.centralizer ({u} : Set G)) : Subgroup G),
          pointRightCosetMul H beta (a : G) = omega) :
    (pairPointStabilizer H beta).relIndex
      (Subgroup.normalizer (translatedCosetUnitSet H z u)) =
        Nat.card (cosetUnitSet H z u) * (Nat.card (cosetFixedSet H u) - 1) := by
  let N : Subgroup G := Subgroup.normalizer (translatedCosetUnitSet H z u)
  let A : Subgroup G := N ⊓ Subgroup.centralizer ({u} : Set G)
  have hA : (pairPointStabilizer H beta).relIndex A = Nat.card (cosetFixedSet H u) - 1 :=
    point_centralizer_index_of_full_offBase_orbit H A (inf_le_left.trans hNH) u
      (pairPointStabilizer_le_point H beta huD) inf_le_right beta hbeta
      ((mem_point_right_stabilizer_iff H beta u).mp huD.2) hoffbase
  rw [normalizer_index_tower N (pairPointStabilizer H beta) u
    (translated_coset_normalizer_intersection h beta hbeta huD)]
  rw [translated_coset_conjugation_index H z u hconj, hA]

theorem q_times_degree_sub_one_twoPower (q k : ℕ)
    (hq : ∃ a : ℕ, q = 2 ^ a) (hk : ∃ i : ℕ, k = q ^ i + 1) :
    ∃ a : ℕ, q * (k - 1) = 2 ^ a := by
  obtain ⟨a, rfl⟩ := hq
  obtain ⟨i, rfl⟩ := hk
  refine ⟨a + a * i, ?_⟩
  rw [Nat.add_sub_cancel, ← pow_mul, ← pow_add]

end CFSG.ProperTwoGeneratedCore.LocalCriterionCosetNormalizerIndex
