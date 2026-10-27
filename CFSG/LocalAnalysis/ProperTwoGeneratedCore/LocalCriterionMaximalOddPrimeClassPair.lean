module

public import CFSG.LocalAnalysis.ProperTwoGeneratedCore.LocalCriterionMaximalOddPrimeClassSylow
public import CFSG.LocalAnalysis.ProperTwoGeneratedCore.LocalCriterionMaximalOddPrimeClassFixedPoints

public noncomputable section

namespace CFSG.ProperTwoGeneratedCore.LocalCriterionMaximalOddPrimeClass

open CFSG.ShultStronglyClosedTI
open CFSG.ProperTwoGeneratedCore.LocalCriterionGeometry
open CFSG.ProperTwoGeneratedCore.LocalCriterionMaximalPrime
open CFSG.ProperTwoGeneratedCore.LocalCriterionInvariantNormalizer

variable {G : Type*} [Group G] [Finite G]

theorem maximal_prime_sylow_pair_normalizer_of_odd_pair_count
    (H : Subgroup G) (p : ℕ) (hp : p.Prime) (hpodd : Odd p)
    (W : Subgroup G) (hW : IsPGroup p W)
    (hmax : ∀ V : Subgroup G, IsPGroup p V → W ≤ V →
      3 ≤ Nat.card (pointFixedSet H V) → V ≤ W)
    (a b : pointFixedSet H W) (hab : a ≠ b)
    (hpair :
      let Y := Subgroup.normalizer (W : Set G)
      letI := pointInvariantSetInverseRightAction H Y (pointFixedSet H W)
        (fun _ hn _ homega => normalizer_preserves_pointFixedSet hn homega)
      ∀ A : Subgroup Y, Odd (Nat.card A) →
        ∀ alpha beta : pointFixedSet H W, alpha ≠ beta →
          (∀ g ∈ A, g • alpha = alpha) → (∀ g ∈ A, g • beta = beta) →
            3 ≤ Nat.card (MulAction.fixedPoints A (pointFixedSet H W))) :
    ∃ P : Sylow p ((rightCosetStabilizer H a.val ⊓ rightCosetStabilizer H b.val) ⊓
        Subgroup.normalizer (W : Set G) : Subgroup G),
      (P : Subgroup ((rightCosetStabilizer H a.val ⊓ rightCosetStabilizer H b.val) ⊓
        Subgroup.normalizer (W : Set G) : Subgroup G)).map
        ((rightCosetStabilizer H a.val ⊓ rightCosetStabilizer H b.val) ⊓
          Subgroup.normalizer (W : Set G)).subtype = W := by
  let : Fact p.Prime := ⟨hp⟩
  let Y := Subgroup.normalizer (W : Set G)
  let D := rightCosetStabilizer H a.val ⊓ rightCosetStabilizer H b.val
  let B := D ⊓ Y
  let := pointInvariantSetInverseRightAction H Y (pointFixedSet H W)
    (fun _ hn _ homega => normalizer_preserves_pointFixedSet hn homega)
  have hWD : W ≤ D := by
    intro w hw
    exact ⟨(mem_point_right_stabilizer_iff H a.val w).mpr (a.property w hw),
      (mem_point_right_stabilizer_iff H b.val w).mpr (b.property w hw)⟩
  have hWB : W ≤ B := le_inf hWD W.le_normalizer
  have hWi : IsPGroup p (W.subgroupOf B) :=
    hW.comap_of_injective B.subtype B.subtype_injective
  obtain ⟨P, hWP⟩ := hWi.exists_le_sylow
  let V := (P : Subgroup B).map B.subtype
  let A : Subgroup Y := (P : Subgroup B).map (Subgroup.inclusion (show B ≤ Y from inf_le_right))
  have hAV : A.map Y.subtype = V := by
    rw [Subgroup.map_map]
    rfl
  have hVD : V ≤ D := (Subgroup.map_subtype_le _).trans inf_le_left
  have hAp : IsPGroup p A := P.isPGroup'.map _
  obtain ⟨k, hk⟩ := hAp.exists_card_eq
  have hAodd : Odd (Nat.card A) := hk ▸ hpodd.pow
  have hfixa : ∀ g ∈ A, g • a = a := by
    intro g hg
    apply Subtype.ext
    change pointRightCosetMul H a.val (g : G)⁻¹ = a.val
    have hmem : (g : G)⁻¹ ∈ V := hAV ▸ Subgroup.mem_map_of_mem Y.subtype (A.inv_mem hg)
    exact (mem_point_right_stabilizer_iff H a.val _).mp (hVD hmem).1
  have hfixb : ∀ g ∈ A, g • b = b := by
    intro g hg
    apply Subtype.ext
    change pointRightCosetMul H b.val (g : G)⁻¹ = b.val
    have hmem : (g : G)⁻¹ ∈ V := hAV ▸ Subgroup.mem_map_of_mem Y.subtype (A.inv_mem hg)
    exact (mem_point_right_stabilizer_iff H b.val _).mp (hVD hmem).2
  have hcount := hpair A hAodd a b hab hfixa hfixb
  have hbridge := restricted_fixed_set_card_le_original H Y (pointFixedSet H W)
    (fun _ hn _ homega => normalizer_preserves_pointFixedSet hn homega) A
  rw [hAV] at hbridge
  have hWV : W ≤ V := by
    rw [← Subgroup.map_subgroupOf_eq_of_le hWB]
    exact Subgroup.map_mono hWP
  have hVW : V ≤ W := hmax V (P.isPGroup'.map B.subtype) hWV (hcount.trans hbridge)
  exact ⟨P, le_antisymm hVW hWV⟩

theorem maximal_prime_sylow_pair_of_odd_pair_count
    (H : Subgroup G) (p : ℕ) (hp : p.Prime) (hpodd : Odd p)
    (W : Subgroup G) (hW : IsPGroup p W)
    (hmax : ∀ V : Subgroup G, IsPGroup p V → W ≤ V →
      3 ≤ Nat.card (pointFixedSet H V) → V ≤ W)
    (a b : pointFixedSet H W) (hab : a ≠ b)
    (hpair :
      let Y := Subgroup.normalizer (W : Set G)
      letI := pointInvariantSetInverseRightAction H Y (pointFixedSet H W)
        (fun _ hn _ homega => normalizer_preserves_pointFixedSet hn homega)
      ∀ A : Subgroup Y, Odd (Nat.card A) →
        ∀ alpha beta : pointFixedSet H W, alpha ≠ beta →
          (∀ g ∈ A, g • alpha = alpha) → (∀ g ∈ A, g • beta = beta) →
            3 ≤ Nat.card (MulAction.fixedPoints A (pointFixedSet H W))) :
    ∃ Q : Sylow p (rightCosetStabilizer H a.val ⊓ rightCosetStabilizer H b.val : Subgroup G),
      (Q : Subgroup (rightCosetStabilizer H a.val ⊓ rightCosetStabilizer H b.val : Subgroup G)).map
        (rightCosetStabilizer H a.val ⊓ rightCosetStabilizer H b.val).subtype = W := by
  apply sylow_of_sylow_normalizer_intersection p hp _ W hW
  · intro w hw
    exact ⟨(mem_point_right_stabilizer_iff H a.val w).mpr (a.property w hw),
      (mem_point_right_stabilizer_iff H b.val w).mpr (b.property w hw)⟩
  · exact maximal_prime_sylow_pair_normalizer_of_odd_pair_count
      H p hp hpodd W hW hmax a b hab hpair

end CFSG.ProperTwoGeneratedCore.LocalCriterionMaximalOddPrimeClass
