module

public import CFSG.LocalAnalysis.EvenSporadicStandard.Co3Std.CentT.Co3Cent
public import CFSG.LocalAnalysis.EvenSporadicStandard.Common.Basic

public section

namespace CFSG.EvenSporadicStandard.Co3Std.CentT

open Subgroup CFSG.Sporadic.Schreier.Co3 CFSG.Blueprint CFSG.Blueprint.NativeSporadic

section Certified


theorem centFacts_of_split {G : Type} [Group G] [Finite G] {C : Subgroup G} {w : G}
    (hw2 : w * w = 1) (hw1 : w ≠ 1) (hwC : C ≤ centralizer ({w} : Set G))
    (hCw : Disjoint C (zpowers w))
    (h : Nonempty (↥C ≃* ↥co3M) ∨
      ∃ N : Subgroup G, N ≤ C ∧ (∀ c ∈ C, ∀ n ∈ N, c * n * c⁻¹ ∈ N) ∧
        Nonempty (↥N ≃* ↥NativeSporadic.M12) ∧ Nat.card ↥C = 2 * 95040) :
    CentFacts ↥(C ⊔ zpowers w) := by
  have hwC' : w ∈ centralizer (C : Set G) :=
    mem_centralizer_iff.2 fun c hc => mem_centralizer_singleton_iff.1 (hwC hc)
  have hw_ord : orderOf w = 2 := by
    haveI : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
    exact orderOf_eq_prime (by rw [pow_two]; exact hw2) hw1
  have hcard : Nat.card ↥(C ⊔ zpowers w) = 2 * Nat.card ↥C := by
    rw [← Nat.card_congr (CFSG.EvenSporadicStandard.mulEquivProdSup (A := C) (B := zpowers w)
      (Subgroup.zpowers_le.2 hwC') hCw).toEquiv, Nat.card_prod, Nat.card_zpowers, hw_ord,
      mul_comm]
  rcases h with hA | ⟨N, hNC, hNnorm, hM12, hCcard⟩
  ·
    have eC : ↥C ≃* ↥co3M := Classical.choice hA
    haveI : (C.subgroupOf (C ⊔ zpowers w)).Normal :=
      (Subgroup.normal_subgroupOf_iff_le_normalizer le_sup_left).2
        (sup_le Subgroup.le_normalizer
          (Subgroup.zpowers_le.2 ((Subgroup.centralizer_le_normalizer (C : Set G)) hwC')))
    refine centFacts_of_typeA (D := ↥(C ⊔ zpowers w))
      (N := C.subgroupOf (C ⊔ zpowers w))
      ((Subgroup.subgroupOfEquivOfLe le_sup_left).trans eC) ?_
    rw [hcard, Nat.card_congr eC.toEquiv, card_co3M]
  ·
    have eN : ↥N ≃* ↥NativeSporadic.M12 := Classical.choice hM12
    have hNle : N ≤ C ⊔ zpowers w := hNC.trans le_sup_left
    haveI : (N.subgroupOf (C ⊔ zpowers w)).Normal :=
      (Subgroup.normal_subgroupOf_iff_le_normalizer hNle).2
        (sup_le (Subgroup.le_normalizer_iff.2 hNnorm)
          (Subgroup.zpowers_le.2
            ((Subgroup.centralizer_le_normalizer (N : Set G))
              (mem_centralizer_iff.2 fun n hn =>
                mem_centralizer_singleton_iff.1 (hwC (hNC hn))))))
    refine centFacts_of_typeB (D := ↥(C ⊔ zpowers w))
      (N := N.subgroupOf (C ⊔ zpowers w))
      ((Subgroup.subgroupOfEquivOfLe hNle).trans eN) ?_
    rw [hcard]
    omega

end Certified

end CFSG.EvenSporadicStandard.Co3Std.CentT
