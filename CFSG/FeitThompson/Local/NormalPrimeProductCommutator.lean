module

public import CFSG.FeitThompson.Foundations.NormalHallContainsPiSubgroups
import CFSG.FeitThompson.Foundations.ProductSubgroupsCardinality
import CFSG.FeitThompson.Local.FrattiniArgumentNormalSylow

open Pointwise

namespace CFSG.FeitThompson

public section

set_option autoImplicit true
set_option maxSynthPendingDepth 3

variable {X : Type*} [Group X]

theorem le_of_subgroupOf_le_subgroupOf {H K L : Subgroup X} (hHL : H ≤ L) (hKL : K ≤ L)
    (h : H.subgroupOf L ≤ K.subgroupOf L) : H ≤ K := by
  have h' := Subgroup.map_subtype_le_map_subtype.2 h
  rwa [Subgroup.map_subgroupOf_eq_of_le hHL, Subgroup.map_subgroupOf_eq_of_le hKL] at h'

theorem isPiSubgroup_compl_singleton_of_coprime {p : ℕ} {K : Subgroup X}
    (hK : (Nat.card K).Coprime p) : IsPiSubgroup {q : ℕ | q.Prime ∧ q ≠ p} K := by
  refine isPiSubgroup_iff.2 fun q hq => ⟨Nat.prime_of_mem_primeFactors hq, fun h => ?_⟩
  subst h
  exact (Nat.prime_of_mem_primeFactors hq).ne_one
    (Nat.Coprime.eq_one_of_dvd (hK.coprime_dvd_left (Nat.dvd_of_mem_primeFactors hq)) dvd_rfl)

theorem natCard_sup_eq_mul_of_coprime {N A : Subgroup X} [N.Normal]
    (h : (Nat.card N).Coprime (Nat.card A)) :
    Nat.card (N ⊔ A : Subgroup X) = Nat.card N * Nat.card A := by
  have hbot : (N ⊓ A : Subgroup X) = ⊥ :=
    disjoint_iff.1 (Subgroup.disjoint_of_coprime_natCard h)
  have key := natCard_mul_mul_natCard_inf N A
  rw [hbot, Subgroup.card_bot, mul_one] at key
  have hset : ((N ⊔ A : Subgroup X) : Set X) = (N : Set X) * (A : Set X) := N.normal_mul A
  calc Nat.card (N ⊔ A : Subgroup X) = Nat.card ((N : Set X) * (A : Set X)) :=
        Nat.card_congr (Set.equivOfEq hset)
    _ = Nat.card N * Nat.card A := key

theorem index_subgroupOf_sup_eq_natCard [Finite X] {N A : Subgroup X} [N.Normal]
    (h : (Nat.card N).Coprime (Nat.card A)) :
    (N.subgroupOf (N ⊔ A)).index = Nat.card A := by
  have hcard := Subgroup.index_mul_card (N.subgroupOf (N ⊔ A : Subgroup X))
  rw [natCard_subgroupOf_of_le (le_sup_left : N ≤ N ⊔ A), natCard_sup_eq_mul_of_coprime h,
    mul_comm (Nat.card N)] at hcard
  exact Nat.eq_of_mul_eq_mul_right Nat.card_pos hcard

theorem isHallPiSubgroup_subgroupOf_sup [Finite X] {N A : Subgroup X} {p n : ℕ} (hp : p.Prime)
    [N.Normal] (hN : (Nat.card N).Coprime p) (hA : Nat.card A = p ^ n) :
    IsHallPiSubgroup {q : ℕ | q.Prime ∧ q ≠ p} (N.subgroupOf (N ⊔ A)) := by
  have hcop : (Nat.card N).Coprime (Nat.card A) := by rw [hA]; exact hN.pow_right n
  refine ⟨isPiSubgroup_compl_singleton_of_coprime (by
    rw [natCard_subgroupOf_of_le (le_sup_left : N ≤ N ⊔ A)]; exact hN), fun q hq => ?_⟩
  rw [index_subgroupOf_sup_eq_natCard hcop, hA, Nat.primeFactors_pow _ (by
    rintro rfl; simp at hq), hp.primeFactors, Finset.mem_singleton] at hq
  simp [hq]

theorem commutator_le_of_sup_normal_of_coprime [Finite X] {N A Y : Subgroup X} {p n : ℕ}
    (hp : p.Prime) [N.Normal] (hN : (Nat.card N).Coprime p) (hA : Nat.card A = p ^ n)
    (hNA : (N ⊔ A : Subgroup X).Normal) (hY : (Nat.card Y).Coprime p)
    (hAY : A ≤ Subgroup.normalizer (Y : Set X)) : ⁅Y, A⁆ ≤ N := by
  have hle : (⁅Y, A⁆ : Subgroup X) ≤ N ⊔ A :=
    (Subgroup.commutator_mono le_rfl (le_sup_right : A ≤ N ⊔ A)).trans
      (Subgroup.commutator_le_right Y (N ⊔ A))
  have hYA : (⁅Y, A⁆ : Subgroup X) ≤ Y := Subgroup.le_normalizer_iff_commutator_le_left.1 hAY
  have hcopC : (Nat.card (⁅Y, A⁆ : Subgroup X)).Coprime p :=
    hY.coprime_dvd_left (Subgroup.card_dvd_of_le hYA)
  have hHall := isHallPiSubgroup_subgroupOf_sup hp hN hA (A := A)
  have hpi : IsPiSubgroup {q : ℕ | q.Prime ∧ q ≠ p}
      ((⁅Y, A⁆ : Subgroup X).subgroupOf (N ⊔ A)) :=
    isPiSubgroup_compl_singleton_of_coprime (by rw [natCard_subgroupOf_of_le hle]; exact hcopC)
  exact le_of_subgroupOf_le_subgroupOf hle le_sup_left (hHall.le_of_isPiSubgroup hpi)

theorem commutator_le_of_sup_normal_of_isPGroup [Finite X] {N A Y : Subgroup X} {p : ℕ}
    (hp : p.Prime) [N.Normal] (hN : (Nat.card N).Coprime p) (hA : IsPGroup p A)
    (hNA : (N ⊔ A : Subgroup X).Normal) (hY : (Nat.card Y).Coprime p)
    (hAY : A ≤ Subgroup.normalizer (Y : Set X)) : ⁅Y, A⁆ ≤ N := by
  have := Fact.mk hp
  obtain ⟨n, hn⟩ := hA.exists_card_eq
  exact commutator_le_of_sup_normal_of_coprime hp hN hn hNA hY hAY

end

end CFSG.FeitThompson
