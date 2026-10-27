module

public import CFSG.LocalAnalysis.EvenSporadicStandard.Induction.Rows.LieOrders
public import CFSG.LocalAnalysis.EvenSporadicStandard.Solomon78.LocMFacts
public import CFSG.Fischer.Classification.Recognition.PSU6
public import CFSG.LocalAnalysis.ComponentClassification.ClassicalModelStatedBridge

public section

namespace CFSG.EvenSporadicStandard.Induction.Hyp

open Subgroup CFSG.Blueprint CFSG.Blueprint.NativeSporadic CFSG.EvenSporadicStandard.Solomon78
  CFSG.Monster.Existence CFSG.Monster.Existence.Compat CFSG.Open CFSG.EvenSporadicStandard.Induction

@[expose] def BCoverRank : Prop :=
  ∀ (X : Type) [Group X] [Finite X], CFSG.IsQuasisimple X → IsSporadic (X ⧸ center X) .B →
    3 ≤ CFSG.pRank 2 X

structure MonsterInvolutions (Y : Type) [Group Y] : Prop where
  conj : ∀ u v : Y, orderOf u = 2 → orderOf v = 2 →
    2 * monsterBabyOrder ≤ Nat.card ↥(centralizer ({u} : Set Y)) →
    2 * monsterBabyOrder ≤ Nat.card ↥(centralizer ({v} : Set Y)) → IsConj u v
  small : ∀ t : Y, orderOf t = 2 →
    2 * monsterBabyOrder ≤ Nat.card ↥(centralizer ({t} : Set Y)) ∨
      ¬ 17 ∣ Nat.card ↥(centralizer ({t} : Set Y))

theorem card_centralizer_of_isTwoACentralizer' {X : Type} [Group X] {a : X} (ha : orderOf a = 2)
    (h : IsTwoACentralizer a) (hB : Nat.card NativeSporadic.B = monsterBabyOrder) :
    Nat.card ↥(centralizer ({a} : Set X)) = 2 * monsterBabyOrder := by
  obtain ⟨-, hz, ⟨e⟩⟩ := h
  have h1 := Subgroup.card_eq_card_quotient_mul_card_subgroup
    (center ↥(centralizer ({a} : Set X)))
  have hc : Nat.card ↥(center ↥(centralizer ({a} : Set X))) = 2 := by
    rw [← Subgroup.card_map_of_injective (centralizer ({a} : Set X)).subtype_injective, hz,
      Nat.card_zpowers, ha]
  rw [Nat.card_congr e.toEquiv, hB, hc] at h1
  omega

theorem twoBCentralizerOrder_lt : twoBCentralizerOrder < 2 * monsterBabyOrder := by
  unfold twoBCentralizerOrder monsterBabyOrder
  norm_num

theorem monsterInvolutions_of_existence {X : Type} [Group X] (h : MonsterExistenceStatement X)
    (hB : Nat.card NativeSporadic.B = monsterBabyOrder) : MonsterInvolutions X := by
  obtain ⟨-, a, z, ha, hz, hnc, hinv, hA, hBz, -⟩ := h
  have hbig : ∀ u : X, orderOf u = 2 → 2 * monsterBabyOrder ≤ Nat.card ↥(centralizer ({u} : Set X))
      → IsConj a u := by
    intro u hu hge
    rcases hinv u hu with h1 | h1
    · exact h1
    · exfalso
      have h2 := (hBz u h1).2.2.2.2.1
      rw [show Nat.card ↥(centralizer ({u} : Set X)) = twoBCentralizerOrder from h2] at hge
      exact absurd hge (not_le.2 twoBCentralizerOrder_lt)
  refine ⟨fun u v hu hv hgu hgv => ?_, fun t ht => ?_⟩
  · exact (hbig u hu hgu).symm.trans (hbig v hv hgv)
  · rcases hinv t ht with h1 | h1
    · left
      have := card_centralizer_of_isTwoACentralizer' ht (hA t h1) hB
      exact this.ge
    · right
      exact (hBz t h1).2.2.2.2.2

theorem MonsterInvolutions.of_mulEquiv {Y X : Type} [Group Y] [Group X] (φ : Y ≃* X)
    (h : MonsterInvolutions X) : MonsterInvolutions Y := by
  refine ⟨fun u v hu hv hgu hgv => ?_, fun t ht => ?_⟩
  · have hu' : orderOf (φ u) = 2 := by rw [MulEquiv.orderOf_eq]; exact hu
    have hv' : orderOf (φ v) = 2 := by rw [MulEquiv.orderOf_eq]; exact hv
    have hc := h.conj (φ u) (φ v) hu' hv' (by rw [card_centralizer_map]; exact hgu)
      (by rw [card_centralizer_map]; exact hgv)
    obtain ⟨c, hc⟩ := isConj_iff.1 hc
    refine isConj_iff.2 ⟨φ.symm c, φ.injective ?_⟩
    simpa using hc
  · have ht' : orderOf (φ t) = 2 := by rw [MulEquiv.orderOf_eq]; exact ht
    rcases h.small (φ t) ht' with h1 | h1
    · left
      rwa [card_centralizer_map] at h1
    · right
      rwa [card_centralizer_map] at h1

end CFSG.EvenSporadicStandard.Induction.Hyp
