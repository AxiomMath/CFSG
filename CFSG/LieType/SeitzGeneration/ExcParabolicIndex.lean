module

public import CFSG.LieType.SeitzGeneration.ExcParabolicCard
public import CFSG.Timmesfeld.Orders.ExceptionalWeylData

public section

namespace CFSG.LieType.SeitzGeneration

open CFSG.LieType.Chevalley CFSG.Blueprint.Chevalley CFSG.Timmesfeld.ExceptionalOrders

theorem e6Chain_tail_check : chainCheck e6Chain.tail 31 = true := by
  have h := e6Chain_check
  change (_ && _ && chainCheck e6Chain.tail 31) = true at h
  exact (Bool.and_eq_true_iff.1 h).2

theorem e7Chain_tail_check : chainCheck e7Chain.tail 63 = true := by
  have h := e7Chain_check
  change (_ && _ && chainCheck e7Chain.tail 63) = true at h
  exact (Bool.and_eq_true_iff.1 h).2

theorem maskSet_E6_ne_univ : (maskSet .E6 31 : Set (Fin Tag.E6.rank)) ≠ Set.univ := by
  intro h
  have h5 : (⟨5, by decide⟩ : Fin Tag.E6.rank) ∈ (maskSet .E6 31 : Set (Fin Tag.E6.rank)) := by
    rw [h]
    exact Set.mem_univ _
  exact absurd (mem_maskSet.1 (Finset.mem_coe.1 h5)) (by decide)

theorem maskSet_E7_ne_univ : (maskSet .E7 63 : Set (Fin Tag.E7.rank)) ≠ Set.univ := by
  intro h
  have h6 : (⟨6, by decide⟩ : Fin Tag.E7.rank) ∈ (maskSet .E7 63 : Set (Fin Tag.E7.rank)) := by
    rw [h]
    exact Set.mem_univ _
  exact absurd (mem_maskSet.1 (Finset.mem_coe.1 h6)) (by decide)

section Index


theorem parabolicSum_E6_univ [Fintype (WeylGroup .E6)] (q : ℕ) :
    parabolicSum .E6 Set.univ q =
      parabolicSum .E6 (maskSet .E6 31) q * (geomSum 9 1 q * geomSum 3 4 q) := by
  have h63 := parabolicSum_eq_of_chainCheck q _ _ e6Chain_check
  have h31 := parabolicSum_eq_of_chainCheck q _ _ e6Chain_tail_check
  rw [maskSet_full (m := 63) (by decide)] at h63
  rw [h63, h31]
  simp only [e6Chain, ChainStep.value, List.tail_cons, List.map_cons, List.map_nil,
    List.prod_cons, List.prod_nil]
  ring

theorem parabolicSum_E7_univ [Fintype (WeylGroup .E7)] (q : ℕ) :
    parabolicSum .E7 Set.univ q = parabolicSum .E7 (maskSet .E7 63) q *
      (geomSum 2 5 q * geomSum 2 9 q * geomSum 14 1 q) := by
  have h127 := parabolicSum_eq_of_chainCheck q _ _ e7Chain_check
  have h63 := parabolicSum_eq_of_chainCheck q _ _ e7Chain_tail_check
  rw [maskSet_full (m := 127) (by decide)] at h127
  rw [h127, h63]
  simp only [e7Chain, ChainStep.value, List.tail_cons, List.map_cons, List.map_nil,
    List.prod_cons, List.prod_nil]
  ring

end Index

section RelIndex

variable {K : Type} [Field K] [Finite K]

theorem relIndex_parabolicSubgroup_E6 [Fintype (WeylGroup .E6)] :
    (parabolicSubgroup .E6 K (maskSet .E6 31)).relIndex (adjointGroup .E6 K) =
      geomSum 9 1 (Nat.card K) * geomSum 3 4 (Nat.card K) := by
  have h := parabolicSum_univ_eq_mul_index (τ := .E6) (K := K) (maskSet .E6 31)
  rw [parabolicSum_E6_univ] at h
  exact (Nat.eq_of_mul_eq_mul_left (parabolicSum_pos _ Nat.card_pos) h).symm

theorem relIndex_parabolicSubgroup_E7 [Fintype (WeylGroup .E7)] :
    (parabolicSubgroup .E7 K (maskSet .E7 63)).relIndex (adjointGroup .E7 K) =
      geomSum 2 5 (Nat.card K) * geomSum 2 9 (Nat.card K) * geomSum 14 1 (Nat.card K) := by
  have h := parabolicSum_univ_eq_mul_index (τ := .E7) (K := K) (maskSet .E7 63)
  rw [parabolicSum_E7_univ] at h
  exact (Nat.eq_of_mul_eq_mul_left (parabolicSum_pos _ Nat.card_pos) h).symm

end RelIndex

end CFSG.LieType.SeitzGeneration
