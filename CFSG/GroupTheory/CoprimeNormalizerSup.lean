module

public import CFSG.GroupTheory.WielandtProductAux

public section

namespace CFSG.GroupTheory

open Subgroup

theorem le_of_le_sup_of_isPGroup_of_not_dvd_card {X : Type*} [Group X] [Finite X]
    {p : ℕ} (hp : p.Prime) {K C Q : Subgroup X}
    (hC : C ≤ Subgroup.normalizer (K : Set X)) (hQ : IsPGroup p Q)
    (hQKC : Q ≤ K ⊔ C) (hcop : ¬ p ∣ Nat.card C) : Q ≤ K := by
  classical
  haveI : Fact p.Prime := ⟨hp⟩
  set A : Subgroup X := K ⊔ C with hA
  have hKA : K ≤ A := le_sup_left
  have hCA : C ≤ A := le_sup_right
  have hKA_norm : A ≤ Subgroup.normalizer (K : Set X) := sup_le Subgroup.le_normalizer hC
  have hKnormal : (K.subgroupOf A).Normal :=
    (Subgroup.normal_subgroupOf_iff_le_normalizer hKA).mpr hKA_norm
  have hQ' : IsPGroup p (Q.subgroupOf A) := by
    have h : Q.subgroupOf A = Subgroup.comap A.subtype Q := by rw [Subgroup.comap_subtype]
    rw [h]
    exact hQ.comap_subtype
  have htop : (C.subgroupOf A) ⊔ (K.subgroupOf A) = ⊤ := by
    rw [← Subgroup.subgroupOf_sup hCA hKA, sup_comm, hA, Subgroup.subgroupOf_self]
  have hindex : (K.subgroupOf A).index = K.relIndex C := by
    rw [← Subgroup.relIndex_top_right (K.subgroupOf A), ← htop,
      Subgroup.relIndex_sup_right, Subgroup.relIndex_subgroupOf hCA]
  have hdvd : (K.subgroupOf A).index ∣ Nat.card C := by
    rw [hindex]
    exact Subgroup.relIndex_dvd_card K C
  have hcop' : Nat.Coprime (Nat.card (Q.subgroupOf A)) (K.subgroupOf A).index := by
    obtain ⟨n, hn⟩ := hQ'.exists_card_eq
    rw [hn]
    exact Nat.Coprime.pow_left n ((Nat.Prime.coprime_iff_not_dvd hp).mpr
      (fun hdvd' => hcop (hdvd'.trans hdvd)))
  have hle := CFSG.GroupTheory.WielandtProduct.le_of_coprime_index (K := K.subgroupOf A)
    (H := Q.subgroupOf A) hcop'
  intro q hq
  have hqA : q ∈ A := hQKC hq
  have hq' : (⟨q, hqA⟩ : ↥A) ∈ Q.subgroupOf A := Subgroup.mem_subgroupOf.mpr hq
  exact Subgroup.mem_subgroupOf.mp (hle hq')

end CFSG.GroupTheory
