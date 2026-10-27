module

public import CFSG.LocalAnalysis.EvenSporadicStandard.Solomon78.H35Normal

public section

namespace CFSG.EvenSporadicStandard.Solomon78

open Subgroup CFSG.QuasithinUnique.Id2519
open scoped Pointwise

variable {G : Type} [Group G]

@[expose] def BTheoremAt (u : G) : Prop :=
  ∀ M : Subgroup G, IsTwoComponentIn M (centralizer ({u} : Set G)) →
    IsCompIn M (centralizer ({u} : Set G))

@[expose] def PumpUpOdd (K : Subgroup G) (t u : G) : Prop :=
  ∀ M : Subgroup G, IsCompIn M (centralizer ({u} : Set G)) →
    K ≤ M ⊔ CFSG.conjugate M t → M ≠ K → Odd (Nat.card (Subgroup.center ↥M))

theorem conjugate_one (K : Subgroup G) : CFSG.conjugate K 1 = K := by
  unfold CFSG.conjugate
  ext x
  simp

theorem conjugate_eq_of_mem_centralizer {K : Subgroup G} {t : G}
    (ht : t ∈ centralizer (K : Set G)) : CFSG.conjugate K t = K := by
  unfold CFSG.conjugate
  refine mem_normalizer_iff_map_conj_eq.1 ?_
  exact Subgroup.centralizer_le_normalizer (K : Set G)
    ((Subgroup.centralizer (K : Set G)).inv_mem ht)

theorem not_odd_card_center_of_mem {M : Subgroup G} [Finite G] {u : G} (hu : u ∈ M)
    (hu2 : orderOf u = 2) (hcent : ∀ x ∈ M, x * u = u * x) :
    ¬ Odd (Nat.card (Subgroup.center ↥M)) := by
  intro hodd
  have hmem : (⟨u, hu⟩ : ↥M) ∈ Subgroup.center ↥M := by
    rw [Subgroup.mem_center_iff]
    intro g
    exact Subtype.ext (hcent g g.2)
  have hord : orderOf (⟨⟨u, hu⟩, hmem⟩ : ↥(Subgroup.center ↥M)) = 2 := by
    rw [← Subgroup.orderOf_coe, Subgroup.coe_mk, Subgroup.orderOf_mk]
    exact hu2
  have hdvd : 2 ∣ Nat.card (Subgroup.center ↥M) := by
    rw [← hord]
    exact orderOf_dvd_natCard _
  exact (Nat.not_even_iff_odd.2 hodd) (even_iff_two_dvd.2 hdvd)

theorem odd_orderOf_of_mem_center {M : Subgroup G} [Finite G]
    (hodd : Odd (Nat.card (Subgroup.center ↥M))) {a : G} (ha : a ∈ M)
    (hc : ∀ x ∈ M, x * a = a * x) : Odd (orderOf a) := by
  have hmem : (⟨a, ha⟩ : ↥M) ∈ Subgroup.center ↥M := by
    rw [Subgroup.mem_center_iff]
    intro g
    exact Subtype.ext (hc g g.2)
  have hdvd : orderOf (⟨⟨a, ha⟩, hmem⟩ : ↥(Subgroup.center ↥M)) ∣
      Nat.card (Subgroup.center ↥M) := orderOf_dvd_natCard _
  have hord : orderOf (⟨⟨a, ha⟩, hmem⟩ : ↥(Subgroup.center ↥M)) = orderOf a := by
    rw [← Subgroup.orderOf_coe, Subgroup.coe_mk, Subgroup.orderOf_mk]
  rw [hord] at hdvd
  exact Odd.of_dvd_nat hodd hdvd

end CFSG.EvenSporadicStandard.Solomon78
