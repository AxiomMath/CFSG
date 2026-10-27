module

public import CFSG.LocalAnalysis.EvenSporadicStandard.TwoHS.Defs

public section

namespace CFSG.EvenSporadicStandard.HNRecog.TwoHSData

open Subgroup CFSG.EvenSporadicStandard.TwoHS

theorem center_eq_zpowers_of_isF5Centralizer {H : Type} [Group H] {E : Subgroup H}
    (h : IsF5Centralizer H E) {a : H} (ha : a ∈ center H) (ha2 : orderOf a = 2) :
    center H = zpowers a := by
  have hcenter_le : center H ≤ E := by
    intro z hz
    apply h.centralizer_le
    rw [Subgroup.mem_centralizer_iff]
    intro y _hy
    exact Subgroup.mem_center_iff.mp hz y
  let f : center H → center E := fun z =>
    ⟨⟨z.1, hcenter_le z.2⟩, by
      rw [Subgroup.mem_center_iff]
      intro e
      apply Subtype.ext
      exact Subgroup.mem_center_iff.mp z.2 e.1⟩
  have hf : Function.Injective f := by
    intro z w hzw
    have h1 : (f z : E) = (f w : E) := Subtype.ext_iff.mp hzw
    have h2 : (f z : H) = (f w : H) := congrArg (fun x : E => (x : H)) h1
    exact Subtype.ext h2
  haveI hFinE : Finite (center E) :=
    Nat.finite_of_card_ne_zero (by rw [h.card_center]; norm_num)
  haveI hFinH : Finite (center H) := Finite.of_injective f hf
  have hcard : Nat.card (center H) ≤ 2 := by
    calc Nat.card (center H) ≤ Nat.card (center E) := Nat.card_le_card_of_injective f hf
      _ = 2 := h.card_center
  have hzp_le : zpowers a ≤ center H := Subgroup.zpowers_le.mpr ha
  have hcard_zp : Nat.card (zpowers a) = 2 := by rw [Nat.card_zpowers, ha2]
  have hge : 2 ≤ Nat.card (center H) := by
    rw [← hcard_zp]
    exact Subgroup.card_le_of_le hzp_le
  have hcard_eq : Nat.card (center H) = 2 := le_antisymm hcard hge
  exact (Subgroup.eq_of_le_of_card_ge hzp_le (by rw [hcard_eq, hcard_zp])).symm

theorem commutator_eq_of_isF5Centralizer {H : Type} [Group H] {E : Subgroup H}
    (h : IsF5Centralizer H E) : commutator H = E := by
  have hE_le : E ≤ commutator H := by
    calc E = (⊤ : Subgroup E).map E.subtype := by
            rw [Subgroup.map_top, Subgroup.range_subtype]
      _ = (_root_.commutator E).map E.subtype := by rw [h.perfect.commutator_eq_top]
      _ = ⁅E, E⁆ := Subgroup.map_subtype_commutator E
      _ ≤ ⁅(⊤ : Subgroup H), ⊤⁆ := Subgroup.commutator_mono le_top le_top
      _ = commutator H := rfl
  have hcomm_le : commutator H ≤ E := by
    haveI : E.Normal := h.normal
    haveI : IsCyclic (H ⧸ E) := isCyclic_of_prime_card (p := 2) (by
      rw [show Nat.card (H ⧸ E) = E.index from rfl, h.index_eq_two])
    exact Subgroup.Normal.quotient_commutative_iff_commutator_le.mp inferInstance
  exact le_antisymm hcomm_le hE_le

end CFSG.EvenSporadicStandard.HNRecog.TwoHSData
