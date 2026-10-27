module

public import Mathlib.GroupTheory.Sylow

public section

namespace CFSG.OddStandard.SmallF3.HarrisU33

open Subgroup

variable {G : Type*} [Group G] [Finite G]

theorem exists_sylow_of_isPGroup {p : ℕ} [Fact p.Prime] {H Q : Subgroup G} (hQH : Q ≤ H)
    (hQ : IsPGroup p Q) :
    ∃ S : Subgroup G, S ≤ H ∧ IsPGroup p S ∧ ¬ p ∣ S.relIndex H ∧ Q ≤ S := by
  have hQ' : IsPGroup p (Q.subgroupOf H) := hQ.comap_subtype
  obtain ⟨S', hQS'⟩ := hQ'.exists_le_sylow
  refine ⟨(S' : Subgroup ↥H).map H.subtype, Subgroup.map_subtype_le (H := H) (S' : Subgroup ↥H),
    S'.isPGroup'.map H.subtype, ?_, ?_⟩
  · have hsub : ((S' : Subgroup ↥H).map H.subtype).subgroupOf H = (S' : Subgroup ↥H) :=
      Subgroup.comap_map_eq_self_of_injective (f := H.subtype) Subtype.coe_injective _
    rw [Subgroup.relIndex, hsub]
    exact S'.not_dvd_index
  · have hQeq : (Q.subgroupOf H).map H.subtype = Q :=
      (Subgroup.subgroupOf_map_subtype Q H).trans (inf_eq_left.mpr hQH)
    rw [← hQeq]
    exact Subgroup.map_mono hQS'

theorem inf_eq_of_isPGroup {S Y T : Subgroup G} (hS : IsPGroup 2 S) (hT : T ≤ S ⊓ Y)
    (hcard : Nat.card T = 2 ^ (Nat.card Y).factorization 2) : S ⊓ Y = T := by
  have hSi : IsPGroup 2 (S ⊓ Y : Subgroup G) := hS.to_inf_left
  obtain ⟨n, hn⟩ := hSi.exists_card_eq
  have hY : Nat.card Y ≠ 0 := by
    haveI : Nonempty ↥Y := ⟨⟨1, Y.one_mem⟩⟩
    exact (Nat.card_pos (α := ↥Y)).ne'
  have hdiv : 2 ^ n ∣ Nat.card ↥Y :=
    hn ▸ Subgroup.card_dvd_of_le (inf_le_right : S ⊓ Y ≤ Y)
  have hnle : n ≤ (Nat.card Y).factorization 2 :=
    (Nat.prime_two.pow_dvd_iff_le_factorization hY).mp hdiv
  have hle : Nat.card ↥(S ⊓ Y) ≤ Nat.card ↥T := by
    rw [hn, hcard]
    exact Nat.pow_le_pow_right (by norm_num) hnle
  exact (Subgroup.eq_of_le_of_card_ge hT hle).symm

end CFSG.OddStandard.SmallF3.HarrisU33
