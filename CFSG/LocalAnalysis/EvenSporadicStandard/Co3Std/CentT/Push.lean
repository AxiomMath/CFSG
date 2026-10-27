module

public import CFSG.LocalAnalysis.EvenSporadicStandard.Co3Std.CentT.Basic
public import CFSG.LocalAnalysis.EvenSporadicStandard.Common.Fusion

public section

namespace CFSG.EvenSporadicStandard.Co3Std.CentT

open Subgroup

theorem false_of_transferWitness {G : Type} [Group G] [Finite G] [IsSimpleGroup G]
    (hnonab : ∃ a b : G, a * b ≠ b * a) {H : Subgroup G} (Q : Sylow 2 G)
    (hQH : (Q : Subgroup G) ≤ H) (a : ↥H) (ha2 : orderOf (a : G) = 2)
    (hTW : TransferWitness ↥H a (fun w => IsConj (a : G) (w : G))) : False := by
  obtain ⟨S, haS, U, hUS, hUrel, haU, hnf⟩ := hTW
  let S' : Subgroup G := (S : Subgroup ↥H).map H.subtype
  let U' : Subgroup G := U.map H.subtype
  have hHodd : ¬ 2 ∣ H.index := fun h =>
    Q.not_dvd_index (h.trans (Subgroup.index_dvd_of_le hQH))
  have hS'p : IsPGroup 2 S' := IsPGroup.map S.isPGroup' H.subtype
  have hS'idx : ¬ 2 ∣ S'.index := by
    change ¬ 2 ∣ ((S : Subgroup ↥H).map H.subtype).index
    rw [Subgroup.index_map_subtype]
    intro h
    rcases Nat.prime_two.dvd_mul.mp h with h1 | h1
    · exact S.not_dvd_index h1
    · exact hHodd h1
  have hU'S' : U' ≤ S' := Subgroup.map_mono hUS
  have hU'rel : U'.relIndex S' = 2 := by
    change (U.map H.subtype).relIndex ((S : Subgroup ↥H).map H.subtype) = 2
    rw [Subgroup.relIndex_map_map_of_injective U (S : Subgroup ↥H) H.subtype_injective,
      hUrel]
  have haS' : (a : G) ∈ S' := ⟨a, haS, rfl⟩
  have haU' : (a : G) ∉ U' := by
    rintro ⟨u, huU, hu_eq⟩
    exact haU (Subtype.ext hu_eq ▸ huU)
  obtain ⟨g, hg⟩ :=
    exists_conj_mem_complement hnonab hS'p hS'idx hU'S' hU'rel haS' haU' ha2
  obtain ⟨u, huU, hu_eq⟩ := hg
  exact hnf u huU (isConj_iff.mpr ⟨g⁻¹, by rw [inv_inv]; exact hu_eq.symm⟩)

end CFSG.EvenSporadicStandard.Co3Std.CentT
