module

public import CFSG.LocalAnalysis.EvenSporadicStandard.Induction.LitComp
public import CFSG.LocalAnalysis.ComponentClassification.GSThmB82A10TLayer

public section

namespace CFSG.EvenSporadicStandard.Induction

open Subgroup

variable {G : Type} [Group G] [Finite G]

theorem twoLayerIn_inf_centralizer_le {H A : Subgroup G} (hA : IsPGroup 2 A)
    (hAH : A ≤ normalizer (H : Set G)) :
    twoLayerIn (H ⊓ centralizer (A : Set G)) ≤ twoLayerIn H :=
  CFSG.ComponentClassification.GSThmB.A10T.layerIn_inf_centralizer_le hA hAH

theorem lt_inf_normalizer_of_isPGroup {S T : Subgroup G} (hS : IsPGroup 2 S) (hT : T ≤ S)
    (hne : T ≠ S) : T < S ⊓ normalizer (T : Set G) := by
  haveI : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  haveI : Group.IsNilpotent S := hS.isNilpotent
  have hlt : T.subgroupOf S < ⊤ := by
    rw [lt_top_iff_ne_top]
    intro h
    apply hne
    apply le_antisymm hT
    intro x hx
    have : (⟨x, hx⟩ : S) ∈ T.subgroupOf S := by rw [h]; exact Subgroup.mem_top _
    exact this
  have hnc := Group.normalizerCondition_of_isNilpotent (G := S) (T.subgroupOf S) hlt
  obtain ⟨x, hxN, hxT⟩ := IsConcreteLE.exists_of_lt hnc
  have hxNG : (x : G) ∈ normalizer (T : Set G) := by
    rw [← Subgroup.subgroupOf_normalizer_eq hT] at hxN
    exact Subgroup.mem_subgroupOf.mp hxN
  have hxmem : (x : G) ∈ S ⊓ normalizer (T : Set G) := ⟨x.2, hxNG⟩
  have hxnot : (x : G) ∉ T := by
    intro hx
    exact hxT ((Subgroup.mem_subgroupOf).mpr hx)
  exact (IsConcreteLE.lt_iff_le_and_exists).mpr
    ⟨le_inf hT le_normalizer, ⟨(x : G), hxmem, hxnot⟩⟩

theorem twoLayerIn_centralizer_le_of_le {S : Subgroup G} (hS : IsPGroup 2 S) {T : Subgroup G}
    (hT : T ≤ S) :
    twoLayerIn (centralizer (S : Set G)) ≤ twoLayerIn (centralizer (T : Set G)) := by
  revert hT
  induction T using WellFoundedGT.induction with
  | _ T ih =>
    intro hT
    by_cases hTS : T = S
    · rw [hTS]
    ·
      set T' : Subgroup G := S ⊓ normalizer (T : Set G) with hT'def
      have hlt : T < T' := by
        rw [hT'def]; exact lt_inf_normalizer_of_isPGroup hS hT hTS
      have hT'S : T' ≤ S := by rw [hT'def]; exact inf_le_left
      have hT'2 : IsPGroup 2 T' := hS.to_le hT'S
      have hTT' : T ≤ T' := le_of_lt hlt
      have hT'normC : T' ≤ normalizer (centralizer (T : Set G) : Set G) :=
        (show T' ≤ normalizer (T : Set G) by rw [hT'def]; exact inf_le_right).trans
          (CFSG.BenderSuzuki.normalizer_le_normalizer_centralizer T)
      have hbal := twoLayerIn_inf_centralizer_le (H := centralizer (T : Set G)) (A := T')
        hT'2 hT'normC
      have hcT'T : centralizer (T' : Set G) ≤ centralizer (T : Set G) :=
        Subgroup.centralizer_le (show (T : Set G) ⊆ (T' : Set G) from hTT')
      rw [inf_eq_right.mpr hcT'T] at hbal
      exact (ih T' hlt hT'S).trans hbal

theorem fs79Lemma15Monotonicity_proved : FS79Lemma15Monotonicity :=
  fun _ _ _ _ _ hS _ hT => twoLayerIn_centralizer_le_of_le hS hT

end CFSG.EvenSporadicStandard.Induction
