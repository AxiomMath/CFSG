module

public import CFSG.GH74.Uniqueness.SU.SU1Basic
public import CFSG.GH74.Uniqueness.SU.SU1MaxClass
public import CFSG.GH74.Uniqueness.SU.SU1CyclicIdx

public section

namespace CFSG.GH74.Uniqueness.SU.SU1

open Subgroup

theorem card_le_four_of_small_centralizer (h916 : CentralizerQuotientLe) {P : Type} [Group P]
    [Finite P] (hP : IsPGroup 2 P) (h8 : 8 < Nat.card P) {x : P}
    (hx : Nat.card (centralizer ({x} : Set P)) ≤ 4) {E : Subgroup P} (hE : ∀ y ∈ E, y * y = 1) :
    Nat.card E ≤ 4 := by
  obtain ⟨m, hm⟩ := IsPGroup.iff_card.mp hP
  obtain ⟨m', hm', hγ⟩ := maximalClass_aux h916 2 Nat.prime_two (Nat.card P) P rfl hP
    (by norm_num; omega) x (by simpa using hx)
  have hmm : m' = m := Nat.pow_right_injective (le_refl 2) (hm'.symm.trans hm)
  subst hmm
  have hnil : Group.IsNilpotent P := hP.isNilpotent
  have hcl : m' - 1 ≤ Group.nilpotencyClass P := by
    by_contra hcon
    apply hγ
    rw [Subgroup.lowerCentralSeries_eq_bot_iff_nilpotencyClass_le]
    omega
  have hm3 : 3 ≤ m' := by
    by_contra hcon
    have : 2 ^ m' ≤ 2 ^ 2 := Nat.pow_le_pow_right two_pos (by omega)
    omega
  obtain ⟨M, hMidx, hMcyc⟩ := exists_cyclic_index_two m' hm3 P hm hcl
  exact card_le_four_of_cyclic_index_two hMidx hE

theorem pRank_two_le_two_of_small_centralizer (h916 : CentralizerQuotientLe) {G : Type} [Group G]
    [Finite G] {S : Subgroup G} (hS : IsPGroup 2 S) (h8 : 8 < Nat.card S) {x : G} (hxS : x ∈ S)
    (hx : Nat.card ↥(S ⊓ centralizer ({x} : Set G)) ≤ 4) : Open.pRank 2 S ≤ 2 := by
  have hc : Nat.card (centralizer ({(⟨x, hxS⟩ : S)} : Set S)) =
      Nat.card ↥(S ⊓ centralizer ({x} : Set G)) := by
    refine Nat.card_congr ⟨fun y => ⟨y.1.1, y.1.2, ?_⟩, fun y => ⟨⟨y.1, y.2.1⟩, ?_⟩,
      fun y => rfl, fun y => rfl⟩
    · refine Subgroup.mem_centralizer_singleton_iff.mpr ?_
      exact congrArg Subtype.val (Subgroup.mem_centralizer_singleton_iff.mp y.2)
    · refine Subgroup.mem_centralizer_singleton_iff.mpr ?_
      apply Subtype.ext
      exact Subgroup.mem_centralizer_singleton_iff.mp y.2.2
  refine pRank_le_of fun E hES hEel k hk => ?_
  have hE2 := isElemAbelian_iff.mp hEel
  have hcard : Nat.card (E.subgroupOf S) = Nat.card E :=
    Nat.card_congr (Subgroup.subgroupOfEquivOfLe hES).toEquiv
  have h4 := card_le_four_of_small_centralizer h916 hS h8 (x := ⟨x, hxS⟩) (hc ▸ hx)
    (E := E.subgroupOf S) (fun y hy => by
      apply Subtype.ext
      have := hE2.2 y.1 (Subgroup.mem_subgroupOf.mp hy)
      simpa [pow_two] using this)
  rw [hcard, hk] at h4
  have : k ≤ 2 := by
    by_contra hcon
    have : 2 ^ 3 ≤ 2 ^ k := Nat.pow_le_pow_right two_pos (by omega)
    omega
  exact this

end CFSG.GH74.Uniqueness.SU.SU1
