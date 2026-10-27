module

public import CFSG.LocalAnalysis.EvenSporadicStandard.Fin76b.Harada75Frame

public section

namespace CFSG.EvenSporadicStandard.Fin76b

open CFSG.Open

theorem card_normalizer_A_le {S : Type} [Group S] [Finite S] (hS : IsPGroup 2 S) {A : Subgroup S}
    (hA : IsElemAbelian 2 A) (hA8 : Nat.card A = 8) (hCA : Subgroup.centralizer (A : Set S) ≤ A) :
    Nat.card (Subgroup.normalizer (A : Set S)) ≤ 64 ∧
      (Nat.card (Subgroup.normalizer (A : Set S)) = 64 →
        ∃ s ∈ Subgroup.normalizer (A : Set S), ∃ t ∈ Subgroup.normalizer (A : Set S),
          s * t * s⁻¹ * t⁻¹ ∉ A) := by
  obtain ⟨N, hN⟩ : ∃ N : Subgroup S, N = Subgroup.normalizer (A : Set S) := ⟨_, rfl⟩
  rw [← hN]
  have hAN : A ≤ N := by
    rw [hN]
    exact Subgroup.le_normalizer
  have hAnorm : (A.subgroupOf N).Normal :=
    (Subgroup.normal_subgroupOf_iff_le_normalizer hAN).mpr hN.le
  have hcomm : ∀ x y : S, x ∈ A → y ∈ A → x * y = y * x := by
    intro x y hx hy
    have h := hA.1.is_comm.comm (⟨x, hx⟩ : A) ⟨y, hy⟩
    exact congrArg Subtype.val h
  have hAel : IsElemAbelian 2 (A.subgroupOf N) := by
    refine ⟨IsMulCommutative.of_comm ?_, ?_⟩
    · intro x y
      apply Subtype.ext
      apply Subtype.ext
      show x.1.1 * y.1.1 = y.1.1 * x.1.1
      exact hcomm _ _ (Subgroup.mem_subgroupOf.mp x.2) (Subgroup.mem_subgroupOf.mp y.2)
    · intro x hx
      apply Subtype.ext
      show x.1 ^ 2 = 1
      exact hA.2 x.1 (Subgroup.mem_subgroupOf.mp hx)
  have hAcard : Nat.card (A.subgroupOf N) = 8 :=
    (Nat.card_congr (Subgroup.subgroupOfEquivOfLe hAN).toEquiv).trans hA8
  have hC : Subgroup.centralizer ((A.subgroupOf N : Subgroup N) : Set N) = A.subgroupOf N := by
    apply le_antisymm
    · intro n hn
      rw [Subgroup.mem_centralizer_iff] at hn
      have hnS : n.1 ∈ Subgroup.centralizer (A : Set S) := by
        rw [Subgroup.mem_centralizer_iff]
        intro a ha
        have h := hn ⟨a, hAN ha⟩ (SetLike.mem_coe.mpr (Subgroup.mem_subgroupOf.mpr ha))
        have h' := congrArg Subtype.val h
        exact h'
      exact Subgroup.mem_subgroupOf.mpr (hCA hnS)
    · intro x hx
      rw [Subgroup.mem_centralizer_iff]
      intro g hg
      apply Subtype.ext
      exact hcomm g.1 x.1 (Subgroup.mem_subgroupOf.mp (SetLike.mem_coe.mp hg))
        (Subgroup.mem_subgroupOf.mp hx)
  have hidx : (Subgroup.centralizer ((A.subgroupOf N : Subgroup N) : Set N)).index ≤ 8 :=
    index_centralizer_le_eight (hS.to_subgroup N) hAnorm hAel hAcard
  rw [hC] at hidx
  have hmul : Nat.card (A.subgroupOf N) * (A.subgroupOf N).index = Nat.card N :=
    Subgroup.card_mul_index (H := A.subgroupOf N)
  rw [hAcard] at hmul
  refine ⟨by omega, fun h64 => ?_⟩
  have h8 : (A.subgroupOf N).index = 8 := by omega
  have h8' : (Subgroup.centralizer ((A.subgroupOf N : Subgroup N) : Set N)).index = 8 := by
    rw [hC]
    exact h8
  obtain ⟨s, t, hst⟩ :=
    exists_comm_not_mem_centralizer (hS.to_subgroup N) hAnorm hAel hAcard h8'
  rw [hC] at hst
  refine ⟨s.1, s.2, t.1, t.2, fun hmem => hst (Subgroup.mem_subgroupOf.mpr ?_)⟩
  simpa using hmem

end CFSG.EvenSporadicStandard.Fin76b
