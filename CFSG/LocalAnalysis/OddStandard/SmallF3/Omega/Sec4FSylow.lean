module

public import CFSG.LocalAnalysis.OddStandard.SmallF3.Omega.Sec4Basic

public section

attribute [-instance] instAddCommGroupOfIsSimpleAddGroupOfIsNilpotent
  instCommGroupOfIsSimpleGroupOfIsNilpotent

namespace CFSG.OddStandard.SmallF3.Omega

open Subgroup CFSG.Blueprint

variable {G : Type} [Group G] [Finite G]

theorem sec4F_exists_sylow_M {A : Subgroup G} (hA2 : IsPGroup 2 A) :
    ∃ P : Subgroup G, A ≤ P ∧ P ≤ normalizer (A : Set G) ∧ IsPGroup 2 P ∧
      ∀ P' : Subgroup G, P ≤ P' → P' ≤ normalizer (A : Set G) → IsPGroup 2 P' → P' = P := by
  classical
  haveI : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  let M : Subgroup G := normalizer (A : Set G)
  have hAM : A ≤ M := Subgroup.le_normalizer
  have hA2' : IsPGroup 2 (A.subgroupOf M) :=
    hA2.of_equiv (Subgroup.subgroupOfEquivOfLe hAM).symm
  haveI : (A.subgroupOf M).Normal :=
    (Subgroup.normal_subgroupOf_iff_le_normalizer hAM).mpr le_rfl
  obtain ⟨Ps⟩ := Sylow.nonempty (p := 2) (G := ↥M)
  have hAlePs : A.subgroupOf M ≤ (Ps : Subgroup ↥M) := hA2'.le_sylow_of_normal Ps
  let P₀ : Subgroup G := (Ps : Subgroup ↥M).map M.subtype
  have hP₀_le_M : P₀ ≤ M := Subgroup.map_subtype_le _
  have hAP₀ : A ≤ P₀ := by
    intro a ha
    exact ⟨⟨a, hAM ha⟩, hAlePs (Subgroup.mem_subgroupOf.mpr ha), rfl⟩
  have hP₀2 : IsPGroup 2 P₀ := Ps.isPGroup'.map M.subtype
  refine ⟨P₀, hAP₀, hP₀_le_M, hP₀2, ?_⟩
  intro P' hP₀P' hP'M hP'2
  have hK2 : IsPGroup 2 (P'.subgroupOf M) :=
    hP'2.of_equiv (Subgroup.subgroupOfEquivOfLe hP'M).symm
  have hPK : (Ps : Subgroup ↥M) ≤ P'.subgroupOf M := by
    intro y hy
    exact Subgroup.mem_subgroupOf.mpr (hP₀P' ⟨y, hy, rfl⟩)
  have hK : P'.subgroupOf M = (Ps : Subgroup ↥M) := Ps.is_maximal' hK2 hPK
  rw [← Subgroup.map_subgroupOf_eq_of_le hP'M, hK]

theorem sec4F_exists_normalizer_elt {P : Subgroup G} (hP2 : IsPGroup 2 P)
    (hS : ¬ IsSylow2Of P ⊤) :
    ∃ x : G, x ∈ normalizer (P : Set G) ∧ x ∉ P ∧ x * x ∈ P ∧ IsPGroup 2 ↥(P ⊔ zpowers x) := by
  classical
  haveI : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  obtain ⟨Q, hPQ⟩ := hP2.exists_le_sylow
  have hPQne : P ≠ (Q : Subgroup G) := by
    intro hEq
    apply hS
    refine ⟨le_top, ?_, ?_⟩
    · rw [hEq]; exact Q.isPGroup'
    · rw [Subgroup.relIndex_top_right, hEq]; exact Q.not_dvd_index
  let H : Subgroup ↥Q := P.subgroupOf Q
  have hHlt : H < ⊤ := by
    rw [lt_top_iff_ne_top]
    intro htop
    exact hPQne (le_antisymm hPQ (Subgroup.subgroupOf_eq_top.mp htop))
  haveI : Group.IsNilpotent ↥Q := Q.isPGroup'.isNilpotent
  have hnc := Group.normalizerCondition_of_isNilpotent (G := ↥Q)
  obtain ⟨y, hy_norm, hy_H⟩ := SetLike.exists_of_lt (hnc H hHlt)
  have hyQ : (y : G) ∈ Q := y.2
  have hy_normP : (y : G) ∈ normalizer (P : Set G) := by
    have hmap := Subgroup.le_normalizer_map (f := (Q : Subgroup G).subtype) (H := H)
    have hy_mem : (y : G) ∈ (Subgroup.normalizer H).map (Q : Subgroup G).subtype :=
      ⟨y, hy_norm, rfl⟩
    have hthis := hmap hy_mem
    rwa [Subgroup.map_subgroupOf_eq_of_le hPQ] at hthis
  have hyP : (y : G) ∉ P := fun hyP => hy_H (Subgroup.mem_subgroupOf.mpr hyP)
  obtain ⟨n, hn⟩ := Q.isPGroup' y
  have hn1 : (y : G) ^ 2 ^ n = 1 := by
    have := congrArg (Subtype.val) hn
    simpa using this
  have hmem : ∃ k : ℕ, (y : G) ^ 2 ^ k ∈ P := ⟨n, by rw [hn1]; exact P.one_mem⟩
  let k := Nat.find hmem
  have hkP : (y : G) ^ 2 ^ k ∈ P := Nat.find_spec hmem
  have hkmin : ∀ j < k, (y : G) ^ 2 ^ j ∉ P := fun j hj => Nat.find_min hmem hj
  have hkne : k ≠ 0 := by
    intro hk0
    exact hyP (by simpa [hk0] using hkP)
  obtain ⟨j, hj⟩ : ∃ j : ℕ, k = j + 1 := Nat.exists_eq_succ_of_ne_zero hkne
  refine ⟨(y : G) ^ 2 ^ j, ?_, ?_, ?_, ?_⟩
  · exact pow_mem hy_normP (2 ^ j)
  · exact hkmin j (by rw [hj]; exact Nat.lt_succ_self j)
  · have heq : (y : G) ^ 2 ^ j * (y : G) ^ 2 ^ j = (y : G) ^ 2 ^ (j + 1) := by
      rw [← pow_add]
      congr 1
      rw [Nat.pow_succ]
      ring
    rw [heq, ← hj]
    exact hkP
  · exact Q.isPGroup'.to_le
      (sup_le hPQ (Subgroup.zpowers_le.mpr (pow_mem hyQ (2 ^ j))))

end CFSG.OddStandard.SmallF3.Omega
