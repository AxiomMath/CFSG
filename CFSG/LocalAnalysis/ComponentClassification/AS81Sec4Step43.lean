module

public import CFSG.LocalAnalysis.ComponentClassification.AS81Sec4S1

public section

namespace CFSG.ComponentClassification.AS81

open Subgroup CFSG.ABGLocalTools HeSylow

variable {G : Type} [Group G] [Finite G]

theorem exists_mem_normalizer_not_mem_of_lt {p : ℕ} [Fact p.Prime] {P Q : Subgroup G}
    (hQ : IsPGroup p Q) (hPQ : P < Q) :
    ∃ x ∈ Q, x ∉ P ∧ x ∈ normalizer (P : Set G) := by
  have : Group.IsNilpotent Q := hQ.isNilpotent
  have hlt : P.subgroupOf Q < ⊤ := by
    refine lt_of_le_of_ne le_top fun htop => hPQ.not_ge fun x hx => ?_
    have hx' : (⟨x, hx⟩ : Q) ∈ P.subgroupOf Q := by
      rw [htop]
      trivial
    exact mem_subgroupOf.mp hx'
  obtain ⟨y, hyN, hyP⟩ :=
    IsConcreteLE.exists_of_lt (Group.normalizerCondition_of_isNilpotent (G := Q) _ hlt)
  refine ⟨y, y.2, fun h => hyP (mem_subgroupOf.mpr h), ?_⟩
  have hy : y ∈ (normalizer (P : Set G)).subgroupOf Q := by
    rw [subgroupOf_normalizer_eq hPQ.le]
    exact hyN
  exact mem_subgroupOf.mp hy

theorem isSylowOf_top_of_normalizer_le {T M : Subgroup G} (hT : IsSylowOf 2 T M)
    (hN : normalizer (T : Set G) ≤ M) : IsSylowOf 2 T ⊤ := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  obtain ⟨S, hTS⟩ := hT.isPGroup.exists_le_sylow
  have hTS' : T = S := by
    by_contra hne
    obtain ⟨y, hyS, hyT, hyN⟩ :=
      exists_mem_normalizer_not_mem_of_lt S.isPGroup' (lt_of_le_of_ne hTS hne)
    have hQ : T ⊔ zpowers y = T :=
      hT.eq_of_le le_sup_left (sup_le hT.le (zpowers_le.mpr (hN hyN)))
        (S.isPGroup'.to_le (sup_le hTS (zpowers_le.mpr hyS)))
    exact hyT (hQ ▸ mem_sup_right (mem_zpowers y))
  rw [isSylowOf_iff]
  refine ⟨le_top, hT.isPGroup, ?_⟩
  rw [relIndex_top_right, hTS']
  exact S.not_dvd_index

theorem step43_of
    (h44 : Step44ii) : Step43 := by
  intro G _ _ A R g E F hset S₁ hSN
  obtain ⟨Q, E', F', U, z, k, -, hm⟩ := exists_sylModel_of_step44 h44 hset hSN
  exact isSylowOf_top_of_normalizer_le hSN (normalizer_le_of_sylModel hset hSN hm)

end CFSG.ComponentClassification.AS81
