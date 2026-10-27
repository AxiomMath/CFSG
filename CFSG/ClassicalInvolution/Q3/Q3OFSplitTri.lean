module

public import CFSG.Assembly.RankThreeEvenDefs
public import CFSG.ClassicalInvolution.Q3.Q3NGBoot
public import CFSG.ClassicalInvolution.Q3.Q3NLFrame
public import CFSG.ClassicalInvolution.Q3.Q3NTLemmaD

public section

set_option linter.unusedSectionVars false

namespace CFSG.ClassicalInvolution.Q3.Q3OF

open CFSG.Open CFSG.ClassicalInvolution CFSG.ClassicalInvolution.Generic
  CFSG.ClassicalInvolution.Generic.DeltaClosure CFSG.ClassicalInvolution.Balance
  CFSG.ClassicalInvolution.Balance.Bootstrap CFSG.ClassicalInvolution.Q3.Q3NL
  CFSG.ClassicalInvolution.Q3.Q3NG CFSG.ClassicalInvolution.Q3.Q3W

section Data

variable {G : Type} [Group G] [Finite G] {Ω : Set (Subgroup G)} {K₁ K₂ M : Subgroup G}
  {z₁ z₂ m : G}

theorem exactTriple_of_edge (he : IsEdge3 Ω K₁ K₂ z₁ z₂) (hm : IsClassicalMember3 M m)
    (hc₁ : Commutes K₁ M) (hc₂ : Commutes K₂ M) (h₁ : z₁ ≠ m) (h₂ : z₂ ≠ m) :
    ExactTriple K₁ K₂ M z₁ z₂ m where
  mem₁ := he.cls₁.mem
  mem₂ := he.cls₂.mem
  mem₃ := hm.mem
  central₁ := fun _ hk =>
    Subgroup.mem_centralizer_singleton_iff.mp (isSubnormal_le he.cls₁.subnormal hk)
  central₂ := fun _ hk =>
    Subgroup.mem_centralizer_singleton_iff.mp (isSubnormal_le he.cls₂.subnormal hk)
  central₃ := fun _ hk =>
    Subgroup.mem_centralizer_singleton_iff.mp (isSubnormal_le hm.subnormal hk)
  sq₁ := Q3NT.mul_self_eq_one_of_orderOf_eq_two he.cls₁.orderOf_eq_two
  sq₂ := Q3NT.mul_self_eq_one_of_orderOf_eq_two he.cls₂.orderOf_eq_two
  sq₃ := Q3NT.mul_self_eq_one_of_orderOf_eq_two hm.orderOf_eq_two
  ne_one₁ := he.cls₁.ne_one
  ne_one₂ := he.cls₂.ne_one
  ne_one₃ := hm.ne_one
  comm₁₂ := he.comm
  comm₁₃ := hc₁
  comm₂₃ := hc₂
  ne₁₂ := he.ne
  ne₁₃ := h₁
  ne₂₃ := h₂

theorem fuzzyFrame3_of_exactTriple (T : ExactTriple K₁ K₂ M z₁ z₂ m) (hind : z₁ * z₂ ≠ m)
    (h₁ : K₁ ∈ Ω ∧ IsClassicalMember3 K₁ z₁) (h₂ : K₂ ∈ Ω ∧ IsClassicalMember3 K₂ z₂)
    (h₃ : M ∈ Ω ∧ IsClassicalMember3 M m) : FuzzyFrame3 Ω T.group := by
  have hrange : Set.range ![z₁, z₂, m] = ({z₁, z₂, m} : Set G) := by
    ext x
    simp only [Set.mem_range, Set.mem_insert_iff, Set.mem_singleton_iff]
    constructor
    · rintro ⟨i, rfl⟩
      fin_cases i <;> simp
    · rintro (rfl | rfl | rfl)
      exacts [⟨0, rfl⟩, ⟨1, rfl⟩, ⟨2, rfl⟩]
  have hcen : ∀ {J : Subgroup G}, J ≤ Subgroup.centralizer (T.group : Set G) →
      T.group ≤ trivialOnQuot J := fun hJ a ha =>
    mem_trivialOnQuot_of_centralizes fun x hx => (Subgroup.mem_centralizer_iff.mp (hJ hx) a ha)
  refine ⟨![K₁, K₂, M], ![z₁, z₂, m], ?_, ?_, T.isElemAbelian, T.card_eq_eight hind, ?_⟩
  · intro i
    fin_cases i
    exacts [h₁, h₂, h₃]
  · rw [hrange]
    rfl
  · intro i
    fin_cases i
    exacts [hcen T.le_centralizer₁, hcen T.le_centralizer₂, hcen T.le_centralizer₃]

@[expose] def NoTripleThrough (Ω : Set (Subgroup G)) (K₁ K₂ : Subgroup G) (z₁ z₂ : G) : Prop :=
  ∀ M ∈ Ω, ∀ m : G, IsClassicalMember3 M m → Commutes K₁ M → Commutes K₂ M →
    m ∈ Subgroup.closure ({z₁, z₂} : Set G)

theorem edge_triple_or_noTripleThrough (Ω : Set (Subgroup G)) (K₁ K₂ : Subgroup G)
    (z₁ z₂ : G) :
    (∃ M ∈ Ω, ∃ m : G, IsClassicalMember3 M m ∧ Commutes K₁ M ∧ Commutes K₂ M ∧
      m ∉ Subgroup.closure ({z₁, z₂} : Set G)) ∨ NoTripleThrough Ω K₁ K₂ z₁ z₂ := by
  by_cases h : NoTripleThrough Ω K₁ K₂ z₁ z₂
  · exact Or.inr h
  · left
    unfold NoTripleThrough at h
    push Not at h
    exact h

theorem ne_of_not_mem_pair (hind : m ∉ Subgroup.closure ({z₁, z₂} : Set G)) :
    z₁ ≠ m ∧ z₂ ≠ m ∧ z₁ * z₂ ≠ m := by
  have h1 : z₁ ∈ Subgroup.closure ({z₁, z₂} : Set G) := Subgroup.subset_closure (by simp)
  have h2 : z₂ ∈ Subgroup.closure ({z₁, z₂} : Set G) := Subgroup.subset_closure (by simp)
  refine ⟨fun h => hind (by rw [← h]; exact h1), fun h => hind (by rw [← h]; exact h2),
    fun h => hind (by rw [← h]; exact mul_mem h1 h2)⟩

end Data

end CFSG.ClassicalInvolution.Q3.Q3OF
