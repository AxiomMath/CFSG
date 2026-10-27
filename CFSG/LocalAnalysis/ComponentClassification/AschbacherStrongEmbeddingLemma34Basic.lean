module

public import CFSG.LocalAnalysis.ComponentClassification.AschbacherStrongEmbeddingOverlap
public import CFSG.LocalAnalysis.SectionRank.PRank
public import CFSG.LocalAnalysis.ComponentClassification.AschbacherStrongEmbeddingDefs

public section

namespace CFSG.ComponentClassification.AschbacherStrongEmbedding

namespace Lemma34

open CFSG.Open CFSG.ComponentClassification.AschbacherTightEmbedding

variable {G : Type*} [Group G]

structure Hyp [Finite G] (S : Sylow 2 G) (A₁ A₂ : Subgroup G) : Prop where
  le_one : A₁ ≤ (S : Subgroup G)
  le_two : A₂ ≤ (S : Subgroup G)
  comm : ⁅A₁, A₂⁆ = ⊥
  rank_one : 2 ≤ pRank 2 A₁
  rank_two : 2 ≤ pRank 2 A₂
  closed_overlap : relStronglyClosed (overlapClosure A₁ A₂) ((A₁ : Set G) ∪ A₂)
    (overlapClosure A₁ A₂ ⊓ (S : Subgroup G))
  closed_one : relStronglyClosed ⊤ ((A₁ : Set G) ∪ A₂)
    ((S : Subgroup G) ⊓ Subgroup.normalizer (A₁ : Set G))
  closed_two : relStronglyClosed ⊤ ((A₁ : Set G) ∪ A₂)
    ((S : Subgroup G) ⊓ Subgroup.normalizer (A₂ : Set G))

@[expose] def FixesOnly (H X : Subgroup G) : Prop :=
  ∀ g : G, (∀ x ∈ X, g⁻¹ * x * g ∈ H) → g ∈ H

theorem overlapClosure_comm (A₁ A₂ : Subgroup G) :
    overlapClosure A₁ A₂ = overlapClosure A₂ A₁ := by
  unfold overlapClosure
  rw [Set.pair_comm]

theorem commute_of_comm {A₁ A₂ : Subgroup G} (h : ⁅A₁, A₂⁆ = ⊥) {a b : G} (ha : a ∈ A₁)
    (hb : b ∈ A₂) : Commute a b := by
  have hle := Subgroup.commutator_eq_bot_iff_le_centralizer.mp h ha
  exact (Subgroup.mem_centralizer_iff.mp hle b hb).symm

theorem le_or_le_of_subset_union {Y A B : Subgroup G} (h : (Y : Set G) ⊆ (A : Set G) ∪ B) :
    Y ≤ A ∨ Y ≤ B := by
  by_contra hcon
  rw [not_or] at hcon
  obtain ⟨y₁, hy₁Y, hy₁A⟩ := Set.not_subset.mp hcon.1
  obtain ⟨y₂, hy₂Y, hy₂B⟩ := Set.not_subset.mp hcon.2
  have hy₁B : y₁ ∈ B := (h hy₁Y).resolve_left hy₁A
  have hy₂A : y₂ ∈ A := (h hy₂Y).resolve_right hy₂B
  rcases h (Y.mul_mem hy₁Y hy₂Y) with hA | hB
  · apply hy₁A
    have := A.mul_mem hA (A.inv_mem hy₂A)
    rwa [mul_inv_cancel_right] at this
  · apply hy₂B
    have := B.mul_mem (B.inv_mem hy₁B) hB
    rwa [inv_mul_cancel_left] at this

theorem conj_mem_of_mem_normalizer {A : Subgroup G} {g a : G}
    (hg : g ∈ Subgroup.normalizer (A : Set G)) (ha : a ∈ A) : g⁻¹ * a * g ∈ A :=
  (Subgroup.mem_normalizer_iff''.mp hg a).mp ha

theorem normalizer_le_overlapClosure_one {A₁ A₂ : Subgroup G} (hne : A₁ ≠ ⊥) :
    Subgroup.normalizer (A₁ : Set G) ≤ overlapClosure A₁ A₂ := by
  intro g hg
  obtain ⟨a, ha, ha1⟩ := (Subgroup.bot_or_exists_ne_one A₁).resolve_left hne
  exact mem_overlapClosure_of_conj (Or.inl rfl) (Or.inl rfl) ha ha1
    (conj_mem_of_mem_normalizer hg ha)

theorem normalizer_le_overlapClosure_two {A₁ A₂ : Subgroup G} (hne : A₂ ≠ ⊥) :
    Subgroup.normalizer (A₂ : Set G) ≤ overlapClosure A₁ A₂ := by
  rw [overlapClosure_comm]
  exact normalizer_le_overlapClosure_one hne

theorem mem_overlapClosure_of_union {A₁ A₂ : Subgroup G} {a g : G}
    (ha : a ∈ (A₁ : Set G) ∪ A₂) (ha1 : a ≠ 1) (hag : g⁻¹ * a * g ∈ (A₁ : Set G) ∪ A₂) :
    g ∈ overlapClosure A₁ A₂ := by
  rcases ha with ha | ha <;> rcases hag with hag | hag
  · exact mem_overlapClosure_of_conj (Or.inl rfl) (Or.inl rfl) ha ha1 hag
  · exact mem_overlapClosure_of_conj (Or.inl rfl) (Or.inr rfl) ha ha1 hag
  · exact mem_overlapClosure_of_conj (Or.inr rfl) (Or.inl rfl) ha ha1 hag
  · exact mem_overlapClosure_of_conj (Or.inr rfl) (Or.inr rfl) ha ha1 hag

variable [Finite G] {S : Sylow 2 G} {A₁ A₂ : Subgroup G}

omit [Finite G] in
theorem ne_bot_of_two_le_pRank [Finite G] {A : Subgroup G} (h : 2 ≤ pRank 2 A) : A ≠ ⊥ := by
  rintro rfl
  have : pRank 2 (⊥ : Subgroup G) ≤ 0 := by
    apply CFSG.SectionRank.pRank_le (by norm_num)
    intro E hE _
    rw [le_bot_iff.mp hE, Subgroup.card_bot]
    norm_num
  omega

theorem Hyp.symm (h : Hyp S A₁ A₂) : Hyp S A₂ A₁ where
  le_one := h.le_two
  le_two := h.le_one
  comm := by rw [Subgroup.commutator_comm]; exact h.comm
  rank_one := h.rank_two
  rank_two := h.rank_one
  closed_overlap := by
    rw [overlapClosure_comm, Set.union_comm]
    exact h.closed_overlap
  closed_one := by
    rw [Set.union_comm]
    exact h.closed_two
  closed_two := by
    rw [Set.union_comm]
    exact h.closed_one

theorem Hyp.ne_bot_one (h : Hyp S A₁ A₂) : A₁ ≠ ⊥ := ne_bot_of_two_le_pRank h.rank_one

theorem Hyp.ne_bot_two (h : Hyp S A₁ A₂) : A₂ ≠ ⊥ := ne_bot_of_two_le_pRank h.rank_two

theorem Hyp.le_overlapClosure_one (h : Hyp S A₁ A₂) : A₁ ≤ overlapClosure A₁ A₂ :=
  fun _ ha => normalizer_le_overlapClosure_one h.ne_bot_one (Subgroup.le_normalizer ha)

theorem Hyp.le_overlapClosure_two (h : Hyp S A₁ A₂) : A₂ ≤ overlapClosure A₁ A₂ :=
  fun _ ha => normalizer_le_overlapClosure_two h.ne_bot_two (Subgroup.le_normalizer ha)

theorem Hyp.mem_overlapClosure_of_mem_union (h : Hyp S A₁ A₂) {a : G}
    (ha : a ∈ (A₁ : Set G) ∪ A₂) : a ∈ overlapClosure A₁ A₂ := by
  rcases ha with ha | ha
  · exact h.le_overlapClosure_one ha
  · exact h.le_overlapClosure_two ha

theorem Hyp.conj_mem_of_mem_overlapClosure (h : Hyp S A₁ A₂) {a y : G}
    (ha : a ∈ (A₁ : Set G) ∪ A₂) (hy : y ∈ overlapClosure A₁ A₂)
    (hS : y⁻¹ * a * y ∈ (S : Subgroup G)) : y⁻¹ * a * y ∈ (A₁ : Set G) ∪ A₂ := by
  refine h.closed_overlap a ha y hy ⟨?_, hS⟩
  exact Subgroup.mul_mem _ (Subgroup.mul_mem _ (Subgroup.inv_mem _ hy)
    (h.mem_overlapClosure_of_mem_union ha)) hy

theorem Hyp.conj_mem_of_mem_normalizer (h : Hyp S A₁ A₂) {a g : G}
    (ha : a ∈ (A₁ : Set G) ∪ A₂) (hS : g⁻¹ * a * g ∈ (S : Subgroup G))
    (hN : g⁻¹ * a * g ∈ Subgroup.normalizer (A₁ : Set G) ∨
      g⁻¹ * a * g ∈ Subgroup.normalizer (A₂ : Set G)) :
    g⁻¹ * a * g ∈ (A₁ : Set G) ∪ A₂ := by
  rcases hN with hN | hN
  · exact h.closed_one a ha g (Subgroup.mem_top g) ⟨hS, hN⟩
  · exact h.closed_two a ha g (Subgroup.mem_top g) ⟨hS, hN⟩

theorem Hyp.conj_subset_of_normalizer (h : Hyp S A₁ A₂) {X : Set G}
    (hX : X ⊆ (A₁ : Set G) ∪ A₂) {g : G} (hXS : ∀ x ∈ X, g⁻¹ * x * g ∈ (S : Subgroup G))
    {x₀ : G} (hx₀ : x₀ ∈ X) (hx₀1 : x₀ ≠ 1)
    (hN : g⁻¹ * x₀ * g ∈ Subgroup.normalizer (A₁ : Set G) ∨
      g⁻¹ * x₀ * g ∈ Subgroup.normalizer (A₂ : Set G)) :
    g ∈ overlapClosure A₁ A₂ ∧ ∀ x ∈ X, g⁻¹ * x * g ∈ (A₁ : Set G) ∪ A₂ := by
  have hg : g ∈ overlapClosure A₁ A₂ :=
    mem_overlapClosure_of_union (hX hx₀) hx₀1
      (h.conj_mem_of_mem_normalizer (hX hx₀) (hXS x₀ hx₀) hN)
  exact ⟨hg, fun x hx => h.conj_mem_of_mem_overlapClosure (hX hx) hg (hXS x hx)⟩

omit [Finite G] in
theorem FixesOnly.mono {H X Y : Subgroup G} (hXY : X ≤ Y) (hX : FixesOnly H X) :
    FixesOnly H Y :=
  fun g hg => hX g fun x hx => hg x (hXY hx)

omit [Finite G] in
theorem fixesOnly_zpowers_iff {H : Subgroup G} {x : G} :
    FixesOnly H (Subgroup.zpowers x) ↔ ∀ g : G, g⁻¹ * x * g ∈ H → g ∈ H := by
  constructor
  · intro hx g hg
    refine hx g fun y hy => ?_
    obtain ⟨k, rfl⟩ := Subgroup.mem_zpowers_iff.mp hy
    have h' : g⁻¹ * x ^ k * g = (g⁻¹ * x * g) ^ k := by
      rw [← MulAut.conj_inv_apply, map_zpow, MulAut.conj_inv_apply]
    rw [h']
    exact H.zpow_mem hg k
  · intro hx g hg
    exact hx g (hg x (Subgroup.mem_zpowers x))

omit [Finite G] in
theorem unique_of_fixesOnly {H : Subgroup G} {z : G} (hzH : z ∈ H)
    (hz : FixesOnly H (Subgroup.zpowers z)) : ∀ g : G, z ∈ rightConjugate H g ↔ g ∈ H := by
  intro g
  rw [mem_rightConjugate_iff]
  constructor
  · intro hg
    have h1 := (fixesOnly_zpowers_iff.mp hz) g⁻¹ (by rwa [inv_inv])
    exact H.inv_mem_iff.mp h1
  · intro hg
    exact H.mul_mem (H.mul_mem hg hzH) (H.inv_mem hg)

end Lemma34

end CFSG.ComponentClassification.AschbacherStrongEmbedding
