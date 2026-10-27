module

public import CFSG.CGT.PushingUpLit.CGT6K1.Beta
import CFSG.LocalAnalysis.ComponentClassification.GMS78Setup

public section

namespace CFSG.CGT.PushingUpLit.CGT6K1

open CFSG CFSG.Blueprint Subgroup CFSG.LocalAnalysis.EvenBN.GMSK CFSG.CGT.PushingUpLit.CGT6

theorem kt_outcome_of_survivors {Q : Type} [Group Q] {n : ℕ} {T₀ : Subgroup Q}
    (hβ : T₀ ⊓ CFSG.layer Q = ⊥) (h : FixedRootSurvivors ↥(CFSG.layer Q) n) :
    SimpleOuterOutcome Q n T₀ := by
  rcases h with h | h | h | ⟨h2, h⟩ | ⟨h3, h⟩
  · exact Or.inr ⟨hβ, Or.inl h⟩
  · exact Or.inr ⟨hβ, Or.inr (Or.inl h)⟩
  · exact Or.inr ⟨hβ, Or.inr (Or.inr (Or.inl h))⟩
  · refine Or.inl ⟨h2, ?_⟩
    rcases h with h | h | h | h | h | h
    · exact Or.inr (Or.inl h)
    · exact Or.inl h
    · exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h))))
    · exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h)))))
    · exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h))))))
    · exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr h))))))
  · exact Or.inr ⟨hβ, Or.inr (Or.inr (Or.inr ⟨h3, h⟩))⟩

theorem kt_stdLinearData {Q : Type} [Group Q] [Finite Q] {n : ℕ} {A T₀ : Subgroup Q}
    (h : AlmostSimple Q n A T₀) (hβ : T₀ ⊓ CFSG.layer Q ≠ ⊥) :
    StdLinearData ↥(CFSG.layer Q) (A.subgroupOf (CFSG.layer Q)) n := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have := CFSG.LocalCores.layer_characteristic (G := Q)
  have := h.simple
  obtain ⟨hn, hstd, hnn, K, _, _, hK, ⟨φ⟩⟩ := h.std
  have heven : Even (Nat.card (centralizer (A : Set Q) ⊓ CFSG.layer Q : Subgroup Q)) := by
    have h2 : IsPGroup 2 (T₀ ⊓ CFSG.layer Q : Subgroup Q) := h.sylow.isPGroup.to_inf_left
    rcases h2.card_eq_or_dvd with h1 | h1
    · exact absurd (card_eq_one.1 h1) hβ
    · exact even_iff_two_dvd.2 (h1.trans (card_dvd_of_le (inf_le_inf_right _ h.sylow.le)))
  refine ⟨hn, CFSG.ComponentClassification.GMS78.standard_subgroupOf hstd h.le heven,
    fun hN => ?_, K, inferInstance, inferInstance, hK, ⟨(subgroupOfEquivOfLe h.le).trans φ⟩⟩
  apply hnn
  rcases IsSimpleGroup.eq_bot_or_eq_top_of_normal (A.subgroupOf (CFSG.layer Q)) with h1 | h1
  · rw [subgroupOf_eq_bot, disjoint_iff, inf_eq_left.2 h.le] at h1
    rw [h1]
    infer_instance
  · rw [subgroupOf_eq_top] at h1
    rw [le_antisymm h.le h1]
    infer_instance

theorem simpleOuterOutcome_of_inputs (hSel : CatSelector) (hSimple : SimpleStd)
    {Q : Type} [Group Q] [Finite Q] {n : ℕ} {A T₀ : Subgroup Q} (h : AlmostSimple Q n A T₀) :
    SimpleOuterOutcome Q n T₀ := by
  by_cases hβ : T₀ ⊓ CFSG.layer Q = ⊥
  · exact kt_outcome_of_survivors hβ (beta_survivors hSel h hβ)
  · exact Or.inl (hSimple _ h.simple (h.kgroup.subgroup _) n _ (kt_stdLinearData h hβ))

end CFSG.CGT.PushingUpLit.CGT6K1
