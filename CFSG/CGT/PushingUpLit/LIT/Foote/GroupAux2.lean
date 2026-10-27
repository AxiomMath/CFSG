module

public import CFSG.LocalAnalysis.ComponentClassification.AschbacherTightEmbeddingData

public section

namespace CFSG.CGT.PushingUpLit.LIT.Foote

open CFSG.ComponentClassification.AschbacherTightEmbedding

variable {G : Type*} [Group G]

theorem mem_sup_iff_of_commute {A B : Subgroup G} (h : ∀ a ∈ A, ∀ b ∈ B, a * b = b * a)
    {x : G} : x ∈ A ⊔ B ↔ ∃ a ∈ A, ∃ b ∈ B, x = a * b := by
  constructor
  · intro hx
    rw [← Subgroup.closure_eq A, ← Subgroup.closure_eq B, ← Subgroup.closure_union] at hx
    induction hx using Subgroup.closure_induction with
    | mem x hx =>
      rcases hx with hx | hx
      · exact ⟨x, hx, 1, B.one_mem, by simp⟩
      · exact ⟨1, A.one_mem, x, hx, by simp⟩
    | one => exact ⟨1, A.one_mem, 1, B.one_mem, by simp⟩
    | mul x y _ _ hx hy =>
      obtain ⟨a, ha, b, hb, rfl⟩ := hx
      obtain ⟨a', ha', b', hb', rfl⟩ := hy
      refine ⟨a * a', A.mul_mem ha ha', b * b', B.mul_mem hb hb', ?_⟩
      calc a * b * (a' * b') = a * (b * a') * b' := by group
        _ = a * (a' * b) * b' := by rw [← h a' ha' b hb]
        _ = a * a' * (b * b') := by group
    | inv x _ hx =>
      obtain ⟨a, ha, b, hb, rfl⟩ := hx
      refine ⟨a⁻¹, A.inv_mem ha, b⁻¹, B.inv_mem hb, ?_⟩
      have hab := h a ha b hb
      calc (a * b)⁻¹ = b⁻¹ * a⁻¹ := by group
        _ = a⁻¹ * b⁻¹ := by
          have : a⁻¹ * b⁻¹ = (b * a)⁻¹ := by group
          rw [this, ← hab]
          group
  · rintro ⟨a, ha, b, hb, rfl⟩
    exact Subgroup.mul_mem_sup ha hb

theorem mem_normalizer_of_tight {P L : Subgroup G} (hPL : P ≤ L)
    (ht : TightlyEmbedded (P.subgroupOf L)) {g : G} (hg : g ∈ L)
    (heven : Even (Nat.card ↥(P ⊓ rightConjugate P g))) :
    g ∈ Subgroup.normalizer (P : Set G) := by
  by_contra hng
  have hN : (⟨g, hg⟩ : ↥L) ∉ Subgroup.normalizer ((P.subgroupOf L : Subgroup L) : Set L) := by
    rw [← Subgroup.subgroupOf_normalizer_eq hPL]
    exact fun h => hng h
  have hodd := ht.2 ⟨g, hg⟩ hN
  have heq : P.subgroupOf L ⊓ rightConjugate (P.subgroupOf L) ⟨g, hg⟩ =
      (P ⊓ rightConjugate P g).subgroupOf L := by
    ext x
    simp only [Subgroup.mem_inf, Subgroup.mem_subgroupOf, mem_rightConjugate_iff]
    rfl
  rw [heq] at hodd
  have hcard : Nat.card ((P ⊓ rightConjugate P g).subgroupOf L) =
      Nat.card ↥(P ⊓ rightConjugate P g) :=
    Nat.card_congr (Subgroup.subgroupOfEquivOfLe (inf_le_left.trans hPL)).toEquiv
  rw [hcard] at hodd
  exact (Nat.not_even_iff_odd.2 hodd) heven

end CFSG.CGT.PushingUpLit.LIT.Foote
