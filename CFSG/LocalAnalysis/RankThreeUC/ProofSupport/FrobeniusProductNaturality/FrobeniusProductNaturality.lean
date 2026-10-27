module


public import CFSG.Open.RankThreeDefs

public section

namespace CFSG.LocalAnalysis.RankThreeUC.ProofSupport.FrobeniusProductNaturality

open CFSG.Open

variable {G : Type} [Group G]

theorem map_product (e : MulAut G) {W K D : Subgroup G}
    (h : rankThreeFrobeniusProduct W K D) :
    rankThreeFrobeniusProduct (W.map e.toMonoidHom) (K.map e.toMonoidHom)
      (D.map e.toMonoidHom) := by
  obtain ⟨X, hW, hK, hKb, hDb, hKX, hKn, hKD, hfix⟩ := h
  have hmem : ∀ (A B : Subgroup G), (∀ x, x ∈ X ↔ ∃ a ∈ A, ∃ b ∈ B, x = a * b) →
      ∀ x, x ∈ X.map e.toMonoidHom ↔ ∃ a ∈ A.map e.toMonoidHom, ∃ b ∈ B.map e.toMonoidHom,
        x = a * b := by
    intro A B hAB x
    constructor
    · rintro ⟨y, hy, rfl⟩
      obtain ⟨a, ha, b, hb, rfl⟩ := (hAB y).1 hy
      exact ⟨e a, ⟨a, ha, rfl⟩, e b, ⟨b, hb, rfl⟩, by simp⟩
    · rintro ⟨_, ⟨a, ha, rfl⟩, _, ⟨b, hb, rfl⟩, rfl⟩
      exact ⟨a * b, (hAB _).2 ⟨a, ha, b, hb, rfl⟩, by simp⟩
  refine ⟨X.map e.toMonoidHom, hmem W D hW, hmem K D hK, ?_, ?_, Subgroup.map_mono hKX, ?_, ?_, ?_⟩
  · intro h0
    exact hKb ((Subgroup.map_eq_bot_iff_of_injective K e.injective).1 h0)
  · intro h0
    exact hDb ((Subgroup.map_eq_bot_iff_of_injective D e.injective).1 h0)
  · rw [Subgroup.normal_subgroupOf_iff_le_normalizer (Subgroup.map_mono hKX),
      ← Subgroup.map_equiv_normalizer_eq]
    exact Subgroup.map_mono ((Subgroup.normal_subgroupOf_iff_le_normalizer hKX).mp hKn)
  · rw [← Subgroup.map_inf _ _ _ e.injective, hKD, Subgroup.map_bot]
  · rintro _ ⟨v, hv, rfl⟩ hv1 _ ⟨k, hk, rfl⟩ hc
    have hv1' : v ≠ 1 := fun h1 => hv1 (by simp [h1])
    have hc' : k * v = v * k := e.injective (by simpa using hc)
    have := hfix v hv hv1' k hk hc'
    simp [this]

end CFSG.LocalAnalysis.RankThreeUC.ProofSupport.FrobeniusProductNaturality
