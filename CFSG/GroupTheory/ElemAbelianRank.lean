module

public import CFSG.Open.LocalVocabulary

public section

namespace CFSG.GroupTheory

open CFSG.Open

variable {G : Type*} [Group G] [Finite G]

theorem card_eq_pow_pRank_of_isElemAbelian {p : ℕ} (hp : p.Prime) {E : Subgroup G}
    (hE : IsElemAbelian p E) : Nat.card E = p ^ pRank p E := by
  haveI : Fact p.Prime := ⟨hp⟩
  have hEp : IsPGroup p ↥E := fun y =>
    ⟨1, Subtype.ext (by simpa using hE.2 y y.2)⟩
  obtain ⟨n, hn⟩ := IsPGroup.iff_card.1 hEp
  have hbound : ∀ k ∈ {k | ∃ F : Subgroup G, F ≤ E ∧ IsElemAbelian p F ∧
      Nat.card F = p ^ k}, k ≤ n := by
    rintro k ⟨F, hFE, -, hF⟩
    have h1 : Nat.card F ≤ Nat.card E := Subgroup.card_le_of_le hFE
    rw [hF, hn] at h1
    exact (pow_le_pow_iff_right₀ hp.one_lt).1 h1
  have hpR : pRank p E = n := by
    apply le_antisymm
    · unfold pRank
      exact csSup_le' hbound
    · unfold pRank
      exact le_csSup ⟨n, hbound⟩ ⟨E, le_rfl, hE, hn⟩
  rw [hpR, hn]

end CFSG.GroupTheory
