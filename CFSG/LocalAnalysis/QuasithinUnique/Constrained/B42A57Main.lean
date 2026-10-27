module

public import CFSG.LocalAnalysis.QuasithinUnique.Constrained.L246B42A57Def
public import CFSG.LocalAnalysis.QuasithinUnique.Constrained.B42A57Dim
public import CFSG.LocalAnalysis.QuasithinUnique.Constrained.B42A57M5

public section

namespace CFSG.QuasithinUnique.B42A57

open CFSG.Quasithin CFSG.Open

@[expose] def A7SixDimIsDeletedOff : Prop :=
  ∀ (S : Type) [CommGroup S] [Finite S], (∀ s : S, s ^ 2 = 1) →
    ∀ (G L A : Subgroup (MulAut S)), Bridge.Alt57.Ctx G L 7 →
      XMod.IsIrrSec ↥L (⊥ : Subgroup S) ⊤ → IsFFStarOffender G A →
      (Nat.card S = 2 ^ 5 ∨ Nat.card S = 2 ^ 6) → AlternatingNatural L ⊤ ⊥ 7

theorem asB42A57_of_A7SixDimOff (h6 : A7SixDimIsDeletedOff) : AsB42A57 := by
  intro S _ _ hS G L A m C hirr hA
  have hS2 : ∀ s : S, s * s = 1 := fun s => by simpa [pow_two] using hS s
  have hup := card_le_of_offender C hirr hA
  have hlo : 2 ^ 4 ≤ Nat.card S := card_ge_of_faithful C hS2
  rcases C.m_cases with rfl | rfl
  · have hcard : Nat.card S = 16 := le_antisymm (by simpa using hup.1 rfl) (by simpa using hlo)
    obtain ⟨ι⟩ := C.iso
    rcases m5_classification hS2 hcard L ι with h | h
    · exact Or.inl ⟨rfl, h⟩
    · exact Or.inr (Or.inl h)
  · have hle : Nat.card S ≤ 2 ^ 6 := hup.2 rfl
    obtain ⟨k, hk⟩ := (IsPGroup.iff_card (p := 2) (G := S)).1 (isPGroup_two hS2)
    have hk4 : 4 ≤ k := by
      by_contra h
      push Not at h
      have : 2 ^ k ≤ 2 ^ 3 := Nat.pow_le_pow_right (by norm_num) (by omega)
      omega
    have hk6 : k ≤ 6 := by
      by_contra h
      push Not at h
      have : 2 ^ 7 ≤ 2 ^ k := Nat.pow_le_pow_right (by norm_num) h
      omega
    interval_cases k
    · exact Or.inr (Or.inr ⟨rfl, hk⟩)
    · exact Or.inr (Or.inl (h6 S hS G L A C hirr hA (Or.inl hk)))
    · exact Or.inr (Or.inl (h6 S hS G L A C hirr hA (Or.inr hk)))

end CFSG.QuasithinUnique.B42A57
