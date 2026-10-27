module

public import CFSG.Quasithin.Background.SmithB42Alt7

public section

namespace CFSG.HardMathSupport.Cooperstein.Coordinator.EightFive

open CFSG.Quasithin CFSG.QuasithinUnique

theorem asB42Alt7_ctx {V : Type} [CommGroup V] [Finite V]
    (hV : ∀ v : V, v ^ 2 = 1) {G L : Subgroup (MulAut V)} (C : Bridge.Alt57.Ctx G L 7)
    (hirr : XMod.IsIrrSec ↥L (⊥ : Subgroup V) ⊤) {A : Subgroup (MulAut V)}
    (hA : IsFFStarOffender G A) : B42Case5 G A ∨ B42Case7 G L A := by
  have hS2 : ∀ s : V, s * s = 1 := fun s => by simpa [pow_two] using hV s
  have hlo := B42A57.card_ge_of_faithful C hS2
  by_cases h16 : Nat.card V = 2 ^ 4
  · exact Or.inr (B42Alt7.case7 hV C hirr hA h16)
  · have hbig : 32 ≤ Nat.card V := by
      obtain ⟨k, hk⟩ := (IsPGroup.iff_card (p := 2) (G := V)).1 (B42A57.isPGroup_two hS2)
      rw [hk] at hlo h16 ⊢
      have hk4 : 4 ≤ k := (Nat.pow_le_pow_iff_right (by norm_num)).1 hlo
      have hk5 : 5 ≤ k := by
        rcases Nat.lt_or_ge k 5 with h | h
        · exact absurd (by rw [show k = 4 by omega]) h16
        · exact h
      calc 32 = 2 ^ 5 := by norm_num
        _ ≤ 2 ^ k := Nat.pow_le_pow_right (by norm_num) hk5
    exact Or.inl (B42Alt7.case5 hV C hirr hA hbig)

end CFSG.HardMathSupport.Cooperstein.Coordinator.EightFive
