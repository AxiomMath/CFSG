module

public import CFSG.LocalAnalysis.ComponentClassification.HSFLitAlternating
public import CFSG.LocalAnalysis.ComponentClassification.UFrontierCoreBranches

public section

namespace CFSG.ComponentClassification.HSFLit

open CFSG Subgroup Blueprint Assembly.LowTwoRank

private theorem oddLieType_of_lieModel {G : Type} [Group G] {t : StatedLieTag} {n p f : ℕ}
    (h : LieModel G t n p f) (hp : p.Prime) (hp2 : p ≠ 2) (_ht : t ≠ .twistedB2) :
    OddLieType G :=
  ⟨t, n, p, f, hp, hp2, CFSG.Blueprint.LieModel.admissible h, h⟩

private theorem ne_two_of_pow_mod_four {p f : ℕ} (hf : 1 ≤ f)
    (h : p ^ f % 4 = 3 ∨ p ^ f % 4 = 1) : p ≠ 2 := by
  rintro rfl
  obtain ⟨g, rfl⟩ : ∃ g, f = g + 1 := ⟨f - 1, by omega⟩
  rcases g with _ | g
  · simp at h
  · have : 2 ^ (g + 1 + 1) = 4 * 2 ^ g := by ring
    rw [this] at h
    omega

theorem oddLieType_of_gen4
    (hGH : UFrontier.GH74ModelsInput)
    (hEven : ∀ (Y : Type) [Group Y] [Finite Y], (LieModel Y .PSL 2 2 3 ∨ LieModel Y .PSL 2 2 4 ∨
      LieModel Y .PSL 3 2 2 ∨ LieModel Y .twistedB2 0 2 3) → ∀ y : Y, orderOf y = 2 → Excluded y)
    (hSpor : ∀ s : TauCeti.SporadicName, (s = .M12 ∨ s = .M22 ∨ s = .M23 ∨ s = .J1 ∨ s = .J2 ∨
      s = .J3 ∨ s = .McL ∨ s = .Ly) →
      ∀ y : NativeSporadic.Carrier s, orderOf y = 2 → Excluded y)
    {X : Type} [Group X] [Finite X] [IsSimpleGroup X] (hnonab : ∃ a b : X, a * b ≠ b * a)
    {t : X} {L : Subgroup X} (h : Config t L)
    (hsect : ∀ P : Subgroup X, IsPGroup 2 P →
      ∃ s : Finset X, s.card ≤ 4 ∧ closure (s : Set X) = P) :
    OddLieType X := by
  have hspor : ∀ s : TauCeti.SporadicName, (s = .M12 ∨ s = .M22 ∨ s = .M23 ∨ s = .J1 ∨
      s = .J2 ∨ s = .J3 ∨ s = .McL ∨ s = .Ly) → NativeSporadic.IsSporadic X s → False := by
    intro s hs hX
    obtain ⟨e⟩ := hX
    have : Finite (NativeSporadic.Carrier s) := Finite.of_equiv X e.toEquiv
    have he : orderOf (e t) = 2 := by rw [MulEquiv.orderOf_eq, h.orderOf_eq]
    exact h.false_of_excluded ((hSpor s hs (e t) he).of_mulEquiv e)
  rcases hGH X hnonab h.three_le_twoRank hsect with ⟨p, f, hp, hp2, hf, h1⟩ |
    ⟨p, f, hp, hp2, hf, h1⟩ | ⟨f, h1⟩ | ⟨p, f, hp, hp2, hf, -, h1⟩ | ⟨p, f, hp, hp2, hf, -, h1⟩ |
    ⟨p, f, hp, hf, hm, h1⟩ | ⟨p, f, hp, hf, hm, h1⟩ | h1 | ⟨n, hn, hn', h1⟩ | h1
  · rcases h1 with h1 | h1
    · exact oddLieType_of_lieModel h1 hp hp2 (by decide)
    · exact oddLieType_of_lieModel h1 hp hp2 (by decide)
  · exact oddLieType_of_lieModel h1 hp hp2 (by decide)
  · exact oddLieType_of_lieModel h1 Nat.prime_three (by norm_num) (by decide)
  · exact oddLieType_of_lieModel h1 hp hp2 (by decide)
  · exact oddLieType_of_lieModel h1 hp hp2 (by decide)
  · exact oddLieType_of_lieModel h1 hp (ne_two_of_pow_mod_four hf (Or.inl hm)) (by decide)
  · exact oddLieType_of_lieModel h1 hp (ne_two_of_pow_mod_four hf (Or.inr hm)) (by decide)
  · exact (h.false_of_excluded (hEven X h1 t h.orderOf_eq)).elim
  · obtain ⟨e⟩ := h1
    exact (h.false_of_mulEquiv_alternating e).elim
  · exfalso
    rcases h1 with h1 | h1 | h1 | h1 | h1 | h1 | h1 | h1
    · exact hspor _ (Or.inl rfl) h1
    · exact hspor _ (Or.inr (Or.inl rfl)) h1
    · exact hspor _ (Or.inr (Or.inr (Or.inl rfl))) h1
    · exact hspor _ (Or.inr (Or.inr (Or.inr (Or.inl rfl)))) h1
    · exact hspor _ (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl rfl))))) h1
    · exact hspor _ (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl rfl)))))) h1
    · exact hspor _ (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl rfl))))))) h1
    · exact hspor _ (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr rfl))))))) h1

end CFSG.ComponentClassification.HSFLit
