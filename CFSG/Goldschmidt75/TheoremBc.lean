module

public import CFSG.Goldschmidt75.TheoremBcL
public import CFSG.Goldschmidt75.TheoremBcN3
public import CFSG.Goldschmidt75.TheoremBcN2

public section

namespace CFSG.Goldschmidt75

open CFSG.Open CFSG.Goldschmidt Subgroup

universe u

variable {G : Type u} [Group G] [Finite G] {p : ℕ} [Fact p.Prime]

theorem rcFor_of_lt (IH : ∀ (H : Type u) [Group H] [Finite H], Nat.card H < Nat.card G →
    RcFor p H) : RcFor p G := by
  intro P S hSP hS
  apply rcSet_stronglyClosed_of_local P hSP hS
  intro S₀ hS₀ hS₀1 hfn hlarger
  by_cases hS₀S : S₀ = S
  · subst hS₀S
    intro h hh x hx hxh
    exact conj_mem_rcSet hh hx hxh
  have hlt : S₀ < S := lt_of_le_of_ne hS₀ hS₀S
  by_cases hN : normalizer (S₀ : Set G) = ⊤
  · have : S₀.Normal := normalizer_eq_top_iff.mp hN
    by_cases hbig : ∃ N : Subgroup G, N.Normal ∧ S₀ < N ∧ N ≤ S
    · obtain ⟨N, hNn, hlt', hNS⟩ := hbig
      have hloc := hlarger N hNS (Subgroup.card_lt_of_lt hlt')
      intro h _ x hx hxh
      exact hloc h (by rw [normalizer_eq_top_iff.mpr hNn]; exact mem_top h) x hx hxh
    have hmax : ∀ N : Subgroup G, N.Normal → S₀ ≤ N → N ≤ S → N = S₀ := by
      intro N hNn h1 h2
      by_contra hne
      exact hbig ⟨N, hNn, lt_of_le_of_ne h1 (Ne.symm hne), h2⟩
    suffices hsc : fusionStronglyClosed ((rcSet S P : Subgroup G) : Set G) P from
      fun h _ x hx hxh => hsc x hx h hxh
    set K := centralizer (S₀ : Set G)
    have hA := rcSet_stronglyClosed_K₁ P hSP hS hS₀ hS₀1 IH
    by_cases hM : normalizer ((S ⊓ K : Subgroup G) : Set G) = ⊤
    · have : (S ⊓ K).Normal := normalizer_eq_top_iff.mp hM
      have hES₀ : S ⊓ K ≤ S₀ := by
        have h1 := hmax (S₀ ⊔ (S ⊓ K)) inferInstance le_sup_left (sup_le hS₀ inf_le_left)
        rw [← h1]
        exact le_sup_right
      exact rcSet_stronglyClosed_of_normal_inf P hSP hS hS₀ hES₀
    · have hcard : Nat.card (normalizer ((S ⊓ K : Subgroup G) : Set G)) < Nat.card G := by
        rw [← Subgroup.card_top (G := G)]
        exact Subgroup.card_lt_of_lt (lt_top_iff_ne_top.mpr hM)
      exact rcSet_stronglyClosed_of_normalizer P hSP hS hS₀ hA (IH _ hcard)
  · have hcard : Nat.card (normalizer (S₀ : Set G)) < Nat.card G := by
      rw [← Subgroup.card_top (G := G)]
      exact Subgroup.card_lt_of_lt (lt_top_iff_ne_top.mpr hN)
    have hS₁ : Nat.card S₀ < Nat.card ↥(S ⊓ normalizer (S₀ : Set G)) :=
      Subgroup.card_lt_of_lt (lt_inf_normalizer (P.isPGroup'.to_le hSP) hlt)
    exact localRc_of_lt P hSP hS hS₀ hfn (IH _ hcard) (hlarger _ inf_le_left hS₁)

theorem rcFor (p : ℕ) [Fact p.Prime] (G : Type u) [Group G] [Finite G] : RcFor p G := by
  suffices key : ∀ n, ∀ (H : Type u) [Group H] [Finite H], Nat.card H = n → RcFor p H from
    key _ G rfl
  intro n
  induction n using Nat.strong_induction_on with
  | _ n ih =>
  intro H _ _ hn
  exact rcFor_of_lt fun K _ _ hK => ih _ (hn ▸ hK) K rfl

theorem theoremB_c (P : Sylow p G) {S : Subgroup G} (hSP : S ≤ P)
    (hS : fusionStronglyClosed (S : Set G) P) :
    fusionStronglyClosed
      ((⁅centralizer (S : Set G), centralizer (S : Set G)⁆ ⊓ P : Subgroup G) : Set G) P :=
  rcFor p G P S hSP hS

end CFSG.Goldschmidt75
