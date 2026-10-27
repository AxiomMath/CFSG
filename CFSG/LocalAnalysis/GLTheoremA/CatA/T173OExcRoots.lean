module

public import CFSG.LocalAnalysis.GLTheoremA.CatA.T173XDefs

public section

namespace CFSG.LocalAnalysis.GLTheoremA.T173O

open CFSG.Open CFSG.LocalAnalysis.GLTheoremA.T173X

theorem stdVanishes_of_innerClosure_eq_top {G₀ : Type} [Group G₀] [Finite G₀]
    {A : Subgroup G₀} {d : G₀} (hsimple : IsSimpleGroup G₀)
    (h2 : ¬ IsPGroup 2 (⊤ : Subgroup G₀)) (h : innerClosure A d = ⊤) :
    StdVanishes A d := by
  rintro ⟨T, hTne, hT2, hle⟩
  have htop : (⊤ : Subgroup G₀) ≤ Subgroup.normalizer (T : Set G₀) := by
    simpa [h] using hle
  haveI : T.Normal := Subgroup.normalizer_eq_top_iff.mp (le_antisymm le_top htop)
  rcases hsimple.eq_bot_or_eq_top_of_normal T with hT | hT
  · exact hTne hT
  · exact h2 (hT ▸ hT2)


theorem not_isPGroup_two_top_of_subgroup {G : Type} [Group G] [Finite G]
    {p : ℕ} (hp : p.Prime) (hp2 : p ≠ 2) (H : Subgroup G) (hpcard : p ∣ Nat.card H) :
    ¬ IsPGroup 2 (⊤ : Subgroup G) := by
  intro h
  have hdvd : p ∣ Nat.card (⊤ : Subgroup G) := by
    rw [Subgroup.card_top]
    exact hpcard.trans (Subgroup.card_subgroup_dvd_card H)
  obtain ⟨k, hk⟩ := h.exists_card_eq
  rw [hk] at hdvd
  exact hp2 ((Nat.prime_dvd_prime_iff_eq hp Nat.prime_two).mp (hp.dvd_of_dvd_pow hdvd))

end CFSG.LocalAnalysis.GLTheoremA.T173O

end
