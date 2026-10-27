module

public import CFSG.CGT.Timmesfeld75.Sec6TwoY

public section

namespace CFSG.CGT.Timmesfeld75

open CFSG.Open

@[expose] def Sec62Exotic : Prop :=
  ∀ (G : Type) [Group G] (T T₁ : Subgroup G) (n m : ℕ), Sec6Ctx T T₁ n m →
    ∀ (x l : G) (T₂ : Subgroup G), Sec62Data T T₁ x l T₂ → T₂ ≠ T₁ → T₂ ≤ T ⊔ T₁

variable {G : Type} [Group G] {T T₁ : Subgroup G} {n m : ℕ}

theorem Sec6Ctx.sec62_core (hExo : Sec62Exotic) (hc : Sec6Ctx T T₁ n m) {x l : G}
    (hx : x ∈ normIn T₁ T) (hx1 : x ≠ 1) (hl : l ∈ T) (hD : x * l ∈ classD T) :
    ∃ s ∈ T, x * l = s⁻¹ * x * s := by
  have := hc.finite
  obtain ⟨k, hk⟩ := exists_mem_conj_of_mem_classD hD
  have d : Sec62Data T T₁ x l (conjSubgroup k T) := ⟨hx, hx1, hl, hD, ⟨k, rfl⟩, hk⟩
  by_cases hT₂ : conjSubgroup k T = T₁
  · have hyT₁ : x * l ∈ T₁ := hT₂ ▸ hk
    have hlT₁ : l ∈ T₁ := by
      have := T₁.mul_mem (T₁.inv_mem (normIn_le _ _ hx)) hyT₁
      simpa using this
    have hl1 : l ∈ T ⊓ T₁ := ⟨hl, hlT₁⟩
    rw [hc.sec3.cfg.inf, Subgroup.mem_bot] at hl1
    exact ⟨1, T.one_mem, by rw [hl1]; group⟩
  · exact d.eq_conj_of_le hc (hExo G T T₁ n m hc x l _ d hT₂)

theorem sec62_of_exotic (h1 : Sec4NoA) (hExo : Sec62Exotic) : Sec62 := by
  intro G _ T T₁ n m hc x hx hxT hcard y hyD t ht hyt
  have := hc.finite
  obtain ⟨k₀, hxk⟩ := exists_mem_conj_of_mem_classD hx.1
  have hne : conjSubgroup k₀ T ≠ T := fun h => hxT (h ▸ hxk)
  have hxN : x ∈ normIn (conjSubgroup k₀ T) T := mem_normIn.2 ⟨hxk, hx.2⟩
  have hx1 : x ≠ 1 := ne_one_of_mem_classD hx.1
  have hbot : normIn (conjSubgroup k₀ T) T ≠ ⊥ := fun hb =>
    hx1 (Subgroup.mem_bot.1 (hb ▸ hxN))
  have hbot' : normIn T (conjSubgroup k₀ T) ≠ ⊥ :=
    normIn_ne_bot_of_conj hc.hy.pair.wc hne hbot
  have hS3 : Sec3 T (conjSubgroup k₀ T) := hc.hS k₀ hne hbot'
  have hu : IsUIdx T T₁ k₀ := by
    refine ⟨hne, ?_⟩
    rw [hS3.card_normIn_swap, ← hS3.cfg.inf_centralizer_eq_normIn hxN hx1]
    exact hcard
  have hc' := hc.of_isUIdx h1 hu
  subst hyt
  exact hc'.sec62_core hExo hxN hx1 ht hyD

end CFSG.CGT.Timmesfeld75
