module

public import CFSG.CGT.Timmesfeld75.Sec4NoAAssembly
public import CFSG.CGT.Timmesfeld75.JLemmaCore
public import CFSG.CGT.Timmesfeld75.Sec63Basic
public import CFSG.CGT.Timmesfeld75.Sec6TwoSetup

public section

namespace CFSG.CGT.Timmesfeld75

open CFSG.Open

@[expose] def Sec63A6 : Prop :=
  ∀ (G : Type) [Group G] (T T₁ : Subgroup G) (n m : ℕ) (x : G) (T₃ : Subgroup G),
    Sec63Cfg T T₁ n m x T₃ →
      (∀ j : Fin 3, (⨅ i, normIn (sec63Fam T T₁ T₃ j) (sec63Fam T T₁ T₃ i)) ≠ ⊥) →
      ¬ Nonempty (jQuot ↥(T ⊔ T₁ ⊔ T₃) ⧸ Subgroup.center (jQuot ↥(T ⊔ T₁ ⊔ T₃)) ≃*
        alternatingGroup (Fin 6))

section Main

variable {G : Type} [Group G] {T T₁ : Subgroup G} {n m : ℕ}

theorem Sec6Ctx.card_centralizer_le (hc : Sec6Ctx T T₁ n m) {x : G} (hx : x ∈ normD T)
    (hxT : x ∉ T) :
    Nat.card ↥(T ⊓ Subgroup.centralizer ({x} : Set G)) ≤ Nat.card ↥(normIn T T₁) := by
  have := hc.finite
  obtain ⟨k, hk⟩ := exists_mem_conj_of_mem_classD hx.1
  have hne : conjSubgroup k T ≠ T := fun h => hxT (h ▸ hk)
  have hxN : x ∈ normIn (conjSubgroup k T) T := mem_normIn.2 ⟨hk, hx.2⟩
  have hx1 : x ≠ 1 := ne_one_of_mem_classD hx.1
  have hL' : normIn (conjSubgroup k T) T ≠ ⊥ := fun hb =>
    hx1 (Subgroup.mem_bot.1 (hb ▸ hxN))
  have hL : normIn T (conjSubgroup k T) ≠ ⊥ := normIn_ne_bot_of_conj hc.hy.pair.wc hne hL'
  have hcfg : Cfg T (conjSubgroup k T) :=
    cfg_of_conj_conj hc.hy.pair.wc ⟨1, (conjSubgroup_one T).symm⟩ ⟨k, rfl⟩ hne hL
  rw [hcfg.inf_centralizer_eq_normIn hxN hx1]
  exact hc.hy.pair.card_normIn_le ⟨1, (conjSubgroup_one T).symm⟩ ⟨k, rfl⟩ hne

theorem Sec6Ctx.two_mul_card_normIn_le (hc : Sec6Ctx T T₁ n m) :
    2 * Nat.card ↥(normIn T T₁) ≤ Nat.card T := by
  have := hc.finite
  have hlt := card_normIn_lt_card_of_maxPair hc.hy.pair
  have hdvd : Nat.card ↥(normIn T T₁) ∣ Nat.card T := Subgroup.card_dvd_of_le (normIn_le T T₁)
  have hpos : 0 < Nat.card ↥(normIn T T₁) := Nat.card_pos
  obtain ⟨k, hk⟩ := hdvd
  rcases k with _ | _ | k
  · simp at hk
    omega
  · simp at hk
    omega
  · rw [hk]
    nlinarith

end Main

end CFSG.CGT.Timmesfeld75
