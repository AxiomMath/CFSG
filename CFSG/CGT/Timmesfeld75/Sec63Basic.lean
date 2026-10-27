module

public import CFSG.Adapters.ProjectiveSpecialLinear
public import CFSG.CGT.Timmesfeld75.Sec6Four

public section

namespace CFSG.CGT.Timmesfeld75

open CFSG.Open

section Fam

variable {G : Type} [Group G]

@[expose] def sec63Fam (T T₁ T₃ : Subgroup G) : Fin 3 → Subgroup G := ![T, T₁, T₃]

structure Sec63Cfg (T T₁ : Subgroup G) (n m : ℕ) (x : G) (T₃ : Subgroup G) : Prop where
  ctx : Sec6Ctx T T₁ n m
  big : 32 ≤ Nat.card T
  hx : x ∈ normD T
  hxT : x ∉ T
  small : Nat.card ↥(T ⊓ Subgroup.centralizer ({x} : Set G)) < Nat.card ↥(normIn T T₁)
  conj : ∃ g : G, T₃ = conjSubgroup g T
  mem : x ∈ T₃

variable {T T₁ T₃ : Subgroup G} {n m : ℕ} {x : G}

theorem Sec63Cfg.ne_left (c : Sec63Cfg T T₁ n m x T₃) : T₃ ≠ T := fun h =>
  c.hxT (h ▸ c.mem)

theorem Sec63Cfg.x_ne_one (c : Sec63Cfg T T₁ n m x T₃) : x ≠ 1 :=
  ne_one_of_mem_classD c.hx.1

theorem Sec63Cfg.x_mem_normIn (c : Sec63Cfg T T₁ n m x T₃) : x ∈ normIn T₃ T :=
  mem_normIn.2 ⟨c.mem, c.hx.2⟩

theorem Sec63Cfg.normIn_ne_bot (c : Sec63Cfg T T₁ n m x T₃) : normIn T T₃ ≠ ⊥ := by
  have := c.ctx.finite
  obtain ⟨g, hg⟩ := c.conj
  have hbot : normIn (conjSubgroup g T) T ≠ ⊥ := hg ▸ fun hb =>
    c.x_ne_one (Subgroup.mem_bot.1 (hb ▸ c.x_mem_normIn))
  exact hg ▸ normIn_ne_bot_of_conj c.ctx.hy.pair.wc (hg ▸ c.ne_left) hbot

theorem Sec63Cfg.sec3 (c : Sec63Cfg T T₁ n m x T₃) : Sec3 T T₃ := by
  have := c.ctx.finite
  obtain ⟨g, hg⟩ := c.conj
  have hne : conjSubgroup g T ≠ T := hg ▸ c.ne_left
  have hbot : normIn T (conjSubgroup g T) ≠ ⊥ := hg ▸ c.normIn_ne_bot
  exact hg ▸ c.ctx.hS g hne hbot

theorem Sec63Cfg.card_normIn (c : Sec63Cfg T T₁ n m x T₃) :
    Nat.card ↥(normIn T T₃) = Nat.card ↥(T ⊓ Subgroup.centralizer ({x} : Set G)) := by
  rw [c.sec3.cfg.inf_centralizer_eq_normIn c.x_mem_normIn c.x_ne_one]

theorem Sec63Cfg.card_normIn_lt (c : Sec63Cfg T T₁ n m x T₃) :
    Nat.card ↥(normIn T₃ T) < Nat.card ↥(normIn T T₁) := by
  have := c.ctx.finite
  rw [c.sec3.card_normIn_swap, c.card_normIn]
  exact c.small

theorem Sec63Cfg.ne_mid (c : Sec63Cfg T T₁ n m x T₃) : T₃ ≠ T₁ := by
  intro h
  have h1 := c.card_normIn_lt
  rw [h, c.ctx.card_normIn_swap] at h1
  exact lt_irrefl _ h1

end Fam

end CFSG.CGT.Timmesfeld75
