module

public import CFSG.CGT.Timmesfeld75.Sec62Count
public import CFSG.CGT.Timmesfeld75.Sec6Two

public section

namespace CFSG.CGT.Timmesfeld75

open CFSG.Open

variable {G : Type} [Group G] [Finite G] {T T₁ T₂ Y : Subgroup G} {n m : ℕ}

omit [Finite G] in
theorem Sec62Ctx.mem_pts (P : Sec62Ctx T T₁ Y n m) (hT₂ : IsConjPt T Y T₂) {A : Subgroup G}
    (hA : A ∈ sec62Pts T T₁ T₂) : IsConjPt T Y A := by
  have hT₂Y : T₂ ≤ Y := hT₂.le (le_sup_left.trans P.hXY)
  rcases hA with rfl | hA
  · exact hT₂
  · simp only [Set.mem_iUnion] at hA
    obtain ⟨Q, hQ, s, hs, rfl⟩ := hA
    exact (P.mem_line hQ).1.conj (hT₂Y hs)

theorem Sec62Ctx.sq_add_le_card (P : Sec62Ctx T T₁ Y n m) (hT₂ : IsConjPt T Y T₂)
    (hT₂X : ¬ T₂ ≤ T ⊔ T₁) : (2 ^ m) ^ 2 + 2 ^ m ≤ Nat.card ↥(normIn T T₁) := by
  have hbound := ncard_mul_pred_add_one_le (cfgM T T₁) (s := sec62Pts T T₁ T₂)
    (c := Nat.card ↥(normIn T T₁))
    (fun A hA B hB hne => P.inf_eq_bot (P.mem_pts hT₂ hA) (P.mem_pts hT₂ hB) hne)
    (fun A hA => P.card_inf_cfgM (P.mem_pts hT₂ hA))
  rw [P.ncard_pts hT₂ hT₂X, P.ctx.sec3.card_cfgM_eq_sq] at hbound
  have hL : Nat.card ↥(normIn T T₁) ≠ 1 := fun h => P.ctx.sec3.cfg.ne (Subgroup.card_eq_one.1 h)
  have hpos : 0 < Nat.card ↥(normIn T T₁) := Nat.card_pos
  obtain ⟨k, hk⟩ : ∃ k, Nat.card ↥(normIn T T₁) = k + 1 :=
    ⟨Nat.card ↥(normIn T T₁) - 1, by omega⟩
  have hk1 : 1 ≤ k := by omega
  rw [hk, Nat.add_sub_cancel] at hbound
  rw [hk]
  generalize 2 ^ m = q at hbound ⊢
  by_contra hlt
  push Not at hlt
  have h3 : k + 3 ≤ (q + 1) * q + 1 := by nlinarith
  have h4 := Nat.mul_le_mul_right k h3
  nlinarith

theorem Sec62Data.le_sup_of_le_three {x l : G} (h1 : Sec4NoA) (hc : Sec6Ctx T T₁ n m)
    (hn : n ≤ 3) (d : Sec62Data T T₁ x l T₂) (hne : T₂ ≠ T₁) : T₂ ≤ T ⊔ T₁ := by
  by_contra hX
  obtain ⟨x₂, hx₂, hx₂T⟩ := (d.sec3₂ hc).conj
  have hP : Sec62Ctx T T₁ (T ⊔ T₁ ⊔ T₂) n m :=
    ⟨hc, le_sup_left, sup_le hc.sec3.cfg.le_normalizer_cfgM (d.T₂_le_normalizer h1 hc hne)⟩
  have hT₂ : IsConjPt T (T ⊔ T₁ ⊔ T₂) T₂ :=
    ⟨x₂, (sup_le (le_sup_left.trans le_sup_left) le_sup_right : T ⊔ T₂ ≤ T ⊔ T₁ ⊔ T₂) hx₂, hx₂T⟩
  have h := hP.sq_add_le_card hT₂ hX
  rw [hc.card_normIn] at h
  have hq : 0 < 2 ^ m := pow_pos (by norm_num) m
  have h5 : (2 ^ m) ^ (n - 1) ≤ (2 ^ m) ^ 2 := Nat.pow_le_pow_right hq (by omega)
  nlinarith

@[expose] def Sec62ExoticBig : Prop :=
  ∀ (G : Type) [Group G] (T T₁ : Subgroup G) (n m : ℕ), Sec6Ctx T T₁ n m → 4 ≤ n →
    ∀ (x l : G) (T₂ : Subgroup G), Sec62Data T T₁ x l T₂ → T₂ ≠ T₁ → T₂ ≤ T ⊔ T₁

omit [Finite G] in
theorem sec62Exotic_of_big (h1 : Sec4NoA) (hB : Sec62ExoticBig) : Sec62Exotic := by
  intro G _ T T₁ n m hc x l T₂ d hne
  have := hc.finite
  rcases Nat.lt_or_ge n 4 with hn | hn
  · exact d.le_sup_of_le_three h1 hc (by omega) hne
  · exact hB G T T₁ n m hc hn x l T₂ d hne

omit [Finite G] in
theorem sec62_of_big (h1 : Sec4NoA) (hB : Sec62ExoticBig) : Sec62 :=
  sec62_of_exotic h1 (sec62Exotic_of_big h1 hB)

end CFSG.CGT.Timmesfeld75
