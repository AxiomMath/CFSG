module

public import CFSG.CGT.Timmesfeld75.Sec6Ctx
public import CFSG.CGT.Timmesfeld75.Sec5NineLift
public import CFSG.CGT.Timmesfeld75.Sec5Eight

public section

namespace CFSG.CGT.Timmesfeld75

open CFSG.Open

variable {G : Type} [Group G] {T T₁ : Subgroup G} {n m : ℕ}

theorem mul_self_eq_one_of_mem_classD (hT : IsElemAbelian 2 T) {x : G} (hx : x ∈ classD T) :
    x * x = 1 := by
  obtain ⟨g, t, ht, -, rfl⟩ := hx
  have htt : t * t = 1 := elemAbelian_mul_self hT ht
  calc g⁻¹ * t * g * (g⁻¹ * t * g) = g⁻¹ * (t * t) * g := by group
    _ = 1 := by rw [htt]; group

theorem ne_one_of_mem_classD {x : G} (hx : x ∈ classD T) : x ≠ 1 := by
  obtain ⟨g, t, -, ht1, rfl⟩ := hx
  intro h
  apply ht1
  calc t = g * (g⁻¹ * t * g) * g⁻¹ := by group
    _ = 1 := by rw [h]; group

theorem Sec6Ctx.mem_hSub_of_card_centralizer (h1 : Sec4NoA) (hc : Sec6Ctx T T₁ n m) {x : G}
    (hx : x ∈ normD T) (hxT : x ∉ T)
    (hcard : Nat.card ↥(T ⊓ Subgroup.centralizer ({x} : Set G)) = Nat.card ↥(normIn T T₁)) :
    x ∈ hSub T (normIn T₁ T) := by
  have := hc.finite
  have hx1 : x ≠ 1 := ne_one_of_mem_classD hx.1
  obtain ⟨g, t, ht, ht1, hxg⟩ := hx.1
  have hxh : x ∈ conjSubgroup g⁻¹ T := mem_conjSubgroup.2 (by
    have e : g⁻¹⁻¹ * x * g⁻¹ = t := by rw [hxg]; group
    rw [e]
    exact ht)
  have hne : conjSubgroup g⁻¹ T ≠ T := fun h => hxT (h ▸ hxh)
  have hxN : x ∈ normIn (conjSubgroup g⁻¹ T) T := mem_normIn.2 ⟨hxh, hx.2⟩
  have hbot : normIn (conjSubgroup g⁻¹ T) T ≠ ⊥ := fun hb =>
    hx1 (Subgroup.mem_bot.1 (hb ▸ hxN))
  have hbot' : normIn T (conjSubgroup g⁻¹ T) ≠ ⊥ :=
    normIn_ne_bot_of_conj hc.hy.pair.wc hne hbot
  have hS3 : Sec3 T (conjSubgroup g⁻¹ T) := hc.hS g⁻¹ hne hbot'
  have hu : IsUIdx T T₁ g⁻¹ := by
    refine ⟨hne, ?_⟩
    rw [hS3.card_normIn_swap, ← hS3.cfg.inf_centralizer_eq_normIn hxN hx1]
    exact hcard
  rw [← sec58 h1 hc.hy hc.hS hc.hI]
  exact le_hSubU_of_isUIdx hu hxN

theorem Sec6Ctx.normD_le_hSub (h1 : Sec4NoA) (h63 : Sec63) (h64 : Sec64Eight)
    (hc : Sec6Ctx T T₁ n m) {x : G} (hx : x ∈ normD T) : x ∈ hSub T (normIn T₁ T) := by
  by_cases hxT : x ∈ T
  · exact left_le_hSub hxT
  · rcases h63 G T T₁ n m hc x hx hxT with hcard | ⟨h16, h8, h4⟩
    · exact hc.mem_hSub_of_card_centralizer h1 hx hxT hcard
    · exact h64 G T T₁ n m hc h16 h8 x hx hxT h4

theorem Sec6Ctx.normD_le_hSub_of_not_a8 (h1 : Sec4NoA) (h63 : Sec63) (hc : Sec6Ctx T T₁ n m)
    (hA8 : ¬ (n = 4 ∧ m = 1)) {x : G} (hx : x ∈ normD T) : x ∈ hSub T (normIn T₁ T) := by
  by_cases hxT : x ∈ T
  · exact left_le_hSub hxT
  · rcases h63 G T T₁ n m hc x hx hxT with hcard | ⟨h16, h8, -⟩
    · exact hc.mem_hSub_of_card_centralizer h1 hx hxT hcard
    · exact absurd (hc.card_eq_sixteen_iff.1 ⟨h16, h8⟩) hA8

theorem Sec6Ctx.hSub_le_closure (hc : Sec6Ctx T T₁ n m) :
    hSub T (normIn T₁ T) ≤ Subgroup.closure (normD T) := by
  have hP := hc.hy.pair
  have hL₁N : normIn T₁ T ≤ Subgroup.normalizer (T : Set G) := fun x hx => (mem_normIn.1 hx).2
  refine sup_le (fun t ht => ?_) (iSup₂_le fun g hg x hx => ?_)
  · by_cases ht1 : t = 1
    · rw [ht1]
      exact Subgroup.one_mem _
    · exact Subgroup.subset_closure ⟨mem_classD_of_mem ht ht1, Subgroup.le_normalizer ht⟩
  · by_cases hx1 : x = 1
    · rw [hx1]
      exact Subgroup.one_mem _
    · obtain ⟨x₀, hx₀⟩ := hP.conj
      have hxT₁ : x ∈ conjSubgroup g T₁ :=
        conjSubgroup_mono (normIn_le T₁ T) hx
      have hxk : x ∈ conjSubgroup (g * x₀) T := by
        rw [hx₀, conjSubgroup_conjSubgroup] at hxT₁
        exact hxT₁
      have hxN : x ∈ Subgroup.normalizer (T : Set G) := by
        have := conjSubgroup_le_normalizer hg hL₁N hx
        exact this
      exact Subgroup.subset_closure (mem_normD_of_mem_conjSubgroup hxk hx1 hxN)

theorem Sec6Ctx.closure_normD_of_not_a8 (h1 : Sec4NoA) (h63 : Sec63) (hc : Sec6Ctx T T₁ n m)
    (hA8 : ¬ (n = 4 ∧ m = 1)) : Subgroup.closure (normD T) = hSub T (normIn T₁ T) :=
  le_antisymm ((Subgroup.closure_le _).2 fun _ hx => hc.normD_le_hSub_of_not_a8 h1 h63 hA8 hx)
    hc.hSub_le_closure

theorem Sec6Ctx.card_centralizer_eq (h63 : Sec63) (hc : Sec6Ctx T T₁ n m)
    (hA8 : ¬ (n = 4 ∧ m = 1)) {x : G} (hx : x ∈ normD T) (hxT : x ∉ T) :
    Nat.card ↥(T ⊓ Subgroup.centralizer ({x} : Set G)) = Nat.card ↥(normIn T T₁) := by
  rcases h63 G T T₁ n m hc x hx hxT with hcard | ⟨h16, h8, -⟩
  · exact hcard
  · exact absurd (hc.card_eq_sixteen_iff.1 ⟨h16, h8⟩) hA8

theorem Sec6Ctx.card_index_centralizer_eq (h63 : Sec63) (hc : Sec6Ctx T T₁ n m)
    (hA8 : ¬ (n = 4 ∧ m = 1)) {x : G} (hx : x ∈ normD T) (hxT : x ∉ T) :
    Nat.card T / Nat.card ↥(T ⊓ Subgroup.centralizer ({x} : Set G)) = 2 ^ m ∧
      Nat.card ↥(commSub x T) = 2 ^ m := by
  have := hc.finite
  have hcard := hc.card_centralizer_eq h63 hA8 hx hxT
  have hx2 : x ^ 2 = 1 := by
    rw [pow_two]
    exact mul_self_eq_one_of_mem_classD hc.hy.pair.wc.1 hx.1
  have h23 := card_commSub_mul_card_centralizer (T := T) hc.hy.pair.wc.1 hx2 hx.2
  have hL0 : 0 < Nat.card ↥(normIn T T₁) := Nat.card_pos
  refine ⟨by rw [hcard]; exact hc.hq, ?_⟩
  rw [hcard] at h23
  refine Nat.eq_of_mul_eq_mul_right hL0 ?_
  rw [h23, hc.mul_card_normIn]

end CFSG.CGT.Timmesfeld75
