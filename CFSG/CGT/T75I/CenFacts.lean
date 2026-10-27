module

public import CFSG.CGT.Timmesfeld75.Sec3OddSubgroup
public import CFSG.CGT.T75I.HatData
public import CFSG.CGT.Timmesfeld75.Sec3TwelveAlg
public import CFSG.CGT.Timmesfeld75.Sec6Ctx

public section

namespace CFSG.CGT.T75I

open CFSG.Open CFSG.CGT.Timmesfeld75
open scoped MatrixGroups

section Facts

variable {G : Type} [Group G] {T T₁ : Subgroup G}

theorem ctx_card_T (hc : Sec6Ctx T T₁ 2 2) : Nat.card T = 16 := by
  rw [hc.hT]
  norm_num

theorem ctx_card_L (hc : Sec6Ctx T T₁ 2 2) : Nat.card (normIn T T₁) = 4 := by
  rw [hc.card_normIn]
  norm_num

theorem ctx_card_T₁ (hc : Sec6Ctx T T₁ 2 2) : Nat.card T₁ = 16 := by
  obtain ⟨x, hx⟩ := hc.hy.pair.conj
  rw [hx, card_conjSubgroup, ctx_card_T hc]

theorem ctx_card_L₁ (hc : Sec6Ctx T T₁ 2 2) : Nat.card (normIn T₁ T) = 4 := by
  rw [hc.card_normIn_swap, ctx_card_L hc]

theorem ctx_not_le_normalizer (hc : Sec6Ctx T T₁ 2 2) :
    ¬ T₁ ≤ Subgroup.normalizer (T : Set G) := by
  intro h
  have h1 : normIn T₁ T = T₁ := inf_eq_left.2 h
  have h4 := ctx_card_L₁ hc
  rw [h1, ctx_card_T₁ hc] at h4
  omega

theorem ctx_not_le_normalizer' (hc : Sec6Ctx T T₁ 2 2) :
    ¬ T ≤ Subgroup.normalizer (T₁ : Set G) := by
  intro h
  have h1 : normIn T T₁ = T := inf_eq_left.2 h
  have h4 := ctx_card_L hc
  rw [h1, ctx_card_T hc] at h4
  omega

theorem ctx_eq_one_of_centralizes_T₁ (hc : Sec6Ctx T T₁ 2 2) {t : G} (ht : t ∈ T)
    (h : ∀ y ∈ T₁, t * y = y * t) : t = 1 := by
  by_contra ht1
  apply ctx_not_le_normalizer hc
  intro y hy
  exact hc.hy.pair.wc.centralizer_le_normalizer ht ht1
    (Subgroup.mem_centralizer_singleton_iff.2 (h y hy).symm)

theorem ctx_eq_one_of_centralizes_T (hc : Sec6Ctx T T₁ 2 2) {y : G} (hy : y ∈ T₁)
    (h : ∀ t ∈ T, y * t = t * y) : y = 1 := by
  by_contra hy1
  apply ctx_not_le_normalizer' hc
  intro t ht
  exact hc.sec3.cfg.wc₁.centralizer_le_normalizer hy hy1
    (Subgroup.mem_centralizer_singleton_iff.2 (h t ht).symm)

theorem ctx_exists_iso_two (hc : Sec6Ctx T T₁ 2 2) :
    ∃ _ : ((cfgM T T₁).subgroupOf (T ⊔ T₁)).Normal,
      Nonempty (↥(T ⊔ T₁) ⧸ (cfgM T T₁).subgroupOf (T ⊔ T₁) ≃* PSL(2, GaloisField 2 2)) := by
  have := hc.finite
  have hP := hc.hy.pair
  obtain ⟨hN, f, hf, hiso⟩ : Sec3Iso T T₁ :=
    sec3Iso_of_conj_conj hc.hI ⟨1, (conjSubgroup_one T).symm⟩ hP.conj hP.ne hP.nontriv
  have h1 := hc.sec3.card_eq_mul hf hiso
  rw [ctx_card_T hc, ctx_card_L hc] at h1
  have h2 : 2 ^ f = 2 ^ 2 := by omega
  have h3 : f = 2 := Nat.pow_right_injective (le_refl 2) h2
  subst h3
  exact ⟨hN, hiso⟩

end Facts

theorem odd_index_of_pair {X : Type} [Group X] [Finite X] {S : Subgroup X} {q : ℕ}
    (h : IsL2Pair X S q) : Odd S.index := by
  obtain ⟨n, hn, hq⟩ := IsL2Pair.exists_eq_two_pow h
  have h1 : S.index * Nat.card S = Nat.card X := S.index_mul_card
  rw [IsL2Pair.card_eq h, IsL2Pair.card_eq_mul h] at h1
  have hq0 : 0 < q := by rw [hq]; positivity
  have h2 : S.index = q ^ 2 - 1 := Nat.eq_of_mul_eq_mul_right hq0 (by rw [h1]; ring)
  have h3 : 2 ∣ q ^ 2 := by
    rw [hq, ← pow_mul]
    exact dvd_pow_self 2 (by omega)
  obtain ⟨c, hc⟩ := h3
  have h4 : 0 < q ^ 2 := by positivity
  rw [h2]
  exact ⟨c - 1, by omega⟩

theorem exists_conj_involutions_of_hat {Y : Type} [Group Y] (h : IsHatA 6 Y ∨ IsHatA 7 Y) :
    ∀ x y : Y, x ≠ 1 → x * x = 1 → y ≠ 1 → y * y = 1 → ∃ g : Y, g * x * g⁻¹ = y := by
  intro x y hx hx2 hy hy2
  rcases h with h | h
  · obtain ⟨-, Z, f, hd⟩ := IsHatA.exists_data h
    exact hd.exists_conj_of_involutions (Or.inl rfl) hx hx2 hy hy2
  · obtain ⟨-, Z, f, hd⟩ := IsHatA.exists_data h
    exact hd.exists_conj_of_involutions (Or.inr rfl) hx hx2 hy hy2

section Facts2

variable {G : Type} [Group G] {T T₁ : Subgroup G}

theorem ctx_eq_one_of_centralizes_hSub (h57 : Step57) (hc : Sec6Ctx T T₁ 2 2) {t : G}
    (ht : t ∈ T) (h : ∀ x ∈ hSub T (normIn T₁ T), x * t = t * x) : t = 1 := by
  have := hc.finite
  by_contra ht1
  have h2 : 2 < Nat.card T := by rw [ctx_card_T hc]; norm_num
  obtain ⟨u, hu, hu1, v, hv, hv1, huv⟩ := exists_ne_one_ne_of_two_lt_natCard h2
  have key : ∀ y ∈ T, y ≠ 1 → y = t := by
    intro y hy hy1
    obtain ⟨x, hx, hxt⟩ := h57 G T T₁ hc.hy t ht ht1 y hy hy1
    rw [← hxt, h x hx]
    group
  exact huv ((key u hu hu1).trans (key v hv hv1).symm)

theorem ctx_exists_odd_element (hc : Sec6Ctx T T₁ 2 2)
    [hN : ((cfgM T T₁).subgroupOf (T ⊔ T₁)).Normal]
    (h : Nonempty (↥(T ⊔ T₁) ⧸ (cfgM T T₁).subgroupOf (T ⊔ T₁) ≃* PSL(2, GaloisField 2 2))) :
    ∃ w ∈ T ⊔ T₁, w ∈ Subgroup.normalizer (T : Set G) ∧ w ≠ 1 ∧
      ∀ m ∈ cfgM T T₁, w * m * w⁻¹ = m → m = 1 := by
  have := hc.finite
  obtain ⟨K, hKX, hKN, hKc, hKfree⟩ :=
    hc.sec3.exists_odd_normalizing_subgroup (f := 2) (by norm_num) h
  have hK1 : 1 < Nat.card K := by
    rw [hKc]
    norm_num
  obtain ⟨⟨w, hw⟩, hw1⟩ :=
    Subgroup.ne_bot_iff_exists_ne_one.1 ((Subgroup.one_lt_card_iff_ne_bot K).1 hK1)
  have hw1' : w ≠ 1 := fun h' => hw1 (Subtype.ext h')
  exact ⟨w, hKX hw, hKN hw, hw1', hKfree w hw hw1'⟩

end Facts2

end CFSG.CGT.T75I
