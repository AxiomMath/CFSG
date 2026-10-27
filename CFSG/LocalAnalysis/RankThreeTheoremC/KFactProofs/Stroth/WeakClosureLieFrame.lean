module

public import CFSG.LocalAnalysis.RankThreeTheoremC.KFactProofs.Stroth.WeakClosureLieTools

public section

namespace CFSG.LocalAnalysis.RankThreeTheoremC.KFactProofs.Stroth.WeakClosure

open CFSG.Open

variable {K : Type} [Group K] [Finite K] {p : ℕ}

private theorem exists_zpow_of_card_prime [Fact p.Prime] {A : Subgroup K} (hA : Nat.card A = p)
    {y z : K} (hy : y ∈ A) (hy1 : y ≠ 1) (hz : z ∈ A) : ∃ k : ℤ, y ^ k = z := by
  have hord : orderOf y = p := by
    have h1 : orderOf y ∣ Nat.card A := Subgroup.orderOf_dvd_natCard A hy
    rw [hA] at h1
    rcases (Nat.dvd_prime (Fact.out : p.Prime)).1 h1 with h | h
    · exact absurd (orderOf_eq_one_iff.1 h) hy1
    · exact h
  have hle : Subgroup.zpowers y ≤ A := Subgroup.zpowers_le.2 hy
  have heq : Subgroup.zpowers y = A := by
    apply Subgroup.eq_of_le_of_card_ge hle
    rw [hA, Nat.card_zpowers, hord]
  rw [← heq] at hz
  exact Subgroup.mem_zpowers_iff.1 hz

theorem normalizerMovesLines_of_twistedFrame [Fact p.Prime] {a r : ℕ} (hr : 2 ≤ r)
    (P : Subgroup K) (φ : (Fin r → Multiplicative (ZMod (p ^ a))) ≃* P)
    (hswap : ∀ i j : Fin r, ∃ n ∈ Subgroup.normalizer (P : Set K),
      ∀ c, n * (φ c : K) * n⁻¹ = (φ (c ∘ Equiv.swap i j) : K))
    (i₀ : Fin r)
    (htwist : ∃ n ∈ Subgroup.normalizer (P : Set K), ∃ μ : ℤ, ¬ (p : ℤ) ∣ μ - 1 ∧
      ∀ c, n * (φ c : K) * n⁻¹ = (φ (Function.update c i₀ (c i₀ ^ μ)) : K)) :
    NormalizerMovesLines p P := by
  intro A hAP hA
  by_contra hcon
  push Not at hcon
  have hconjA : ∀ n ∈ Subgroup.normalizer (P : Set K), ∀ y ∈ A, n * y * n⁻¹ ∈ A := by
    intro n hn y hy
    rw [← hcon n hn]
    exact ⟨y, hy, by simp [MulAut.conj_apply]⟩
  have hexp : ∀ y ∈ A, y ^ p = 1 := by
    intro y hy
    have := pow_card_eq_one' (G := A) (x := ⟨y, hy⟩)
    rw [hA] at this
    exact congrArg Subtype.val this
  have hcoord : ∀ y ∈ A, ∃ c : Fin r → Multiplicative (ZMod (p ^ a)), (φ c : K) = y := by
    intro y hy
    exact ⟨φ.symm ⟨y, hAP hy⟩, by simp⟩
  have hcp : ∀ c : Fin r → Multiplicative (ZMod (p ^ a)), (φ c : K) ∈ A → ∀ j, c j ^ p = 1 := by
    intro c hc j
    have h1 : (φ c : K) ^ p = 1 := hexp _ hc
    have h2 : φ (c ^ p) = 1 := Subtype.ext (by rw [map_pow]; exact h1)
    have h3 : c ^ p = 1 := φ.injective (by rw [h2, map_one])
    simpa using congrFun h3 j
  have hordp : ∀ x : Multiplicative (ZMod (p ^ a)), x ^ p = 1 → x ≠ 1 → orderOf x = p := by
    intro x hx hx1
    rcases (Nat.dvd_prime (Fact.out : p.Prime)).1 (orderOf_dvd_of_pow_eq_one hx) with h | h
    · exact absurd (orderOf_eq_one_iff.1 h) hx1
    · exact h
  obtain ⟨y₁, hy₁A, hy₁⟩ : ∃ y ∈ A, y ≠ 1 := by
    by_contra h
    push Not at h
    have : A = ⊥ := (Subgroup.eq_bot_iff_forall A).2 h
    rw [this, Subgroup.card_bot] at hA
    exact (Fact.out : p.Prime).one_lt.ne hA
  obtain ⟨c, hcA, hc0⟩ : ∃ c : Fin r → Multiplicative (ZMod (p ^ a)),
      (φ c : K) ∈ A ∧ c i₀ ≠ 1 := by
    obtain ⟨c₁, hc₁⟩ := hcoord y₁ hy₁A
    have hne : c₁ ≠ 1 := by
      rintro rfl
      apply hy₁
      rw [← hc₁, map_one]; rfl
    obtain ⟨j, hj⟩ := Function.ne_iff.1 hne
    by_cases hi : c₁ i₀ = 1
    · have hji : j ≠ i₀ := fun h => hj (h ▸ hi)
      obtain ⟨n, hn, hnc⟩ := hswap i₀ j
      refine ⟨c₁ ∘ Equiv.swap i₀ j, ?_, ?_⟩
      · rw [← hnc, hc₁]; exact hconjA n hn _ hy₁A
      · simp only [Function.comp_apply, Equiv.swap_apply_left]
        exact hj
    · exact ⟨c₁, hc₁ ▸ hy₁A, hi⟩
  have hcne : (φ c : K) ≠ 1 := by
    intro h
    have h1 : φ c = 1 := Subtype.ext h
    have h2 : c = 1 := φ.injective (h1.trans (map_one φ).symm)
    exact hc0 (by rw [h2]; rfl)
  obtain ⟨n₁, hn₁, μ, hμ, hnμ⟩ := htwist
  have hsupp : ∀ j, j ≠ i₀ → c j = 1 := by
    intro j hji
    by_contra hcj
    have hmem := hconjA n₁ hn₁ _ hcA
    rw [hnμ c] at hmem
    obtain ⟨k, hk⟩ := exists_zpow_of_card_prime hA hcA hcne hmem
    have hk' : c ^ k = Function.update c i₀ (c i₀ ^ μ) :=
      φ.injective (Subtype.ext (by rw [map_zpow]; exact hk))
    have e1 := congrFun hk' j
    have e2 := congrFun hk' i₀
    simp only [Pi.pow_apply, Function.update_of_ne hji, Function.update_self] at e1 e2
    have hcjp : (c j) ^ p = 1 := hcp c hcA j
    have hojc : orderOf (c j) = p := hordp _ hcjp hcj
    have hk1 : (p : ℤ) ∣ k - 1 := by
      rw [← hojc]
      refine orderOf_dvd_iff_zpow_eq_one.2 ?_
      rw [zpow_sub, e1, zpow_one, mul_inv_cancel]
    have hc0p : (c i₀) ^ p = 1 := hcp c hcA i₀
    have hoc0 : orderOf (c i₀) = p := hordp _ hc0p hc0
    have hkk : c i₀ ^ k = c i₀ := by
      obtain ⟨m, hm⟩ := hk1
      have : k = 1 + (p : ℤ) * m := by omega
      rw [this, zpow_add, zpow_one, zpow_mul, zpow_natCast, hc0p, one_zpow, mul_one]
    have h3 : c i₀ ^ μ = c i₀ := by rw [← e2, hkk]
    have hμ1 : c i₀ ^ (μ - 1) = 1 := by
      rw [zpow_sub, zpow_one, h3, mul_inv_cancel]
    exact hμ (by rw [← hoc0]; exact orderOf_dvd_iff_zpow_eq_one.2 hμ1)
  obtain ⟨j₁, hj₁⟩ : ∃ j : Fin r, j ≠ i₀ := by
    by_cases h0 : i₀.val = 0
    · exact ⟨⟨1, by omega⟩, fun h => by have := congrArg Fin.val h; simp at this; omega⟩
    · exact ⟨⟨0, by omega⟩, fun h => by have := congrArg Fin.val h; simp at this; omega⟩
  obtain ⟨n₂, hn₂, hnc₂⟩ := hswap i₀ j₁
  have hmem₂ := hconjA n₂ hn₂ _ hcA
  rw [hnc₂ c] at hmem₂
  obtain ⟨k, hk⟩ := exists_zpow_of_card_prime hA hcA hcne hmem₂
  have hk' : c ^ k = c ∘ Equiv.swap i₀ j₁ :=
    φ.injective (Subtype.ext (by rw [map_zpow]; exact hk))
  have e := congrFun hk' j₁
  simp only [Pi.pow_apply, Function.comp_apply, Equiv.swap_apply_right, hsupp j₁ hj₁,
    one_zpow] at e
  exact hc0 e.symm

@[expose] def prodOneSubgroup (C : Type*) [CommGroup C] (r : ℕ) : Subgroup (Fin r → C) where
  carrier := {c | ∏ i, c i = 1}
  mul_mem' := by
    intro a b ha hb
    simp only [Set.mem_setOf_eq, Pi.mul_apply, Finset.prod_mul_distrib] at *
    rw [ha, hb, one_mul]
  one_mem' := by simp
  inv_mem' := by
    intro a ha
    simp only [Set.mem_setOf_eq, Pi.inv_apply, Finset.prod_inv_distrib] at *
    rw [ha, inv_one]

theorem mem_prodOneSubgroup {C : Type*} [CommGroup C] {r : ℕ} {c : Fin r → C} :
    c ∈ prodOneSubgroup C r ↔ ∏ i, c i = 1 := Iff.rfl

theorem normalizerMovesLines_of_sumZeroFrame [Fact p.Prime] {a r : ℕ} (hr : 3 ≤ r)
    (hpr : ¬ p ∣ r) (P : Subgroup K)
    (φ : prodOneSubgroup (Multiplicative (ZMod (p ^ a))) r ≃* P)
    (hswap : ∀ i j : Fin r, ∃ n ∈ Subgroup.normalizer (P : Set K),
      ∀ c : prodOneSubgroup (Multiplicative (ZMod (p ^ a))) r,
        ∃ c' : prodOneSubgroup (Multiplicative (ZMod (p ^ a))) r,
          (c' : Fin r → Multiplicative (ZMod (p ^ a))) =
              (c : Fin r → Multiplicative (ZMod (p ^ a))) ∘ Equiv.swap i j ∧
            n * (φ c : K) * n⁻¹ = (φ c' : K)) :
    NormalizerMovesLines p P := by
  intro A hAP hA
  by_contra hcon
  push Not at hcon
  have hconjA : ∀ n ∈ Subgroup.normalizer (P : Set K), ∀ y ∈ A, n * y * n⁻¹ ∈ A := by
    intro n hn y hy
    rw [← hcon n hn]
    exact ⟨y, hy, by simp [MulAut.conj_apply]⟩
  have hexp : ∀ y ∈ A, y ^ p = 1 := by
    intro y hy
    have := pow_card_eq_one' (G := A) (x := ⟨y, hy⟩)
    rw [hA] at this
    exact congrArg Subtype.val this
  have hcp : ∀ c : prodOneSubgroup (Multiplicative (ZMod (p ^ a))) r, (φ c : K) ∈ A →
      ∀ j, (c : Fin r → Multiplicative (ZMod (p ^ a))) j ^ p = 1 := by
    intro c hc j
    have h1 : (φ c : K) ^ p = 1 := hexp _ hc
    have h2 : φ (c ^ p) = 1 := Subtype.ext (by rw [map_pow]; exact h1)
    have h3 : c ^ p = 1 := φ.injective (by rw [h2, map_one])
    have h4 := congrArg (fun z : prodOneSubgroup (Multiplicative (ZMod (p ^ a))) r =>
      (z : Fin r → Multiplicative (ZMod (p ^ a))) j) h3
    simpa using h4
  have hordp : ∀ x : Multiplicative (ZMod (p ^ a)), x ^ p = 1 → x ≠ 1 → orderOf x = p := by
    intro x hx hx1
    rcases (Nat.dvd_prime (Fact.out : p.Prime)).1 (orderOf_dvd_of_pow_eq_one hx) with h | h
    · exact absurd (orderOf_eq_one_iff.1 h) hx1
    · exact h
  have hsw : ∀ (i j : Fin r) (c : prodOneSubgroup (Multiplicative (ZMod (p ^ a))) r),
      (φ c : K) ∈ A → (φ c : K) ≠ 1 → ∃ k : ℤ, ∀ m,
        (c : Fin r → Multiplicative (ZMod (p ^ a))) (Equiv.swap i j m) =
          (c : Fin r → Multiplicative (ZMod (p ^ a))) m ^ k := by
    intro i j c hcA hc1
    obtain ⟨n, hn, hnc⟩ := hswap i j
    obtain ⟨c', hc'val, hnφ⟩ := hnc c
    have hmem : (φ c' : K) ∈ A := by rw [← hnφ]; exact hconjA n hn _ hcA
    obtain ⟨k, hk⟩ := exists_zpow_of_card_prime hA hcA hc1 hmem
    have hck : c ^ k = c' := φ.injective (Subtype.ext (by rw [map_zpow]; exact hk))
    refine ⟨k, fun m => ?_⟩
    have h1 := congrArg (fun z : prodOneSubgroup (Multiplicative (ZMod (p ^ a))) r =>
      (z : Fin r → Multiplicative (ZMod (p ^ a))) m) hck
    simp only [Subgroup.coe_zpow, Pi.pow_apply, hc'val, Function.comp_apply] at h1
    exact h1.symm
  obtain ⟨y₁, hy₁A, hy₁⟩ : ∃ y ∈ A, y ≠ 1 := by
    by_contra h
    push Not at h
    have : A = ⊥ := (Subgroup.eq_bot_iff_forall A).2 h
    rw [this, Subgroup.card_bot] at hA
    exact (Fact.out : p.Prime).one_lt.ne hA
  obtain ⟨c, hc⟩ : ∃ c : prodOneSubgroup (Multiplicative (ZMod (p ^ a))) r, (φ c : K) = y₁ :=
    ⟨φ.symm ⟨y₁, hAP hy₁A⟩, by simp⟩
  have hcA : (φ c : K) ∈ A := hc ▸ hy₁A
  have hc1 : (φ c : K) ≠ 1 := hc ▸ hy₁
  have hcne : c ≠ 1 := fun h => hc1 (by rw [h]; simp)
  have hprod : ∏ i, (c : Fin r → Multiplicative (ZMod (p ^ a))) i = 1 := c.2
  obtain ⟨i, j, hij⟩ : ∃ i j : Fin r, (c : Fin r → Multiplicative (ZMod (p ^ a))) i ≠
      (c : Fin r → Multiplicative (ZMod (p ^ a))) j := by
    by_contra hall
    push Not at hall
    let i0 : Fin r := ⟨0, by omega⟩
    have hz : ∀ i, (c : Fin r → Multiplicative (ZMod (p ^ a))) i =
        (c : Fin r → Multiplicative (ZMod (p ^ a))) i0 := fun i => hall i i0
    have hpow : (c : Fin r → Multiplicative (ZMod (p ^ a))) i0 ^ r = 1 := by
      rw [← hprod, Finset.prod_congr rfl (fun i _ => hz i)]
      simp
    by_cases hz1 : (c : Fin r → Multiplicative (ZMod (p ^ a))) i0 = 1
    · exact hcne (Subtype.ext (funext fun i => by rw [hz i, hz1]; rfl))
    · have hord := hordp _ (hcp c hcA i0) hz1
      exact hpr (hord ▸ orderOf_dvd_of_pow_eq_one hpow)
  have hji : i ≠ j := fun h => hij (h ▸ rfl)
  obtain ⟨k, hk⟩ := hsw i j c hcA hc1
  have hrest : ∀ m, m ≠ i → m ≠ j →
      (c : Fin r → Multiplicative (ZMod (p ^ a))) m = 1 := by
    intro m hmi hmj
    by_contra hcm
    have h1 := hk m
    rw [Equiv.swap_apply_of_ne_of_ne hmi hmj] at h1
    have hcmp := hcp c hcA m
    have hom := hordp _ hcmp hcm
    have hdvd : (p : ℤ) ∣ k - 1 := by
      rw [← hom]
      refine orderOf_dvd_iff_zpow_eq_one.2 ?_
      rw [zpow_sub, ← h1, zpow_one, mul_inv_cancel]
    obtain ⟨t, ht⟩ := hdvd
    have hk' : k = 1 + (p : ℤ) * t := by omega
    have hcip := hcp c hcA i
    have hki : (c : Fin r → Multiplicative (ZMod (p ^ a))) i ^ k =
        (c : Fin r → Multiplicative (ZMod (p ^ a))) i := by
      rw [hk', zpow_add, zpow_one, zpow_mul, zpow_natCast, hcip, one_zpow, mul_one]
    have h2 := hk i
    rw [Equiv.swap_apply_left, hki] at h2
    exact hij h2.symm
  have hprod2 : (c : Fin r → Multiplicative (ZMod (p ^ a))) i *
      (c : Fin r → Multiplicative (ZMod (p ^ a))) j = 1 := by
    rw [← hprod]
    exact (Fintype.prod_eq_mul i j hji (fun x hx => hrest x hx.1 hx.2)).symm
  obtain ⟨l, -, hl⟩ : ∃ l ∈ (Finset.univ : Finset (Fin r)), l ∉ ({i, j} : Finset (Fin r)) := by
    apply Finset.exists_mem_notMem_of_card_lt_card
    rw [Finset.card_univ, Fintype.card_fin]
    exact lt_of_le_of_lt Finset.card_le_two (by omega)
  have hli : l ≠ i := fun h => hl (by simp [h])
  have hlj : l ≠ j := fun h => hl (by simp [h])
  obtain ⟨k', hk''⟩ := hsw i l c hcA hc1
  have hcl := hrest l hli hlj
  have e1 := hk'' l
  rw [Equiv.swap_apply_right, hcl, one_zpow] at e1
  have hci : (c : Fin r → Multiplicative (ZMod (p ^ a))) i = 1 := e1
  have hcj : (c : Fin r → Multiplicative (ZMod (p ^ a))) j = 1 := by
    rw [hci, one_mul] at hprod2
    exact hprod2
  exact hij (hci.trans hcj.symm)

end CFSG.LocalAnalysis.RankThreeTheoremC.KFactProofs.Stroth.WeakClosure
