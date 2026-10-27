module

public import CFSG.LocalAnalysis.RankFourTheoremC.PPointSemilinear

public section

namespace CFSG.LocalAnalysis.RankFourTheoremC.P5

theorem exists_ringEquiv_of_normalizes_p {F : Type} [Field F] [Finite F] {p : ℕ} [CharP F p]
    (hp2 : p ≠ 2) (ψ : F ≃+ F)
    (hnorm : ∀ a : Fˣ, ∃ b : Fˣ, ∀ t, ψ ((a : F) ^ 2 * t) = (b : F) ^ 2 * ψ t) :
    ∃ σ : F ≃+* F, ∀ s t, ψ (s * t) = σ s * ψ t := by
  haveI : Fact p.Prime := ⟨CharP.char_is_prime F p⟩
  have h2 : (2 : F) ≠ 0 := by
    intro h
    have hd : p ∣ 2 := (CharP.cast_eq_zero_iff F p 2).mp (by exact_mod_cast h)
    exact hp2 ((Nat.prime_dvd_prime_iff_eq (Fact.out : p.Prime) Nat.prime_two).mp hd)
  have hsq : ∀ a : F, ∃ r : F, ∀ t, ψ (a ^ 2 * t) = r * ψ t := by
    intro a
    by_cases ha : a = 0
    · exact ⟨0, fun t => by simp [ha]⟩
    · obtain ⟨b, hb⟩ := hnorm (Units.mk0 a ha)
      exact ⟨(b : F) ^ 2, hb⟩
  have hsub : ∀ s s' : F, (∃ r, ∀ t, ψ (s * t) = r * ψ t) →
      (∃ r, ∀ t, ψ (s' * t) = r * ψ t) → ∃ r, ∀ t, ψ ((s - s') * t) = r * ψ t := by
    rintro s s' ⟨r, hr⟩ ⟨r', hr'⟩
    exact ⟨r - r', fun t => by rw [sub_mul, map_sub, hr, hr', sub_mul]⟩
  have hall : ∀ s : F, ∃ r : F, ∀ t, ψ (s * t) = r * ψ t := by
    intro s
    have e : s = ((s + 1) / 2) ^ 2 - ((s - 1) / 2) ^ 2 := by
      field_simp
      ring
    rw [e]
    exact hsub _ _ (hsq _) (hsq _)
  choose r hr using hall
  have hψ1 : ψ 1 ≠ 0 := by
    intro h
    exact one_ne_zero (ψ.injective (h.trans (map_zero ψ).symm))
  let σ : F →+* F :=
    { toFun := r
      map_one' := mul_right_cancel₀ hψ1 (by rw [one_mul, ← hr 1 1, mul_one])
      map_mul' := fun s s' => mul_right_cancel₀ hψ1 (by
        calc r (s * s') * ψ 1 = ψ ((s * s') * 1) := (hr _ _).symm
          _ = ψ (s * (s' * 1)) := by rw [mul_assoc]
          _ = r s * ψ (s' * 1) := hr s _
          _ = r s * (r s' * ψ 1) := by rw [hr s' 1]
          _ = r s * r s' * ψ 1 := by rw [mul_assoc])
      map_zero' := (mul_eq_zero.mp (by rw [← hr 0 1, zero_mul, map_zero] :
        r 0 * ψ 1 = 0)).resolve_right hψ1
      map_add' := fun s s' => mul_right_cancel₀ hψ1 (by
        calc r (s + s') * ψ 1 = ψ ((s + s') * 1) := (hr _ _).symm
          _ = ψ (s * 1) + ψ (s' * 1) := by rw [add_mul, map_add]
          _ = (r s + r s') * ψ 1 := by rw [hr s 1, hr s' 1, add_mul]) }
  exact ⟨RingEquiv.ofBijective σ ⟨σ.injective, Finite.surjective_of_injective σ.injective⟩, hr⟩

theorem card_le_of_fixed_subset_p {F : Type} [Field F] [Finite F] {p : ℕ} [Fact p.Prime]
    [CharP F p] (σ : F ≃+* F) (hσ : ∀ x, σ (σ x) = x)
    (hfix : ∀ x, σ x = x → ∃ m : ℕ, x = (m : F)) : Nat.card F ≤ 2 * p ^ 2 := by
  classical
  have := Fintype.ofFinite F
  have hp0 : 0 < p := (Fact.out : p.Prime).pos
  let g : F → F × F := fun x => (x + σ x, x * σ x)
  have hfib : ∀ x y, g y = g x → y = x ∨ y = σ x := by
    intro x y h
    simp only [g, Prod.mk.injEq] at h
    obtain ⟨h1, h2⟩ := h
    have h0 : (y - x) * (y - σ x) = 0 := by
      calc (y - x) * (y - σ x) = y ^ 2 - (x + σ x) * y + x * σ x := by ring
        _ = y ^ 2 - (y + σ y) * y + y * σ y := by rw [← h1, ← h2]
        _ = 0 := by ring
    rcases mul_eq_zero.mp h0 with h | h
    · exact Or.inl (sub_eq_zero.mp h)
    · exact Or.inr (sub_eq_zero.mp h)
  let P : Finset F := (Finset.range p).image (fun k : ℕ => (k : F))
  have hP : ∀ m : ℕ, (m : F) ∈ P := fun m =>
    Finset.mem_image.mpr ⟨m % p, Finset.mem_range.mpr (Nat.mod_lt m hp0),
      (CharP.cast_eq_mod F p m).symm⟩
  have hPcard : P.card ≤ p := Finset.card_image_le.trans (by simp)
  have hfixP : ∀ y : F, σ y = y → y ∈ P := by
    intro y hy
    obtain ⟨m, hm⟩ := hfix y hy
    rw [hm]
    exact hP m
  have hadd_fix : ∀ x : F, σ (x + σ x) = x + σ x := fun x => by
    rw [map_add, hσ, add_comm]
  have hmul_fix : ∀ x : F, σ (x * σ x) = x * σ x := fun x => by
    rw [map_mul, hσ, mul_comm]
  have himg : ∀ x, g x ∈ P ×ˢ P := fun x =>
    Finset.mem_product.mpr ⟨hfixP _ (hadd_fix x), hfixP _ (hmul_fix x)⟩
  have hG : (Finset.univ.image g).card ≤ p ^ 2 := by
    calc (Finset.univ.image g).card ≤ (P ×ˢ P).card :=
          Finset.card_le_card (fun a ha => by
            obtain ⟨x, -, rfl⟩ := Finset.mem_image.mp ha
            exact himg x)
      _ = P.card * P.card := Finset.card_product P P
      _ ≤ p * p := Nat.mul_le_mul hPcard hPcard
      _ = p ^ 2 := (sq p).symm
  have hmul := Finset.card_le_mul_card_image (Finset.univ : Finset F) 2 (f := g) (by
    intro a ha
    obtain ⟨x, -, rfl⟩ := Finset.mem_image.mp ha
    calc _ ≤ ({x, σ x} : Finset F).card := Finset.card_le_card (fun y hy => by
          simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hy
          simpa using hfib x y hy)
      _ ≤ 2 := Finset.card_le_two)
  rw [Nat.card_eq_fintype_card, ← Finset.card_univ]
  calc Finset.univ.card ≤ 2 * (Finset.univ.image g).card := hmul
    _ ≤ 2 * p ^ 2 := Nat.mul_le_mul (le_refl 2) hG

theorem exists_fixed_not_mem_prime_field_p {F : Type} [Field F] [Finite F] {p n : ℕ} [Fact p.Prime]
    [CharP F p] (hp2 : p ≠ 2) (hF : Nat.card F = p ^ n) (hn : 3 ≤ n) (S : Set (F ≃+* F))
    (hS : ∀ σ ∈ S, ∀ x, σ (σ x) = x) :
    ∃ w : F, (∀ σ ∈ S, σ w = w) ∧ ∀ m : ℕ, w ≠ (m : F) := by
  obtain ⟨σ₀, hσ₀, hle⟩ : ∃ σ₀ : F ≃+* F, (∀ x, σ₀ (σ₀ x) = x) ∧
      ∀ σ ∈ S, ∀ x, σ₀ x = x → σ x = x := by
    by_cases h : ∃ σ₁ ∈ S, ∃ x, σ₁ x ≠ x
    · obtain ⟨σ₁, hσ₁S, hx⟩ := h
      refine ⟨σ₁, hS σ₁ hσ₁S, fun σ hσ x hx' => ?_⟩
      by_cases hσ1 : ∃ y, σ y ≠ y
      · rw [← ringEquiv_eq_of_involutive_of_charP p σ₁ σ (hS σ₁ hσ₁S) (hS σ hσ) hx hσ1]
        exact hx'
      · exact not_not.mp fun hne => hσ1 ⟨x, hne⟩
    · exact ⟨RingEquiv.refl F, fun x => rfl, fun σ hσ x _ =>
        not_not.mp fun hne => h ⟨σ, hσ, x, hne⟩⟩
  have hex : ∃ w : F, σ₀ w = w ∧ ∀ m : ℕ, w ≠ (m : F) := by
    by_contra hcon
    have hfix : ∀ x, σ₀ x = x → ∃ m : ℕ, x = (m : F) := by
      intro x hx
      by_contra hx'
      exact hcon ⟨x, hx, fun m hm => hx' ⟨m, hm⟩⟩
    have hcard := card_le_of_fixed_subset_p σ₀ hσ₀ hfix
    have hp0 : 0 < p := (Fact.out : p.Prime).pos
    have h3 : 3 ≤ p := by
      have := (Fact.out : p.Prime).two_le
      omega
    have hpn : p ^ 3 ≤ p ^ n := Nat.pow_le_pow_right hp0 hn
    have hp2pos : 0 < p ^ 2 := pow_pos hp0 2
    have hlt : 2 * p ^ 2 < p ^ 3 :=
      calc 2 * p ^ 2 < p * p ^ 2 := mul_lt_mul_of_pos_right (by omega) hp2pos
        _ = p ^ 3 := by ring
    have hle' : p ^ n ≤ 2 * p ^ 2 := by
      rw [← hF]
      exact hcard
    exact absurd hle' (not_le.mpr (lt_of_lt_of_le hlt hpn))
  obtain ⟨w, hw, hwm⟩ := hex
  exact ⟨w, fun σ hσ => hle σ hσ w hw, hwm⟩

theorem exists_fixed_not_mem_line_p {F : Type} [Field F] [Finite F] {p n : ℕ} [Fact p.Prime]
    [CharP F p] (hp2 : p ≠ 2) (hF : Nat.card F = p ^ n) (hn : 3 ≤ n) (Ψ : Set (F ≃+ F))
    (hinv : ∀ ψ ∈ Ψ, ∀ t, ψ (ψ t) = t)
    (hnorm : ∀ ψ ∈ Ψ, ∀ a : Fˣ, ∃ b : Fˣ, ∀ t, ψ ((a : F) ^ 2 * t) = (b : F) ^ 2 * ψ t)
    {v : F} (hv : v ≠ 0) (hfix : ∀ ψ ∈ Ψ, ψ v = v) :
    ∃ w : F, (∀ ψ ∈ Ψ, ψ w = w) ∧ ∀ m : ℕ, w ≠ (m : F) * v := by
  have hex : ∀ ψ : Ψ, ∃ σ : F ≃+* F, ∀ s t, (ψ : F ≃+ F) (s * t) = σ s * (ψ : F ≃+ F) t :=
    fun ψ => exists_ringEquiv_of_normalizes_p hp2 (ψ : F ≃+ F) (hnorm ψ ψ.2)
  choose σ hσ using hex
  obtain ⟨w, hwfix, hwm⟩ := exists_fixed_not_mem_prime_field_p hp2 hF hn (Set.range σ) (by
    rintro _ ⟨ψ, rfl⟩
    exact ringEquiv_involutive_of_semilinear (ψ : F ≃+ F) (σ ψ) (hσ ψ) (hinv ψ ψ.2))
  refine ⟨v * w, fun ψ hψ => ?_, fun m h => hwm m (mul_left_cancel₀ hv (h.trans (mul_comm _ _)))⟩
  rw [mul_comm v w, hσ ⟨ψ, hψ⟩ w v, hfix ψ hψ, hwfix _ ⟨⟨ψ, hψ⟩, rfl⟩]

end CFSG.LocalAnalysis.RankFourTheoremC.P5
