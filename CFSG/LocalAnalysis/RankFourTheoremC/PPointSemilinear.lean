module

public import Mathlib.FieldTheory.Finite.Basic
import Mathlib.Algebra.Algebra.ZMod

public section

namespace CFSG.LocalAnalysis.RankFourTheoremC

theorem charP_three_of_card_eq_pow {F : Type} [Field F] [Finite F] {n : ℕ}
    (hF : Nat.card F = 3 ^ n) : CharP F 3 := by
  have := Fintype.ofFinite F
  obtain ⟨p, hp, m, hpp, hm⟩ := FiniteField.card' F
  rw [Nat.card_eq_fintype_card] at hF
  have hdvd : p ∣ 3 ^ n := by
    rw [← hF, hm]
    exact dvd_pow_self p m.ne_zero
  have hp3 : p = 3 :=
    (Nat.prime_dvd_prime_iff_eq hpp Nat.prime_three).mp (hpp.dvd_of_dvd_pow hdvd)
  subst hp3
  exact hp

theorem exists_ringEquiv_of_normalizes {F : Type} [Field F] [Finite F] [CharP F 3]
    (ψ : F ≃+ F) (hnorm : ∀ a : Fˣ, ∃ b : Fˣ, ∀ t, ψ ((a : F) ^ 2 * t) = (b : F) ^ 2 * ψ t) :
    ∃ σ : F ≃+* F, ∀ s t, ψ (s * t) = σ s * ψ t := by
  have h3 : (3 : F) = 0 := by exact_mod_cast CharP.cast_eq_zero F 3
  have hsq : ∀ a : F, ∃ r : F, ∀ t, ψ (a ^ 2 * t) = r * ψ t := by
    intro a
    by_cases ha : a = 0
    · exact ⟨0, fun t => by simp [ha]⟩
    · obtain ⟨b, hb⟩ := hnorm (Units.mk0 a ha)
      exact ⟨(b : F) ^ 2, hb⟩
  have hadd : ∀ s s' : F, (∃ r, ∀ t, ψ (s * t) = r * ψ t) → (∃ r, ∀ t, ψ (s' * t) = r * ψ t) →
      ∃ r, ∀ t, ψ ((s + s') * t) = r * ψ t := by
    rintro s s' ⟨r, hr⟩ ⟨r', hr'⟩
    exact ⟨r + r', fun t => by rw [add_mul, map_add, hr, hr', add_mul]⟩
  have hall : ∀ s : F, ∃ r : F, ∀ t, ψ (s * t) = r * ψ t := by
    intro s
    have e : s = (s + 1) ^ 2 + (s - 1) ^ 2 + (s - 1) ^ 2 := by
      linear_combination (s - s ^ 2 - 1) * h3
    rw [e]
    exact hadd _ _ (hadd _ _ (hsq _) (hsq _)) (hsq _)
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

theorem ringEquiv_involutive_of_semilinear {F : Type} [Field F] (ψ : F ≃+ F) (σ : F ≃+* F)
    (hσ : ∀ s t, ψ (s * t) = σ s * ψ t) (hinv : ∀ t, ψ (ψ t) = t) (x : F) : σ (σ x) = x := by
  have h1 : ψ x = σ x * ψ 1 := by simpa using hσ x 1
  calc σ (σ x) = σ (σ x) * ψ (ψ 1) := by rw [hinv, mul_one]
    _ = ψ (σ x * ψ 1) := (hσ _ _).symm
    _ = ψ (ψ x) := by rw [h1]
    _ = x := hinv x

theorem ringEquiv_eq_of_involutive_of_charP {F : Type} [Field F] [Finite F] (p : ℕ) [Fact p.Prime]
    [CharP F p] (σ τ : F ≃+* F) (hσ : ∀ x, σ (σ x) = x) (hτ : ∀ x, τ (τ x) = x)
    (hσ1 : ∃ x, σ x ≠ x) (hτ1 : ∃ x, τ x ≠ x) : σ = τ := by
  classical
  let _ : Algebra (ZMod p) F := ZMod.algebra F p
  have key : ∀ ρ : F ≃+* F, ∀ x : ZMod p,
      ρ (algebraMap (ZMod p) F x) = algebraMap (ZMod p) F x := fun ρ x =>
    DFunLike.congr_fun (RingHom.ext_zmod ((ρ : F →+* F).comp (algebraMap (ZMod p) F))
      (algebraMap (ZMod p) F)) x
  obtain ⟨σ', hσ'⟩ : ∃ σ' : F ≃ₐ[ZMod p] F, ∀ x, σ' x = σ x :=
    ⟨AlgEquiv.ofRingEquiv (key σ), fun _ => rfl⟩
  obtain ⟨τ', hτ'⟩ : ∃ τ' : F ≃ₐ[ZMod p] F, ∀ x, τ' x = τ x :=
    ⟨AlgEquiv.ofRingEquiv (key τ), fun _ => rfl⟩
  have : Finite (F ≃ₐ[ZMod p] F) :=
    Finite.of_injective (fun f : F ≃ₐ[ZMod p] F => (f : F → F)) DFunLike.coe_injective
  have := Fintype.ofFinite (F ≃ₐ[ZMod p] F)
  have hcard := IsCyclic.card_pow_eq_one_le (α := F ≃ₐ[ZMod p] F) (n := 2) (by norm_num)
  by_contra hne
  have hσ'1 : σ' ≠ 1 := by
    intro h
    obtain ⟨x, hx⟩ := hσ1
    exact hx (by rw [← hσ', h]; rfl)
  have hτ'1 : τ' ≠ 1 := by
    intro h
    obtain ⟨x, hx⟩ := hτ1
    exact hx (by rw [← hτ', h]; rfl)
  have hne' : σ' ≠ τ' := by
    intro h
    exact hne (RingEquiv.ext fun x => by rw [← hσ', ← hτ', h])
  have hsub : ({1, σ', τ'} : Finset (F ≃ₐ[ZMod p] F)) ⊆
      Finset.univ.filter (fun a : F ≃ₐ[ZMod p] F => a ^ 2 = 1) := by
    intro a ha
    simp only [Finset.mem_insert, Finset.mem_singleton] at ha
    simp only [Finset.mem_filter, Finset.mem_univ, true_and]
    rcases ha with rfl | rfl | rfl
    · simp
    · ext x
      simp [pow_two, hσ', hσ]
    · ext x
      simp [pow_two, hτ', hτ]
  have h3 : ({1, σ', τ'} : Finset (F ≃ₐ[ZMod p] F)).card = 3 := by
    rw [Finset.card_insert_of_notMem, Finset.card_pair hne']
    simp only [Finset.mem_insert, Finset.mem_singleton, not_or]
    exact ⟨hσ'1.symm, hτ'1.symm⟩
  have := Finset.card_le_card hsub
  omega

theorem card_le_eighteen_of_fixed_subset {F : Type} [Field F] [Finite F] (σ : F ≃+* F)
    (hσ : ∀ x, σ (σ x) = x) (hfix : ∀ x, σ x = x → x = 0 ∨ x = 1 ∨ x = -1) :
    Nat.card F ≤ 18 := by
  classical
  have := Fintype.ofFinite F
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
  have himg : ∀ x, g x ∈ ({0, 1, -1} : Finset F) ×ˢ ({0, 1, -1} : Finset F) := by
    intro x
    simp only [Finset.mem_product, Finset.mem_insert, Finset.mem_singleton]
    constructor
    · exact hfix _ (by rw [map_add, hσ, add_comm])
    · exact hfix _ (by rw [map_mul, hσ, mul_comm])
  have hT : (({0, 1, -1} : Finset F) ×ˢ ({0, 1, -1} : Finset F)).card ≤ 9 := by
    rw [Finset.card_product]
    have := Finset.card_le_three (a := (0 : F)) (b := 1) (c := -1)
    nlinarith
  have himg_card : (Finset.univ.image g).card ≤ 9 :=
    (Finset.card_le_card (fun a ha => by
      obtain ⟨x, -, rfl⟩ := Finset.mem_image.mp ha
      exact himg x)).trans hT
  have hmul := Finset.card_le_mul_card_image (Finset.univ : Finset F) 2 (f := g) (by
    intro a ha
    obtain ⟨x, -, rfl⟩ := Finset.mem_image.mp ha
    calc _ ≤ ({x, σ x} : Finset F).card := Finset.card_le_card (fun y hy => by
          simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hy
          simpa using hfib x y hy)
      _ ≤ 2 := Finset.card_le_two)
  rw [Nat.card_eq_fintype_card, ← Finset.card_univ]
  omega

theorem exists_fixed_not_mem_prime_field {F : Type} [Field F] [Finite F] [CharP F 3] {n : ℕ}
    (hF : Nat.card F = 3 ^ n) (hn : 3 ≤ n) (S : Set (F ≃+* F))
    (hS : ∀ σ ∈ S, ∀ x, σ (σ x) = x) :
    ∃ w : F, (∀ σ ∈ S, σ w = w) ∧ w ≠ 0 ∧ w ≠ 1 ∧ w ≠ -1 := by
  obtain ⟨σ₀, hσ₀, hle⟩ : ∃ σ₀ : F ≃+* F, (∀ x, σ₀ (σ₀ x) = x) ∧
      ∀ σ ∈ S, ∀ x, σ₀ x = x → σ x = x := by
    by_cases h : ∃ σ₁ ∈ S, ∃ x, σ₁ x ≠ x
    · obtain ⟨σ₁, hσ₁S, hx⟩ := h
      refine ⟨σ₁, hS σ₁ hσ₁S, fun σ hσ x hx' => ?_⟩
      by_cases hσ1 : ∃ y, σ y ≠ y
      · rw [← ringEquiv_eq_of_involutive_of_charP 3 σ₁ σ (hS σ₁ hσ₁S) (hS σ hσ) hx hσ1]
        exact hx'
      · exact not_not.mp fun hne => hσ1 ⟨x, hne⟩
    · exact ⟨RingEquiv.refl F, fun x => rfl, fun σ hσ x _ =>
        not_not.mp fun hne => h ⟨σ, hσ, x, hne⟩⟩
  have hex : ∃ w : F, σ₀ w = w ∧ w ≠ 0 ∧ w ≠ 1 ∧ w ≠ -1 := by
    by_contra hcon
    have hfix : ∀ x, σ₀ x = x → x = 0 ∨ x = 1 ∨ x = -1 := by
      intro x hx
      by_contra hx'
      exact hcon ⟨x, hx, fun h => hx' (Or.inl h), fun h => hx' (Or.inr (Or.inl h)),
        fun h => hx' (Or.inr (Or.inr h))⟩
    have h18 := card_le_eighteen_of_fixed_subset σ₀ hσ₀ hfix
    have h27 : 3 ^ 3 ≤ 3 ^ n := Nat.pow_le_pow_right (by norm_num) hn
    omega
  obtain ⟨w, hw, h0, h1, h1'⟩ := hex
  exact ⟨w, fun σ hσ => hle σ hσ w hw, h0, h1, h1'⟩

theorem exists_fixed_not_mem_line {F : Type} [Field F] [Finite F] {n : ℕ}
    (hF : Nat.card F = 3 ^ n) (hn : 3 ≤ n) (Ψ : Set (F ≃+ F))
    (hinv : ∀ ψ ∈ Ψ, ∀ t, ψ (ψ t) = t)
    (hnorm : ∀ ψ ∈ Ψ, ∀ a : Fˣ, ∃ b : Fˣ, ∀ t, ψ ((a : F) ^ 2 * t) = (b : F) ^ 2 * ψ t)
    {v : F} (hv : v ≠ 0) (hfix : ∀ ψ ∈ Ψ, ψ v = v) :
    ∃ w : F, (∀ ψ ∈ Ψ, ψ w = w) ∧ w ≠ 0 ∧ w ≠ v ∧ w ≠ -v := by
  have := charP_three_of_card_eq_pow hF
  have hex : ∀ ψ : Ψ, ∃ σ : F ≃+* F, ∀ s t, (ψ : F ≃+ F) (s * t) = σ s * (ψ : F ≃+ F) t :=
    fun ψ => exists_ringEquiv_of_normalizes (ψ : F ≃+ F) (hnorm ψ ψ.2)
  choose σ hσ using hex
  obtain ⟨w, hwfix, hw0, hw1, hw1'⟩ := exists_fixed_not_mem_prime_field hF hn (Set.range σ) (by
    rintro _ ⟨ψ, rfl⟩
    exact ringEquiv_involutive_of_semilinear (ψ : F ≃+ F) (σ ψ) (hσ ψ) (hinv ψ ψ.2))
  refine ⟨v * w, fun ψ hψ => ?_, mul_ne_zero hv hw0, fun h => hw1 ?_, fun h => hw1' ?_⟩
  · rw [mul_comm v w, hσ ⟨ψ, hψ⟩ w v, hfix ψ hψ, hwfix _ ⟨⟨ψ, hψ⟩, rfl⟩]
  · exact mul_left_cancel₀ hv (by rw [mul_one]; exact h)
  · exact mul_left_cancel₀ hv (by rw [mul_neg, mul_one]; exact h)

end CFSG.LocalAnalysis.RankFourTheoremC
