module

public import CFSG.LieType.SeitzGeneration.ExcWideThree.TwE6LongRootLeviBase
public import CFSG.LieType.SeitzGeneration.ExcWideThree.TwE6LongRootLeviEven
import CFSG.Timmesfeld.Orders.ExceptionalTwistedUnipotent

public section

namespace CFSG.LieType.SeitzGeneration.ExcWideThree.TwE6LongRoot

open CFSG.Blueprint CFSG.Blueprint.Chevalley CFSG.LieType.Chevalley

namespace LeviAux

theorem exists_unit_sq_ne_one_of_four_le {F : Type*} [Field F] [Finite F] (h : 4 ≤ Nat.card F) :
    ∃ u : Fˣ, (u : F) ^ 2 ≠ 1 := by
  classical
  haveI := Fintype.ofFinite F
  exact exists_unit_sq_ne_one ⟨Finset.univ, by rw [Finset.card_univ, ← Nat.card_eq_fintype_card]; exact h⟩

theorem two_le_of_card_eq_sq {K : Type} [Field K] [Finite K] {q : ℕ} (hK : Nat.card K = q ^ 2) :
    2 ≤ q := by
  have h1 : 1 < Nat.card K := Finite.one_lt_card
  rw [hK] at h1
  by_contra h
  interval_cases q <;> simp at h1

theorem q_cases {K : Type} [Field K] [Finite K] {q : ℕ} (hr : ringChar K ≠ 3)
    (hK : Nat.card K = q ^ 2) :
    ∃ p f : ℕ, p.Prime ∧ 1 ≤ f ∧ q = p ^ f ∧ ((q = 2 ∧ (2 : K) = 0) ∨ 4 ≤ q) := by
  have hq2 := two_le_of_card_eq_sq hK
  haveI := Fintype.ofFinite K
  obtain ⟨p, hpK, n, hp, hcard⟩ := FiniteField.card' K
  rw [← Nat.card_eq_fintype_card, hK] at hcard
  have hdvd : q ∣ p ^ (n : ℕ) := ⟨q, by rw [← hcard]; ring⟩
  obtain ⟨k, -, hk⟩ := (Nat.dvd_prime_pow hp).mp hdvd
  have hk1 : 1 ≤ k := by
    rcases Nat.eq_zero_or_pos k with h | h
    · rw [h, pow_zero] at hk
      omega
    · exact h
  have hchar : ringChar K = p := ringChar.eq K p
  refine ⟨p, k, hp, hk1, hk, ?_⟩
  by_cases hq3 : q = 3
  · exfalso
    have h3 : p ∣ 3 := by
      rw [← hq3, hk]
      exact dvd_pow_self p (by omega)
    exact hr (hchar.trans ((Nat.prime_dvd_prime_iff_eq hp Nat.prime_three).1 h3))
  · by_cases hq2' : q = 2
    · left
      refine ⟨hq2', ?_⟩
      have h2 : p ∣ 2 := by
        rw [← hq2', hk]
        exact dvd_pow_self p (by omega)
      have hp2 : p = 2 := (Nat.prime_dvd_prime_iff_eq hp Nat.prime_two).1 h2
      subst hp2
      exact_mod_cast CharP.cast_eq_zero K 2
    · right
      omega

theorem sigma_sigma {K : Type} [Field K] [Finite K] (σ : K ≃+* K) {q : ℕ}
    (hσ : ∀ c, σ c = c ^ q) (hK : Nat.card K = q ^ 2) (c : K) : σ (σ c) = c := by
  haveI := Fintype.ofFinite K
  rw [hσ, hσ, ← pow_mul, ← pow_two, ← hK, Nat.card_eq_fintype_card]
  exact FiniteField.pow_card c

section Main

variable {K : Type} [Field K] [Finite K] (σ : K ≃+* K) {q : ℕ}

local notation "LeviJ" => twE6LongRootLevi (twE6RootSubgroup K σ e6HighestRoot)
  (twE6RootSubgroup K σ (-e6HighestRoot))

theorem card_orbitField_eq (hσ : ∀ c, σ c = c ^ q) (hK : Nat.card K = q ^ 2) {p f : ℕ}
    (hp : p.Prime) (hf : 1 ≤ f) (hq : q = p ^ f) (a : Fin TwistTag.E6.foldedTag.rank) :
    Nat.card (orbitField TwistTag.E6 K σ.toRingHom a) = q ^ (TwistTag.E6.orbit a).card := by
  subst hq
  exact CFSG.Timmesfeld.ExceptionalOrders.card_orbitField (t := TwistTag.E6) hp hf hK
    (σ := σ.toRingHom) hσ a

theorem xG_mem_levi (hr : ringChar K ≠ 3) (hσ : ∀ c, σ c = c ^ q) (hK : Nat.card K = q ^ 2)
    {a : Fin TwistTag.E6.foldedTag.rank} (ha : a ≠ 3)
    (c : orbitField TwistTag.E6 K σ.toRingHom a) : xG σ a c ∈ LeviJ := by
  obtain ⟨p, f, hp, hf, hq, hcases⟩ := q_cases hr hK
  have hq2 := two_le_of_card_eq_sq hK
  have h012 : ∀ b : Fin TwistTag.E6.foldedTag.rank, b ≠ 3 → b = 0 ∨ b = 1 ∨ b = 2 := by decide
  rcases h012 a ha with rfl | rfl | rfl
  · obtain ⟨u, hu⟩ := exists_unit_sq_ne_one_of_four_le (F := orbitField TwistTag.E6 K σ.toRingHom 0)
      (by
        rw [card_orbitField_eq σ hσ hK hp hf hq,
          show (TwistTag.E6.orbit (0 : Fin TwistTag.E6.foldedTag.rank)).card = 2 by decide]
        nlinarith)
    exact xG_mem_levi_of_unit σ ha hu c
  · obtain ⟨u, hu⟩ := exists_unit_sq_ne_one_of_four_le (F := orbitField TwistTag.E6 K σ.toRingHom 1)
      (by
        rw [card_orbitField_eq σ hσ hK hp hf hq, card_orbit_one']
        nlinarith)
    exact xG_mem_levi_of_unit σ ha hu c
  · rcases hcases with ⟨hq2', h2⟩ | h4
    ·
      subst hq2'
      have hσσ := sigma_sigma σ hσ hK
      have hfix : σ (c : K) = c := by
        have := mem_orbitField.1 c.2
        rw [show (TwistTag.E6.orbit (2 : Fin TwistTag.E6.foldedTag.rank)).card = 1 from
          card_orbit_two', pow_one] at this
        exact this
      have hc2 : (c : K) ^ 2 = c := by rw [← hσ, hfix]
      have hc01 : (c : K) = 0 ∨ (c : K) = 1 := by
        have : (c : K) * ((c : K) - 1) = 0 := by linear_combination hc2
        rcases mul_eq_zero.1 this with h | h
        · exact Or.inl h
        · exact Or.inr (sub_eq_zero.1 h)
      rcases hc01 with h0 | h1
      · have : c = 0 := Subtype.ext h0
        rw [this, xG_zero]
        exact one_mem _
      · classical
        haveI := Fintype.ofFinite K
        obtain ⟨w, -, hw⟩ := Finset.exists_mem_notMem_of_card_lt_card
          (s := ({0, 1} : Finset K)) (t := Finset.univ)
          (by
            rw [Finset.card_univ, ← Nat.card_eq_fintype_card, hK]
            exact lt_of_le_of_lt Finset.card_le_two (by norm_num))
        simp only [Finset.mem_insert, Finset.mem_singleton, not_or] at hw
        have hw3 : w ^ 3 = 1 := by
          have := FiniteField.pow_card_sub_one_eq_one w hw.1
          rwa [← Nat.card_eq_fintype_card, hK] at this
        have hq' : w ^ 2 + w + 1 = 0 := by
          have : (w - 1) * (w ^ 2 + w + 1) = 0 := by linear_combination hw3
          exact (mul_eq_zero.1 this).resolve_left (sub_ne_zero.2 hw.2)
        have hwσ : w + σ w = 1 := by
          rw [hσ w]
          linear_combination hq' - h2
        have hwmem : w ∈ orbitField TwistTag.E6 K σ.toRingHom 1 := by
          rw [mem_orbitField, card_orbit_one', pow_two]
          exact hσσ w
        exact xG_a2_mem_levi_of_two σ h2 ⟨w, hwmem⟩ c (h1.trans hwσ.symm)
    · obtain ⟨u, hu⟩ := exists_unit_sq_ne_one_of_four_le
        (F := orbitField TwistTag.E6 K σ.toRingHom 2)
        (by
          rw [card_orbitField_eq σ hσ hK hp hf hq, card_orbit_two', pow_one]
          exact h4)
      exact xG_mem_levi_of_unit σ ha hu c

end Main

end LeviAux

section Public

theorem xG_mem_twE6LongRootLevi (K : Type) [Field K] [Finite K] (σ : K ≃+* K) (q : ℕ)
    (hr : ringChar K ≠ 3) (hσ : ∀ c, σ c = c ^ q) (hK : Nat.card K = q ^ 2)
    (a : Fin TwistTag.E6.foldedTag.rank) (ha : a ≠ 3)
    (c : orbitField TwistTag.E6 K σ.toRingHom a) :
    xG σ a c ∈ twE6LongRootLevi (twE6RootSubgroup K σ e6HighestRoot)
      (twE6RootSubgroup K σ (-e6HighestRoot)) :=
  LeviAux.xG_mem_levi σ hr hσ hK ha c

theorem yG_mem_twE6LongRootLevi (K : Type) [Field K] [Finite K] (σ : K ≃+* K) (q : ℕ)
    (hr : ringChar K ≠ 3) (hσ : ∀ c, σ c = c ^ q) (hK : Nat.card K = q ^ 2)
    (a : Fin TwistTag.E6.foldedTag.rank) (ha : a ≠ 3)
    (c : orbitField TwistTag.E6 K σ.toRingHom a) :
    yG σ a c ∈ twE6LongRootLevi (twE6RootSubgroup K σ e6HighestRoot)
      (twE6RootSubgroup K σ (-e6HighestRoot)) :=
  LeviAux.yG_mem_levi_of_x σ ha (fun c => LeviAux.xG_mem_levi σ hr hσ hK ha c) c

theorem nG_mem_twE6LongRootLevi (K : Type) [Field K] [Finite K] (σ : K ≃+* K) (q : ℕ)
    (hr : ringChar K ≠ 3) (hσ : ∀ c, σ c = c ^ q) (hK : Nat.card K = q ^ 2)
    (a : Fin TwistTag.E6.foldedTag.rank) (ha : a ≠ 3) :
    nG σ a ∈ twE6LongRootLevi (twE6RootSubgroup K σ e6HighestRoot)
      (twE6RootSubgroup K σ (-e6HighestRoot)) :=
  LeviAux.nG_mem_levi_of_x σ ha (fun c => LeviAux.xG_mem_levi σ hr hσ hK ha c)

end Public

end CFSG.LieType.SeitzGeneration.ExcWideThree.TwE6LongRoot
