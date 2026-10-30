module

public import CFSG.Fischer.Classification.Recognition.PSU6
public import CFSG.HardMathSupport.Solomon.Coordinator.InndiagProxy
public import CFSG.HardMathSupport.Solomon.Proving.L2OrderUnique
public import CFSG.LocalAnalysis.ComponentClassification.ClassicalModelStatedBridge

public section

namespace CFSG.HardMathSupport.Dickson.Sec6.I923

open CFSG CFSG.Open CFSG.HardMathSupport.Solomon.LocalBalance.Lemma514CoverNs

theorem num_odd : ∀ p ∈ ({3, 5, 7, 11} : Finset ℕ), ∀ k < 8, 1 ≤ k → 10 ≤ p ^ k → p ^ k < 2700 →
    ((p ^ k) ^ 3 - p ^ k) / 2 ∣ 9196830720 → 11 ∣ ((p ^ k) ^ 3 - p ^ k) / 2 := by
  decide +kernel

theorem num_even : ∀ m < 12, 4 ≤ m → (2 ^ m) ^ 3 - 2 ^ m ∣ 9196830720 →
    11 ∣ (2 ^ m) ^ 3 - 2 ^ m := by
  decide +kernel

theorem prime_dvd_smooth {p : ℕ} (hp : p.Prime)
    (h : p ∣ 2 ^ 16 * 3 ^ 6 * 5 * 7 * 11) : p = 2 ∨ p = 3 ∨ p = 5 ∨ p = 7 ∨ p = 11 := by
  have key : ∀ q k : ℕ, q.Prime → p ∣ q ^ k → p = q := fun q k hq h =>
    (Nat.prime_dvd_prime_iff_eq hp hq).1 (hp.dvd_of_dvd_pow h)
  rcases (Nat.Prime.dvd_mul hp).1 h with h | h
  · rcases (Nat.Prime.dvd_mul hp).1 h with h | h
    · rcases (Nat.Prime.dvd_mul hp).1 h with h | h
      · rcases (Nat.Prime.dvd_mul hp).1 h with h | h
        · exact Or.inl (key 2 16 Nat.prime_two h)
        · exact Or.inr (Or.inl (key 3 6 Nat.prime_three h))
      · exact Or.inr (Or.inr (Or.inl (key 5 1 Nat.prime_five (by simpa using h))))
    · exact Or.inr (Or.inr (Or.inr (Or.inl (key 7 1 (by norm_num) (by simpa using h)))))
  · exact Or.inr (Or.inr (Or.inr (Or.inr (key 11 1 (by norm_num) (by simpa using h)))))

theorem eleven_dvd_of_typeL2 {Y : Type} [Group Y] {r : ℕ} (hr : 10 ≤ r) (hT : IsTypeL2 r Y)
    (hdvd : Nat.card (Y ⧸ Subgroup.center Y) ∣ 9196830720) :
    11 ∣ Nat.card (Y ⧸ Subgroup.center Y) := by
  obtain ⟨-, hodd, heven⟩ := CFSG.HardMathSupport.Solomon.Proving.typeL2_card Y hT
  have hle : Nat.card (Y ⧸ Subgroup.center Y) ≤ 9196830720 := Nat.le_of_dvd (by norm_num) hdvd
  generalize Nat.card (Y ⧸ Subgroup.center Y) = M₀ at hodd heven hdvd hle ⊢
  rcases Nat.even_or_odd r with hev | hod
  · obtain ⟨h1, m, hm1, rfl⟩ := heven hev
    have hm : m < 12 := by
      by_contra hm
      push Not at hm
      have h2 : 2 ^ 12 ≤ 2 ^ m := Nat.pow_le_pow_right (by norm_num) hm
      have h3 : (2 ^ m) ^ 3 = 2 ^ m * 2 ^ m * 2 ^ m := by ring
      nlinarith
    have hm4 : 4 ≤ m := by
      by_contra hm
      push Not at hm
      have h2 : 2 ^ m ≤ 2 ^ 3 := Nat.pow_le_pow_right (by norm_num) (by omega)
      omega
    have hM : M₀ = (2 ^ m) ^ 3 - 2 ^ m := by omega
    rw [hM] at hdvd ⊢
    exact num_even m hm hm4 hdvd
  · have h1 := hodd hod
    obtain ⟨F, hF, hFin, hcard, -⟩ := hT
    haveI : Fintype F := Fintype.ofFinite F
    obtain ⟨p, -, n, hp, hpn⟩ := FiniteField.card' F
    have hrp : r = p ^ (n : ℕ) := by
      rw [← hcard, Nat.card_eq_fintype_card, hpn]
    have hr2700 : r < 2700 := by
      by_contra hcon
      push Not at hcon
      have h2 : r * r ≥ 2700 * 2700 := Nat.mul_le_mul hcon hcon
      have h3 : r ^ 3 = r * (r * r) := by ring
      nlinarith
    have hp2N : p ∣ 2 ^ 16 * 3 ^ 6 * 5 * 7 * 11 := by
      have h2M : r ∣ 2 * M₀ := by
        have : 2 * M₀ = r * (r ^ 2 - 1) := by
          have hr3 : r ^ 3 = r * r ^ 2 := by ring
          have hr1 : 1 ≤ r ^ 2 := Nat.one_le_pow _ _ (by omega)
          rw [Nat.mul_sub, mul_one]
          omega
        rw [this]
        exact dvd_mul_right _ _
      have : r ∣ 2 ^ 16 * 3 ^ 6 * 5 * 7 * 11 := by
        refine h2M.trans ?_
        have : (2 ^ 16 * 3 ^ 6 * 5 * 7 * 11 : ℕ) = 2 * 9196830720 := by norm_num
        rw [this]
        exact mul_dvd_mul_left 2 hdvd
      exact (hrp ▸ dvd_pow_self p n.ne_zero).trans this
    have hpne2 : p ≠ 2 := by
      rintro rfl
      have : 2 ∣ r := hrp ▸ dvd_pow_self 2 n.ne_zero
      exact (Nat.not_even_iff_odd.2 hod) (even_iff_two_dvd.2 this)
    have hpmem : p ∈ ({3, 5, 7, 11} : Finset ℕ) := by
      rcases prime_dvd_smooth hp hp2N with h | h | h | h | h
      · exact absurd h hpne2
      · simp [h]
      · simp [h]
      · simp [h]
      · simp [h]
    have hM : M₀ = ((p ^ (n : ℕ)) ^ 3 - p ^ (n : ℕ)) / 2 := by
      subst hrp
      omega
    rw [hM] at hdvd ⊢
    refine num_odd p hpmem n ?_ n.pos ?_ ?_ hdvd
    · by_contra hcon
      push Not at hcon
      have : 3 ^ 8 ≤ p ^ (n : ℕ) := by
        calc 3 ^ 8 ≤ 3 ^ (n : ℕ) := Nat.pow_le_pow_right (by norm_num) hcon
          _ ≤ p ^ (n : ℕ) := Nat.pow_le_pow_left (by
              rcases Finset.mem_insert.1 hpmem with h | h
              · omega
              · simp at h; omega) _
      omega
    · exact hrp ▸ hr
    · exact hrp ▸ hr2700

end CFSG.HardMathSupport.Dickson.Sec6.I923
