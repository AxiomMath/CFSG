module

public import CFSG.HardMathSupport.Cooperstein.Coordinator.TwE6.TBInterfaces
public import CFSG.HardMathSupport.Cooperstein.Coordinator.F4Exc.Arith
public import CFSG.HardMathSupport.Cooperstein.Coordinator.CurtisExc.Digits

public section

namespace CFSG.HardMathSupport.Cooperstein.Coordinator.TwE6

theorem twM0_dvd_of_periodic {f g : ℕ} (hf : 1 ≤ f)
    (hm : (2 ^ Nat.gcd f g - 1) * twM0 f g = 2 ^ f - 1) {n a : ℕ} (hn : n = f ∨ n = 2 * f)
    (h : (2 ^ n - 1) ∣ (2 ^ g - 1) * a) : twM0 f g ∣ a := by
  set d := Nat.gcd f g with hd
  have hd0 : 1 ≤ d := Nat.gcd_pos_of_pos_left _ hf
  have hfn : (2 ^ f - 1) ∣ (2 ^ n - 1) := by
    obtain ⟨gh, hgh⟩ := F4Exc.exists_gh hf (show f ∣ n by rcases hn with rfl | rfl <;> simp)
    exact ⟨gh, hgh⟩
  have h1 : (2 ^ f - 1) ∣ (2 ^ g - 1) * a := hfn.trans h
  obtain ⟨m₁, hm₁⟩ := F4Exc.exists_gh hd0 (Nat.gcd_dvd_right f g)
  have hG : 0 < 2 ^ d - 1 := by
    have : 2 ^ 1 ≤ 2 ^ d := Nat.pow_le_pow_right (by norm_num) hd0
    omega
  have hcop : Nat.Coprime (twM0 f g) m₁ := by
    have h2 := Nat.pow_sub_one_gcd_pow_sub_one 2 f g
    rw [← hd, ← hm, hm₁, Nat.gcd_mul_left] at h2
    have h3 : (2 ^ d - 1) * Nat.gcd (twM0 f g) m₁ = (2 ^ d - 1) * 1 := by rw [h2, mul_one]
    exact Nat.eq_of_mul_eq_mul_left hG h3
  rw [← hm, hm₁, mul_assoc] at h1
  exact hcop.dvd_of_dvd_mul_left (Nat.dvd_of_mul_dvd_mul_left hG h1)

theorem exists_digits_of_periodic {f g : ℕ} (hf : 1 ≤ f) (hg : 1 ≤ g) (hgf : g ∣ 2 * f)
    (hm : (2 ^ Nat.gcd f g - 1) * twM0 f g = 2 ^ f - 1) {n : ℕ} {J' : Finset ℕ}
    (hn : n = f ∨ n = 2 * f) (hJ : ∀ b ∈ J', b < n) (hne : J'.Nonempty)
    (h : (2 ^ n - 1) ∣ (2 ^ g - 1) * ∑ b ∈ J', 2 ^ b) :
    ∃ D ⊆ J', (2 * f / g + 1) / 2 ≤ D.card ∧ ∀ b ∈ D, ∀ b' ∈ D, b ≠ b' → b % f ≠ b' % f := by
  classical
  set d := Nat.gcd f g with hd
  have hd0 : 1 ≤ d := Nat.gcd_pos_of_pos_left _ hf
  rcases hn with rfl | rfl
  ·
    refine ⟨J', subset_rfl, ?_, fun b hb b' hb' hbb' => ?_⟩
    · have hdvd := twM0_dvd_of_periodic hf hm (Or.inl rfl) h
      have hper : (2 ^ n - 1) ∣ (2 ^ d - 1) * ∑ b ∈ J', 2 ^ b := by
        rw [← hm]; exact Nat.mul_dvd_mul_left _ hdvd
      have hcard := CurtisExc.card_ge_of_periodic hd0 (Nat.gcd_dvd_left n g) hJ hne hper
      have hdg : d ≤ g := Nat.le_of_dvd hg (Nat.gcd_dvd_right n g)
      have h1 : 2 * n / g ≤ 2 * n / d := Nat.div_le_div_left hdg hd0
      have h2 : 2 * n / d = 2 * (n / d) := Nat.mul_div_assoc 2 (Nat.gcd_dvd_left n g)
      omega
    · rw [Nat.mod_eq_of_lt (hJ b hb), Nat.mod_eq_of_lt (hJ b' hb')]
      exact hbb'
  ·
    refine ⟨J'.filter (fun b => b < f ∨ b - f ∉ J'), Finset.filter_subset _ _, ?_, ?_⟩
    · have hcard := CurtisExc.card_ge_of_periodic hg hgf hJ hne h
      set D := J'.filter (fun b => b < f ∨ b - f ∉ J') with hD
      have hsub : J' ⊆ D ∪ D.image (· + f) := by
        intro b hb
        by_cases hbD : b ∈ D
        · exact Finset.mem_union_left _ hbD
        · refine Finset.mem_union_right _ (Finset.mem_image.2 ⟨b - f, ?_, ?_⟩)
          · have h1 : ¬ (b < f ∨ b - f ∉ J') := fun hc => hbD (Finset.mem_filter.2 ⟨hb, hc⟩)
            push Not at h1
            refine Finset.mem_filter.2 ⟨h1.2, Or.inl ?_⟩
            have := hJ b hb
            omega
          · have h1 : ¬ (b < f ∨ b - f ∉ J') := fun hc => hbD (Finset.mem_filter.2 ⟨hb, hc⟩)
            push Not at h1
            omega
      have h2 : J'.card ≤ 2 * D.card := by
        calc J'.card ≤ (D ∪ D.image (· + f)).card := Finset.card_le_card hsub
          _ ≤ D.card + (D.image (· + f)).card := Finset.card_union_le _ _
          _ ≤ D.card + D.card := Nat.add_le_add_left Finset.card_image_le _
          _ = 2 * D.card := by ring
      omega
    · intro b hb b' hb' hbb' hmod
      obtain ⟨hbJ, hbc⟩ := Finset.mem_filter.1 hb
      obtain ⟨hbJ', hbc'⟩ := Finset.mem_filter.1 hb'
      have hb2 := hJ b hbJ
      have hb2' := hJ b' hbJ'
      have key : ∀ x, x < 2 * f → x % f = if x < f then x else x - f := by
        intro x hx
        split_ifs with hxf
        · exact Nat.mod_eq_of_lt hxf
        · rw [Nat.mod_eq_sub_mod (by omega), Nat.mod_eq_of_lt (by omega)]
      rw [key b hb2, key b' hb2'] at hmod
      split_ifs at hmod with h1 h2 h2
      · exact hbb' hmod
      ·
        rcases hbc' with h3 | h3
        · exact h2 h3
        · exact h3 (hmod ▸ hbJ)
      · rcases hbc with h3 | h3
        · exact h1 h3
        · exact h3 (hmod.symm ▸ hbJ')
      · exact hbb' (by omega)

end CFSG.HardMathSupport.Cooperstein.Coordinator.TwE6
