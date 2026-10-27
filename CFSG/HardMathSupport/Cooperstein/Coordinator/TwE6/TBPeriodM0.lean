module

public import CFSG.HardMathSupport.Cooperstein.Coordinator.TwE6.TBInterfaces
public import CFSG.HardMathSupport.Cooperstein.Coordinator.F4Exc.Arith

set_option linter.unusedSectionVars false

public noncomputable section

namespace CFSG.HardMathSupport.Cooperstein.Coordinator.TwE6

theorem twM0_den_pos {f g : ℕ} (hf : 1 ≤ f) : 0 < 2 ^ Nat.gcd f g - 1 := by
  have hd : 1 ≤ Nat.gcd f g := Nat.gcd_pos_of_pos_left g (by omega)
  have : 2 ≤ 2 ^ Nat.gcd f g := by
    calc 2 = 2 ^ 1 := by norm_num
      _ ≤ 2 ^ Nat.gcd f g := Nat.pow_le_pow_right (by norm_num) hd
  omega

theorem twM0_eq {f g gh : ℕ} (hf : 1 ≤ f) (hgh : 2 ^ f - 1 = (2 ^ Nat.gcd f g - 1) * gh) :
    twM0 f g = gh := by
  unfold twM0
  rw [hgh, Nat.mul_div_cancel_left gh (twM0_den_pos hf)]

theorem twM0_mul {f : ℕ} (hf : 1 ≤ f) (g : ℕ) :
    (2 ^ Nat.gcd f g - 1) * twM0 f g = 2 ^ f - 1 := by
  have hd : 1 ≤ Nat.gcd f g := Nat.gcd_pos_of_pos_left g (by omega)
  obtain ⟨gh, hgh⟩ := F4Exc.exists_gh hd (Nat.gcd_dvd_left f g)
  rw [twM0_eq hf hgh, hgh]

theorem twM0_arith {f g : ℕ} (hf : 1 ≤ f) (hg : 1 ≤ g) (hgf : g ∣ 2 * f) (ht : 3 ≤ 2 * f / g) :
    3 ≤ twM0 f g ∧ Odd (twM0 f g) ∧ twM0 f g ∣ 2 ^ f - 1 ∧
      ∀ j : ℕ, 0 < j → j < f → ¬ twM0 f g ∣ 2 ^ j - 1 := by
  have hd : 1 ≤ Nat.gcd f g := Nat.gcd_pos_of_pos_left g (by omega)
  have hdf : Nat.gcd f g ∣ f := Nat.gcd_dvd_left f g
  have hdg : Nat.gcd f g ≤ g := Nat.le_of_dvd (by omega) (Nat.gcd_dvd_right f g)
  have h3g : 3 * g ≤ 2 * f := (Nat.le_div_iff_mul_le (by omega : 0 < g)).1 ht
  have hgf' : g < f := by omega
  have hdlt : Nat.gcd f g < f := by omega
  obtain ⟨r, hr⟩ := hdf
  have hfr : f = r * Nat.gcd f g := by rw [Nat.mul_comm]; exact hr
  have hdiv : f / Nat.gcd f g = r := Nat.div_eq_of_eq_mul_left (by omega) hfr
  have hr2 : 2 ≤ r := by
    rcases Nat.lt_or_ge r 2 with h | h
    · interval_cases r
      · omega
      · omega
    · exact h
  have ht2 : 2 ≤ f / Nat.gcd f g := by rw [hdiv]; exact hr2
  obtain ⟨gh, hgh⟩ := F4Exc.exists_gh hd (Nat.gcd_dvd_left f g)
  have hm : twM0 f g = gh := twM0_eq hf hgh
  rw [hm]
  refine ⟨F4Exc.three_le_gh hf hd (Nat.gcd_dvd_left f g) ht2 hgh,
    F4Exc.gh_odd hf hgh, Dvd.intro_left _ hgh.symm,
    fun j hj0 hjn => F4Exc.not_dvd_pow_sub_one hd (Nat.gcd_dvd_left f g) ht2 hgh hj0 hjn⟩

end CFSG.HardMathSupport.Cooperstein.Coordinator.TwE6
