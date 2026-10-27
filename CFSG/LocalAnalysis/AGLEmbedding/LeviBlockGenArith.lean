module

public import CFSG.Open.Defs
import CFSG.ClassicalInvolution.RouteD.TWRExoticArith

public section

namespace CFSG.AGLEmbedding

open CFSG.Open

namespace LeviBlock

open CFSG.ClassicalInvolution.RouteD.TWR (padicValNat_ordA padicValNat_ordTwistedA
  padicValNat_ordBC padicValNat_ordD padicValNat_ordTwistedD)

theorem eq_of_padicValNat_two {x k e m : ℕ} (hk : padicValNat 2 x = k) (hx : x = 2 ^ e * m)
    (hm : m % 2 = 1) : k = e := by
  subst hx
  rw [← hk, padicValNat.mul (by positivity) (by omega), padicValNat.prime_pow,
    padicValNat.eq_zero_of_not_dvd (by omega), add_zero]

theorem two_le_two_pow_mul {e m : ℕ} (hm : m % 2 = 1) (he : 1 ≤ e) : 2 ≤ 2 ^ e * m :=
  calc 2 = 2 ^ 1 := rfl
    _ ≤ 2 ^ e := Nat.pow_le_pow_right (by norm_num) he
    _ ≤ 2 ^ e * m := Nat.le_mul_of_pos_right _ (by omega)

theorem le_triangle (n : ℕ) : n ≤ n * (n + 1) / 2 := by
  rcases Nat.eq_zero_or_pos n with rfl | hn
  · simp
  exact (Nat.le_div_iff_mul_le (by norm_num)).mpr (Nat.mul_le_mul le_rfl (by omega))

theorem ordA_zero (q : ℕ) : ordA 0 q = 1 := by simp [ordA]

theorem ordA_one {n : ℕ} (hn : 1 ≤ n) : ordA n 1 = 0 := by
  unfold ordA
  rw [Finset.prod_eq_zero (i := 2) (Finset.mem_Icc.mpr ⟨le_rfl, by omega⟩) (by simp)]
  simp

theorem ordTwistedA_zero (q : ℕ) : ordTwistedA 0 q = 1 := by simp [ordTwistedA]

theorem ordTwistedA_one {n : ℕ} (hn : 1 ≤ n) : ordTwistedA n 1 = 0 := by
  unfold ordTwistedA
  rw [Finset.prod_eq_zero (i := 2) (Finset.mem_Icc.mpr ⟨le_rfl, by omega⟩) (by norm_num)]
  simp

theorem ordBC_zero_le (q : ℕ) : ordBC 0 q ≤ 1 := by
  unfold ordBC
  simpa using Nat.div_le_self 1 _

theorem ordBC_one {n : ℕ} (hn : 1 ≤ n) : ordBC n 1 = 0 := by
  unfold ordBC
  rw [Finset.prod_eq_zero (i := 1) (Finset.mem_Icc.mpr ⟨le_rfl, hn⟩) (by simp)]
  simp

theorem ordD_zero (q : ℕ) : ordD 0 q = 0 := by simp [ordD]

theorem ordD_one (n : ℕ) : ordD n 1 = 0 := by simp [ordD]

theorem ordTwistedD_zero (q : ℕ) : ordTwistedD 0 q = 1 := by simp [ordTwistedD]

theorem ordTwistedD_one_le (n : ℕ) : ordTwistedD n 1 ≤ 1 := by
  unfold ordTwistedD
  rcases Nat.lt_or_ge n 2 with hn | hn
  · interval_cases n <;> simp
  · rw [Finset.prod_eq_zero (i := 1) (Finset.mem_Icc.mpr ⟨le_rfl, by omega⟩) (by simp)]
    simp

theorem ordA_two_part {n q f e m : ℕ} (hq : q = 2 ^ f) (hm : m % 2 = 1) (he : 1 ≤ e)
    (h : ordA n q = 2 ^ e * m) :
    1 ≤ n ∧ n ≤ e ∧ 1 ≤ f ∧ f ≤ e ∧ f * (n * (n + 1) / 2) = e := by
  have h2 := two_le_two_pow_mul hm he
  rcases Nat.eq_zero_or_pos n with rfl | hn
  · rw [ordA_zero] at h; omega
  rcases Nat.eq_zero_or_pos f with rfl | hf
  · rw [hq, pow_zero, ordA_one hn] at h; omega
  have hv := eq_of_padicValNat_two (padicValNat_ordA hq hf hn) h hm
  have hN := le_triangle n
  exact ⟨hn, hN.trans (Nat.le_mul_of_pos_left _ hf) |>.trans hv.le, hf,
    (Nat.le_mul_of_pos_right _ (by omega)).trans hv.le, hv⟩

theorem ordTwistedA_two_part {n q f e m : ℕ} (hq : q = 2 ^ f) (hm : m % 2 = 1) (he : 1 ≤ e)
    (h : ordTwistedA n q = 2 ^ e * m) :
    1 ≤ n ∧ n ≤ e ∧ 1 ≤ f ∧ f ≤ e ∧ f * (n * (n + 1) / 2) = e := by
  have h2 := two_le_two_pow_mul hm he
  rcases Nat.eq_zero_or_pos n with rfl | hn
  · rw [ordTwistedA_zero] at h; omega
  rcases Nat.eq_zero_or_pos f with rfl | hf
  · rw [hq, pow_zero, ordTwistedA_one hn] at h; omega
  have hv := eq_of_padicValNat_two (padicValNat_ordTwistedA hq hf hn) h hm
  have hN := le_triangle n
  exact ⟨hn, hN.trans (Nat.le_mul_of_pos_left _ hf) |>.trans hv.le, hf,
    (Nat.le_mul_of_pos_right _ (by omega)).trans hv.le, hv⟩

theorem ordBC_two_part {n q f e m : ℕ} (hq : q = 2 ^ f) (hm : m % 2 = 1) (he : 1 ≤ e)
    (h : ordBC n q = 2 ^ e * m) : 1 ≤ n ∧ n ≤ e ∧ 1 ≤ f ∧ f ≤ e ∧ f * (n * n) = e := by
  have h2 := two_le_two_pow_mul hm he
  rcases Nat.eq_zero_or_pos n with rfl | hn
  · have := ordBC_zero_le q; omega
  rcases Nat.eq_zero_or_pos f with rfl | hf
  · rw [hq, pow_zero, ordBC_one hn] at h; omega
  have hv := eq_of_padicValNat_two (padicValNat_ordBC hq hf hn) h hm
  have hN : n ≤ n * n := Nat.le_mul_of_pos_left _ hn
  exact ⟨hn, hN.trans (Nat.le_mul_of_pos_left _ hf) |>.trans hv.le, hf,
    (Nat.le_mul_of_pos_right _ (by omega)).trans hv.le, hv⟩

theorem ordD_two_part {n q f e m : ℕ} (hq : q = 2 ^ f) (hm : m % 2 = 1) (he : 1 ≤ e)
    (h : ordD n q = 2 ^ e * m) : 2 ≤ n ∧ n ≤ e ∧ 1 ≤ f ∧ f ≤ e ∧ f * (n * (n - 1)) = e := by
  have h2 := two_le_two_pow_mul hm he
  rcases Nat.eq_zero_or_pos n with rfl | hn
  · rw [ordD_zero] at h; omega
  rcases Nat.eq_zero_or_pos f with rfl | hf
  · rw [hq, pow_zero, ordD_one] at h; omega
  have hv := eq_of_padicValNat_two (padicValNat_ordD hq hf hn) h hm
  have hn2 : 2 ≤ n := by
    by_contra hlt
    obtain rfl : n = 1 := by omega
    simp at hv
    omega
  have hN : n ≤ n * (n - 1) := Nat.le_mul_of_pos_right _ (by omega)
  exact ⟨hn2, hN.trans (Nat.le_mul_of_pos_left _ hf) |>.trans hv.le, hf,
    (Nat.le_mul_of_pos_right _ (by omega)).trans hv.le, hv⟩

theorem ordTwistedD_two_part {n q f e m : ℕ} (hq : q = 2 ^ f) (hm : m % 2 = 1) (he : 1 ≤ e)
    (h : ordTwistedD n q = 2 ^ e * m) :
    2 ≤ n ∧ n ≤ e ∧ 1 ≤ f ∧ f ≤ e ∧ f * (n * (n - 1)) = e := by
  have h2 := two_le_two_pow_mul hm he
  rcases Nat.eq_zero_or_pos n with rfl | hn
  · rw [ordTwistedD_zero] at h; omega
  rcases Nat.eq_zero_or_pos f with rfl | hf
  · have := ordTwistedD_one_le n
    rw [hq, pow_zero] at h
    omega
  have hv := eq_of_padicValNat_two (padicValNat_ordTwistedD hq hf hn) h hm
  have hn2 : 2 ≤ n := by
    by_contra hlt
    obtain rfl : n = 1 := by omega
    simp at hv
    omega
  have hN : n ≤ n * (n - 1) := Nat.le_mul_of_pos_right _ (by omega)
  exact ⟨hn2, hN.trans (Nat.le_mul_of_pos_left _ hf) |>.trans hv.le, hf,
    (Nat.le_mul_of_pos_right _ (by omega)).trans hv.le, hv⟩

end LeviBlock

theorem ordA_ne_u38 {n q f : ℕ} (hq : q = 2 ^ f) : ordA n q ≠ 5515776 := by
  intro h
  obtain ⟨h1, h2, h3, h4, h5⟩ := LeviBlock.ordA_two_part hq (e := 9) (m := 10773) (by norm_num)
    (by norm_num) (h.trans (by norm_num))
  subst hq
  interval_cases n <;> interval_cases f <;> first | omega | (revert h; unfold ordA; decide)

theorem ordTwistedA_eq_u38_iff {n q f : ℕ} (hq : q = 2 ^ f) :
    ordTwistedA n q = 5515776 ↔ n = 2 ∧ q = 8 := by
  refine ⟨fun h => ?_, fun ⟨hn, hq8⟩ => by subst hn hq8; unfold ordTwistedA; decide⟩
  obtain ⟨h1, h2, h3, h4, h5⟩ := LeviBlock.ordTwistedA_two_part hq (e := 9) (m := 10773)
    (by norm_num) (by norm_num) (h.trans (by norm_num))
  subst hq
  interval_cases n <;> interval_cases f <;> first | omega | (revert h; unfold ordTwistedA; decide)

theorem ordBC_ne_u38 {n q f : ℕ} (hq : q = 2 ^ f) : ordBC n q ≠ 5515776 := by
  intro h
  obtain ⟨h1, h2, h3, h4, h5⟩ := LeviBlock.ordBC_two_part hq (e := 9) (m := 10773) (by norm_num)
    (by norm_num) (h.trans (by norm_num))
  subst hq
  interval_cases n <;> interval_cases f <;> first | omega | (revert h; unfold ordBC; decide)

theorem ordD_ne_u38 {n q f : ℕ} (hq : q = 2 ^ f) : ordD n q ≠ 5515776 := by
  intro h
  obtain ⟨h1, h2, h3, h4, h5⟩ := LeviBlock.ordD_two_part hq (e := 9) (m := 10773) (by norm_num)
    (by norm_num) (h.trans (by norm_num))
  interval_cases n <;> omega

theorem ordTwistedD_ne_u38 {n q f : ℕ} (hq : q = 2 ^ f) : ordTwistedD n q ≠ 5515776 := by
  intro h
  obtain ⟨h1, h2, h3, h4, h5⟩ := LeviBlock.ordTwistedD_two_part hq (e := 9) (m := 10773)
    (by norm_num) (by norm_num) (h.trans (by norm_num))
  interval_cases n <;> omega

theorem ordA_ne_u42 {n q f : ℕ} (hq : q = 2 ^ f) : ordA n q ≠ 25920 := by
  intro h
  obtain ⟨h1, h2, h3, h4, h5⟩ := LeviBlock.ordA_two_part hq (e := 6) (m := 405) (by norm_num)
    (by norm_num) (h.trans (by norm_num))
  subst hq
  interval_cases n <;> interval_cases f <;> first | omega | (revert h; unfold ordA; decide)

theorem ordTwistedA_eq_u42_iff {n q f : ℕ} (hq : q = 2 ^ f) :
    ordTwistedA n q = 25920 ↔ n = 3 ∧ q = 2 := by
  refine ⟨fun h => ?_, fun ⟨hn, hq2⟩ => by subst hn hq2; unfold ordTwistedA; decide⟩
  obtain ⟨h1, h2, h3, h4, h5⟩ := LeviBlock.ordTwistedA_two_part hq (e := 6) (m := 405)
    (by norm_num) (by norm_num) (h.trans (by norm_num))
  subst hq
  interval_cases n <;> interval_cases f <;> first | omega | (revert h; unfold ordTwistedA; decide)

theorem ordBC_ne_u42 {n q f : ℕ} (hq : q = 2 ^ f) : ordBC n q ≠ 25920 := by
  intro h
  obtain ⟨h1, h2, h3, h4, h5⟩ := LeviBlock.ordBC_two_part hq (e := 6) (m := 405) (by norm_num)
    (by norm_num) (h.trans (by norm_num))
  subst hq
  interval_cases n <;> interval_cases f <;> first | omega | (revert h; unfold ordBC; decide)

theorem ordD_ne_u42 {n q f : ℕ} (hq : q = 2 ^ f) : ordD n q ≠ 25920 := by
  intro h
  obtain ⟨h1, h2, h3, h4, h5⟩ := LeviBlock.ordD_two_part hq (e := 6) (m := 405) (by norm_num)
    (by norm_num) (h.trans (by norm_num))
  subst hq
  interval_cases n <;> interval_cases f <;> first | omega | (revert h; unfold ordD; decide)

theorem ordTwistedD_eq_u42_iff {n q f : ℕ} (hq : q = 2 ^ f) :
    ordTwistedD n q = 25920 ↔ n = 3 ∧ q = 2 := by
  refine ⟨fun h => ?_, fun ⟨hn, hq2⟩ => by subst hn hq2; unfold ordTwistedD; decide⟩
  obtain ⟨h1, h2, h3, h4, h5⟩ := LeviBlock.ordTwistedD_two_part hq (e := 6) (m := 405)
    (by norm_num) (by norm_num) (h.trans (by norm_num))
  subst hq
  interval_cases n <;> interval_cases f <;> first | omega | (revert h; unfold ordTwistedD; decide)

theorem ordA_eq_sixty_iff {n q f : ℕ} (hq : q = 2 ^ f) : ordA n q = 60 ↔ n = 1 ∧ q = 4 := by
  refine ⟨fun h => ?_, fun ⟨hn, hq4⟩ => by subst hn hq4; unfold ordA; decide⟩
  obtain ⟨h1, h2, h3, h4, h5⟩ := LeviBlock.ordA_two_part hq (e := 2) (m := 15) (by norm_num)
    (by norm_num) (h.trans (by norm_num))
  subst hq
  interval_cases n <;> interval_cases f <;> omega

theorem ordTwistedA_eq_sixty_iff {n q f : ℕ} (hq : q = 2 ^ f) :
    ordTwistedA n q = 60 ↔ n = 1 ∧ q = 4 := by
  refine ⟨fun h => ?_, fun ⟨hn, hq4⟩ => by subst hn hq4; unfold ordTwistedA; decide⟩
  obtain ⟨h1, h2, h3, h4, h5⟩ := LeviBlock.ordTwistedA_two_part hq (e := 2) (m := 15)
    (by norm_num) (by norm_num) (h.trans (by norm_num))
  subst hq
  interval_cases n <;> interval_cases f <;> omega

theorem ordBC_eq_sixty_iff {n q f : ℕ} (hq : q = 2 ^ f) : ordBC n q = 60 ↔ n = 1 ∧ q = 4 := by
  refine ⟨fun h => ?_, fun ⟨hn, hq4⟩ => by subst hn hq4; unfold ordBC; decide⟩
  obtain ⟨h1, h2, h3, h4, h5⟩ := LeviBlock.ordBC_two_part hq (e := 2) (m := 15) (by norm_num)
    (by norm_num) (h.trans (by norm_num))
  subst hq
  interval_cases n <;> interval_cases f <;> omega

theorem ordD_ne_sixty {n q f : ℕ} (hq : q = 2 ^ f) : ordD n q ≠ 60 := by
  intro h
  obtain ⟨h1, h2, h3, h4, h5⟩ := LeviBlock.ordD_two_part hq (e := 2) (m := 15) (by norm_num)
    (by norm_num) (h.trans (by norm_num))
  obtain rfl : n = 2 := by omega
  obtain rfl : f = 1 := by omega
  subst hq
  revert h
  unfold ordD
  decide

theorem ordTwistedD_eq_sixty_iff {n q f : ℕ} (hq : q = 2 ^ f) :
    ordTwistedD n q = 60 ↔ n = 2 ∧ q = 2 := by
  refine ⟨fun h => ?_, fun ⟨hn, hq2⟩ => by subst hn hq2; unfold ordTwistedD; decide⟩
  obtain ⟨h1, h2, h3, h4, h5⟩ := LeviBlock.ordTwistedD_two_part hq (e := 2) (m := 15)
    (by norm_num) (by norm_num) (h.trans (by norm_num))
  obtain rfl : n = 2 := by omega
  obtain rfl : f = 1 := by omega
  exact ⟨rfl, hq⟩

end CFSG.AGLEmbedding
