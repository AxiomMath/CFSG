module

public import CFSG.LocalAnalysis.GLTheoremB.Prop95IvFactAltChevBound
public import CFSG.LocalAnalysis.EvenSmallLie.CatalogOrdersLie

public section

namespace CFSG.LocalAnalysis.GLTheoremB.Prop95IvFact

open CFSG.Open CFSG.EvenSmallLie.CatalogOrders CFSG.LocalAnalysis.GLTheoremB.Prop95Parts

@[expose] def Char2Order (m : ℕ) : Prop :=
  (∃ r f : ℕ, 1 ≤ r ∧ 1 ≤ f ∧ m = ordA r (2 ^ f)) ∨
  (∃ r f : ℕ, 2 ≤ r ∧ 1 ≤ f ∧ m = ordTwistedA r (2 ^ f)) ∨
  (∃ r f : ℕ, 2 ≤ r ∧ 1 ≤ f ∧ m = ordBC r (2 ^ f)) ∨
  (∃ r f : ℕ, 4 ≤ r ∧ 1 ≤ f ∧ m = ordD r (2 ^ f)) ∨
  (∃ r f : ℕ, 4 ≤ r ∧ 1 ≤ f ∧ m = ordTwistedD r (2 ^ f)) ∨
  (∃ f : ℕ, 1 ≤ f ∧ m = ordE6 (2 ^ f)) ∨
  (∃ f : ℕ, 1 ≤ f ∧ m = ordE7 (2 ^ f)) ∨
  (∃ f : ℕ, 1 ≤ f ∧ m = ordE8 (2 ^ f)) ∨
  (∃ f : ℕ, 1 ≤ f ∧ m = ordF4 (2 ^ f)) ∨
  (∃ f : ℕ, 1 ≤ f ∧ m = ordG2 (2 ^ f)) ∨
  (∃ f : ℕ, 1 ≤ f ∧ m = ordTwistedE6 (2 ^ f)) ∨
  (∃ f : ℕ, 1 ≤ f ∧ m = ordTrialityD4 (2 ^ f)) ∨
  (∃ a : ℕ, 1 ≤ a ∧ m = ordSuzuki (2 ^ (2 * a + 1))) ∨
  (∃ a : ℕ, 1 ≤ a ∧ m = ordTwistedF4 (2 ^ (2 * a + 1))) ∨
  m = ordTits

theorem two_le_two_pow {f : ℕ} (hf : 1 ≤ f) : 2 ≤ 2 ^ f := by
  calc 2 = 2 ^ 1 := by norm_num
    _ ≤ 2 ^ f := Nat.pow_le_pow_right (by norm_num) hf

theorem one_le_two_pow' (f : ℕ) : 1 ≤ 2 ^ f := Nat.one_le_two_pow

theorem fam_A {r f : ℕ} (hr : 1 ≤ r) (hf : 1 ≤ f) :
    2 ^ (f * (r * (r + 1) / 2)) ∣ ordA r (2 ^ f) ∧
      ordA r (2 ^ f) ≤ 2 ^ (3 * (f * (r * (r + 1) / 2))) := by
  refine ⟨?_, ?_⟩
  · have hd := pow_dvd_ordA (n := r + 1) (by omega) (2 ^ f)
    simp only [Nat.add_sub_cancel] at hd
    rw [pow_mul]
    exact hd
  · calc ordA r (2 ^ f) ≤ (2 ^ f) ^ (3 * (r * (r + 1) / 2)) :=
          ordA_le hr (one_le_two_pow' f)
      _ = 2 ^ (3 * (f * (r * (r + 1) / 2))) := two_pow_pow f 3 _

theorem fam_twistedA {r f : ℕ} (hr : 2 ≤ r) (hf : 1 ≤ f) :
    2 ^ (f * (r * (r + 1) / 2)) ∣ ordTwistedA r (2 ^ f) ∧
      ordTwistedA r (2 ^ f) ≤ 2 ^ (3 * (f * (r * (r + 1) / 2))) := by
  have h2f := two_le_two_pow hf
  refine ⟨?_, ?_⟩
  · have hd := pow_dvd_ordTwistedA (n := r + 1) (by omega) (2 ^ f)
    simp only [Nat.add_sub_cancel] at hd
    rw [pow_mul]
    exact hd
  · have hb : ordTwistedA r (2 ^ f) ≤ (2 ^ f) ^ (3 * (r * (r + 1) / 2)) := by
      rcases (show r = 2 ∨ 3 ≤ r by omega) with rfl | h3
      · exact ordTwistedA_two h2f
      · exact ordTwistedA_le_three h3 h2f
    calc _ ≤ _ := hb
      _ = 2 ^ (3 * (f * (r * (r + 1) / 2))) := two_pow_pow f 3 _

theorem fam_BC {r f : ℕ} (hr : 1 ≤ r) (hf : 1 ≤ f) :
    2 ^ (f * (r * r)) ∣ ordBC r (2 ^ f) ∧
      ordBC r (2 ^ f) ≤ 2 ^ (3 * (f * (r * r))) := by
  refine ⟨?_, ?_⟩
  · have hd := pow_dvd_ordBC hr (2 ^ f)
    rw [pow_mul]
    exact hd
  · calc ordBC r (2 ^ f) ≤ (2 ^ f) ^ (3 * (r * r)) := ordBC_le hr (one_le_two_pow' f)
      _ = 2 ^ (3 * (f * (r * r))) := two_pow_pow f 3 _

theorem fam_D {r f : ℕ} (hr : 4 ≤ r) (hf : 1 ≤ f) :
    2 ^ (f * (r * (r - 1))) ∣ ordD r (2 ^ f) ∧
      ordD r (2 ^ f) ≤ 2 ^ (3 * (f * (r * (r - 1)))) := by
  refine ⟨?_, ?_⟩
  · have hd := pow_dvd_ordD r (2 ^ f)
    rw [pow_mul]
    exact hd
  · calc ordD r (2 ^ f) ≤ (2 ^ f) ^ (3 * (r * (r - 1))) := ordD_le hr (one_le_two_pow' f)
      _ = 2 ^ (3 * (f * (r * (r - 1)))) := two_pow_pow f 3 _

theorem fam_twistedD {r f : ℕ} (hr : 4 ≤ r) (hf : 1 ≤ f) :
    2 ^ (f * (r * (r - 1))) ∣ ordTwistedD r (2 ^ f) ∧
      ordTwistedD r (2 ^ f) ≤ 2 ^ (3 * (f * (r * (r - 1)))) := by
  refine ⟨?_, ?_⟩
  · have hd := pow_dvd_ordTwistedD r (2 ^ f)
    rw [pow_mul]
    exact hd
  · calc ordTwistedD r (2 ^ f) ≤ (2 ^ f) ^ (3 * (r * (r - 1))) :=
          ordTwistedD_le hr (two_le_two_pow hf)
      _ = 2 ^ (3 * (f * (r * (r - 1)))) := two_pow_pow f 3 _

theorem fam_E6 {f : ℕ} (hf : 1 ≤ f) :
    2 ^ (f * 36) ∣ ordE6 (2 ^ f) ∧ ordE6 (2 ^ f) ≤ 2 ^ (3 * (f * 36)) := by
  refine ⟨?_, ?_⟩
  · rw [pow_mul]
    exact pow_dvd_ordE6 (2 ^ f)
  · calc ordE6 (2 ^ f) ≤ (2 ^ f) ^ (3 * 36) := ordE6_le (one_le_two_pow' f)
      _ = 2 ^ (3 * (f * 36)) := two_pow_pow f 3 36

theorem fam_E7 {f : ℕ} (hf : 1 ≤ f) :
    2 ^ (f * 63) ∣ ordE7 (2 ^ f) ∧ ordE7 (2 ^ f) ≤ 2 ^ (3 * (f * 63)) := by
  refine ⟨?_, ?_⟩
  · rw [pow_mul]
    exact pow_dvd_ordE7 (2 ^ f)
  · calc ordE7 (2 ^ f) ≤ (2 ^ f) ^ (3 * 63) := ordE7_le (one_le_two_pow' f)
      _ = 2 ^ (3 * (f * 63)) := two_pow_pow f 3 63

theorem fam_E8 {f : ℕ} (hf : 1 ≤ f) :
    2 ^ (f * 120) ∣ ordE8 (2 ^ f) ∧ ordE8 (2 ^ f) ≤ 2 ^ (3 * (f * 120)) := by
  refine ⟨?_, ?_⟩
  · rw [pow_mul]
    exact pow_lieExp_dvd (t := .E8) (n := 0) (by decide) (2 ^ f)
  · calc ordE8 (2 ^ f) ≤ (2 ^ f) ^ (3 * 120) := ordE8_le (one_le_two_pow' f)
      _ = 2 ^ (3 * (f * 120)) := two_pow_pow f 3 120

theorem fam_F4 {f : ℕ} (hf : 1 ≤ f) :
    2 ^ (f * 24) ∣ ordF4 (2 ^ f) ∧ ordF4 (2 ^ f) ≤ 2 ^ (3 * (f * 24)) := by
  refine ⟨?_, ?_⟩
  · rw [pow_mul]
    exact pow_lieExp_dvd (t := .F4) (n := 0) (by decide) (2 ^ f)
  · calc ordF4 (2 ^ f) ≤ (2 ^ f) ^ (3 * 24) := ordF4_le (one_le_two_pow' f)
      _ = 2 ^ (3 * (f * 24)) := two_pow_pow f 3 24

theorem fam_G2 {f : ℕ} (hf : 1 ≤ f) :
    2 ^ (f * 6) ∣ ordG2 (2 ^ f) ∧ ordG2 (2 ^ f) ≤ 2 ^ (3 * (f * 6)) := by
  refine ⟨?_, ?_⟩
  · rw [pow_mul]
    exact pow_lieExp_dvd (t := .G2) (n := 0) (by decide) (2 ^ f)
  · calc ordG2 (2 ^ f) ≤ (2 ^ f) ^ (3 * 6) := ordG2_le (one_le_two_pow' f)
      _ = 2 ^ (3 * (f * 6)) := two_pow_pow f 3 6

theorem fam_twistedE6 {f : ℕ} (hf : 1 ≤ f) :
    2 ^ (f * 36) ∣ ordTwistedE6 (2 ^ f) ∧ ordTwistedE6 (2 ^ f) ≤ 2 ^ (3 * (f * 36)) := by
  refine ⟨?_, ?_⟩
  · rw [pow_mul]
    exact pow_dvd_ordTwistedE6 (2 ^ f)
  · calc ordTwistedE6 (2 ^ f) ≤ (2 ^ f) ^ (3 * 36) := ordTwistedE6_le (two_le_two_pow hf)
      _ = 2 ^ (3 * (f * 36)) := two_pow_pow f 3 36

theorem fam_trialityD4 {f : ℕ} (hf : 1 ≤ f) :
    2 ^ (f * 12) ∣ ordTrialityD4 (2 ^ f) ∧ ordTrialityD4 (2 ^ f) ≤ 2 ^ (3 * (f * 12)) := by
  refine ⟨?_, ?_⟩
  · rw [pow_mul]
    exact pow_lieExp_dvd (t := .trialityD4) (n := 0) (by decide) (2 ^ f)
  · calc ordTrialityD4 (2 ^ f) ≤ (2 ^ f) ^ (3 * 12) :=
          ordTrialityD4_le (two_le_two_pow hf)
      _ = 2 ^ (3 * (f * 12)) := two_pow_pow f 3 12

theorem fam_suzuki {a : ℕ} (ha : 1 ≤ a) :
    2 ^ ((2 * a + 1) * 2) ∣ ordSuzuki (2 ^ (2 * a + 1)) ∧
      ordSuzuki (2 ^ (2 * a + 1)) ≤ 2 ^ (3 * ((2 * a + 1) * 2)) := by
  have hf : 1 ≤ 2 * a + 1 := by omega
  refine ⟨?_, ?_⟩
  · rw [pow_mul]
    unfold ordSuzuki
    exact (dvd_mul_right _ _).mul_right _
  · calc ordSuzuki (2 ^ (2 * a + 1)) ≤ (2 ^ (2 * a + 1)) ^ (3 * 2) :=
          ordSuzuki_le (two_le_two_pow hf)
      _ = 2 ^ (3 * ((2 * a + 1) * 2)) := two_pow_pow (2 * a + 1) 3 2

theorem fam_twistedF4 {a : ℕ} (ha : 1 ≤ a) :
    2 ^ ((2 * a + 1) * 12) ∣ ordTwistedF4 (2 ^ (2 * a + 1)) ∧
      ordTwistedF4 (2 ^ (2 * a + 1)) ≤ 2 ^ (3 * ((2 * a + 1) * 12)) := by
  have hf : 1 ≤ 2 * a + 1 := by omega
  refine ⟨?_, ?_⟩
  · rw [pow_mul]
    unfold CFSG.Open.ordTwistedF4
    exact ((((dvd_refl ((2 ^ (2 * a + 1)) ^ 12)).mul_right _).mul_right _).mul_right _).mul_right _
  · calc ordTwistedF4 (2 ^ (2 * a + 1)) ≤ (2 ^ (2 * a + 1)) ^ (3 * 12) :=
          ordTwistedF4_le (two_le_two_pow hf)
      _ = 2 ^ (3 * ((2 * a + 1) * 12)) := two_pow_pow (2 * a + 1) 3 12

theorem ordTits_dvd : 2 ^ 11 ∣ ordTits := by
  unfold ordTits
  decide

theorem ordTits_le : ordTits ≤ 2 ^ (3 * 11) := by
  unfold ordTits
  norm_num

theorem char2Order_bound {m : ℕ} (h : Char2Order m) :
    ∃ k : ℕ, 2 ^ k ∣ m ∧ m ≤ 2 ^ (3 * k) := by
  rcases h with ⟨r, f, hr, hf, rfl⟩ | ⟨r, f, hr, hf, rfl⟩ | ⟨r, f, hr, hf, rfl⟩ |
    ⟨r, f, hr, hf, rfl⟩ | ⟨r, f, hr, hf, rfl⟩ | ⟨f, hf, rfl⟩ | ⟨f, hf, rfl⟩ | ⟨f, hf, rfl⟩ |
    ⟨f, hf, rfl⟩ | ⟨f, hf, rfl⟩ | ⟨f, hf, rfl⟩ | ⟨f, hf, rfl⟩ | ⟨a, ha, rfl⟩ | ⟨a, ha, rfl⟩ |
    rfl
  · exact ⟨_, (fam_A hr hf).1, (fam_A hr hf).2⟩
  · exact ⟨_, (fam_twistedA hr hf).1, (fam_twistedA hr hf).2⟩
  · exact ⟨_, (fam_BC (by omega : 1 ≤ r) hf).1, (fam_BC (by omega : 1 ≤ r) hf).2⟩
  · exact ⟨_, (fam_D hr hf).1, (fam_D hr hf).2⟩
  · exact ⟨_, (fam_twistedD hr hf).1, (fam_twistedD hr hf).2⟩
  · exact ⟨_, (fam_E6 hf).1, (fam_E6 hf).2⟩
  · exact ⟨_, (fam_E7 hf).1, (fam_E7 hf).2⟩
  · exact ⟨_, (fam_E8 hf).1, (fam_E8 hf).2⟩
  · exact ⟨_, (fam_F4 hf).1, (fam_F4 hf).2⟩
  · exact ⟨_, (fam_G2 hf).1, (fam_G2 hf).2⟩
  · exact ⟨_, (fam_twistedE6 hf).1, (fam_twistedE6 hf).2⟩
  · exact ⟨_, (fam_trialityD4 hf).1, (fam_trialityD4 hf).2⟩
  · exact ⟨_, (fam_suzuki ha).1, (fam_suzuki ha).2⟩
  · exact ⟨_, (fam_twistedF4 ha).1, (fam_twistedF4 ha).2⟩
  · exact ⟨11, ordTits_dvd, ordTits_le⟩

theorem tri_pos {r : ℕ} (hr : 1 ≤ r) : 1 ≤ r * (r + 1) / 2 := by
  have : 2 ≤ r * (r + 1) := by nlinarith
  omega

theorem le_mul_tri {r f : ℕ} (hr : 1 ≤ r) (hf : 1 ≤ f) : r ≤ f * (r * (r + 1) / 2) := by
  have h1 : 2 * r ≤ r * (r + 1) := by nlinarith
  have h2 : r ≤ r * (r + 1) / 2 := by omega
  exact h2.trans (Nat.le_mul_of_pos_left _ hf)

theorem le_mul_sq {r f : ℕ} (hr : 1 ≤ r) (hf : 1 ≤ f) : r ≤ f * (r * r) :=
  (Nat.le_mul_of_pos_left r hr).trans (Nat.le_mul_of_pos_left _ hf)

theorem le_of_mul_le_left {f N K : ℕ} (hN : 1 ≤ N) (h : f * N ≤ K) : f ≤ K :=
  (Nat.le_mul_of_pos_right f hN).trans h

theorem le_six_of_two_pow_dvd {k : ℕ} (h : 2 ^ k ∣ 181440) : k ≤ 6 := by
  by_contra hk
  have h7 : 2 ^ 7 ∣ 181440 := (pow_dvd_pow 2 (by omega)).trans h
  exact absurd h7 (by decide)

theorem le_seven_of_two_pow_dvd {k : ℕ} (h : 2 ^ k ∣ 1814400) : k ≤ 7 := by
  by_contra hk
  have h8 : 2 ^ 8 ∣ 1814400 := (pow_dvd_pow 2 (by omega)).trans h
  exact absurd h8 (by decide)

theorem enumA_181440 : ∀ r < 7, ∀ f < 7, 1 ≤ r → 1 ≤ f →
    f * (r * (r + 1) / 2) ≤ 6 → ordA r (2 ^ f) ≠ 181440 := by
  decide +kernel

theorem enumTwA_181440 : ∀ r < 7, ∀ f < 7, 2 ≤ r →
    f * (r * (r + 1) / 2) ≤ 6 → ordTwistedA r (2 ^ f) ≠ 181440 := by
  decide +kernel

theorem enumBC_181440 : ∀ r < 7, ∀ f < 7, 2 ≤ r →
    f * (r * r) ≤ 6 → ordBC r (2 ^ f) ≠ 181440 := by
  decide +kernel

theorem enumA_1814400 : ∀ r < 8, ∀ f < 8, 1 ≤ r → 1 ≤ f →
    f * (r * (r + 1) / 2) ≤ 7 → ordA r (2 ^ f) ≠ 1814400 := by
  decide +kernel

theorem enumTwA_1814400 : ∀ r < 8, ∀ f < 8, 2 ≤ r →
    f * (r * (r + 1) / 2) ≤ 7 → ordTwistedA r (2 ^ f) ≠ 1814400 := by
  decide +kernel

theorem enumBC_1814400 : ∀ r < 8, ∀ f < 8, 2 ≤ r →
    f * (r * r) ≤ 7 → ordBC r (2 ^ f) ≠ 1814400 := by
  decide +kernel

theorem not_char2Order_181440 : ¬ Char2Order 181440 := by
  intro h
  rcases h with ⟨r, f, hr, hf, hm⟩ | ⟨r, f, hr, hf, hm⟩ | ⟨r, f, hr, hf, hm⟩ | ⟨r, f, hr, hf, hm⟩ |
    ⟨r, f, hr, hf, hm⟩ | ⟨f, hf, hm⟩ | ⟨f, hf, hm⟩ | ⟨f, hf, hm⟩ | ⟨f, hf, hm⟩ | ⟨f, hf, hm⟩ |
    ⟨f, hf, hm⟩ | ⟨f, hf, hm⟩ | ⟨a, ha, hm⟩ | ⟨a, ha, hm⟩ | hm
  · have hd := (fam_A hr hf).1
    rw [← hm] at hd
    have hk := le_six_of_two_pow_dvd hd
    exact enumA_181440 r (by have := le_mul_tri hr hf; omega) f
      (by have := le_of_mul_le_left (tri_pos hr) hk; omega) hr hf hk hm.symm
  · have hd := (fam_twistedA hr hf).1
    rw [← hm] at hd
    have hk := le_six_of_two_pow_dvd hd
    exact enumTwA_181440 r (by have := le_mul_tri (by omega : 1 ≤ r) hf; omega) f
      (by have := le_of_mul_le_left (tri_pos (by omega : 1 ≤ r)) hk; omega) hr hk hm.symm
  · have hd := (fam_BC (by omega : 1 ≤ r) hf).1
    rw [← hm] at hd
    have hk := le_six_of_two_pow_dvd hd
    exact enumBC_181440 r (by have := le_mul_sq (by omega : 1 ≤ r) hf; omega) f
      (by have := le_of_mul_le_left (Nat.mul_pos (by omega : 0 < r) (by omega : 0 < r)) hk; omega) hr hk
      hm.symm
  · have hd := (fam_D hr hf).1
    rw [← hm] at hd
    have hk := le_six_of_two_pow_dvd hd
    have h12 : 4 * 3 ≤ r * (r - 1) := Nat.mul_le_mul (by omega) (by omega)
    have := Nat.le_mul_of_pos_left (r * (r - 1)) hf
    omega
  · have hd := (fam_twistedD hr hf).1
    rw [← hm] at hd
    have hk := le_six_of_two_pow_dvd hd
    have h12 : 4 * 3 ≤ r * (r - 1) := Nat.mul_le_mul (by omega) (by omega)
    have := Nat.le_mul_of_pos_left (r * (r - 1)) hf
    omega
  · have hd := (fam_E6 hf).1
    rw [← hm] at hd
    have hk := le_six_of_two_pow_dvd hd
    omega
  · have hd := (fam_E7 hf).1
    rw [← hm] at hd
    have hk := le_six_of_two_pow_dvd hd
    omega
  · have hd := (fam_E8 hf).1
    rw [← hm] at hd
    have hk := le_six_of_two_pow_dvd hd
    omega
  · have hd := (fam_F4 hf).1
    rw [← hm] at hd
    have hk := le_six_of_two_pow_dvd hd
    omega
  · have hd := (fam_G2 hf).1
    rw [← hm] at hd
    have hk := le_six_of_two_pow_dvd hd
    have hf1 : f = 1 := by omega
    subst hf1
    norm_num [ordG2] at hm
  · have hd := (fam_twistedE6 hf).1
    rw [← hm] at hd
    have hk := le_six_of_two_pow_dvd hd
    omega
  · have hd := (fam_trialityD4 hf).1
    rw [← hm] at hd
    have hk := le_six_of_two_pow_dvd hd
    omega
  · have hd := (fam_suzuki ha).1
    rw [← hm] at hd
    have hk := le_six_of_two_pow_dvd hd
    have ha1 : a = 1 := by omega
    subst ha1
    norm_num [ordSuzuki] at hm
  · have hd := (fam_twistedF4 ha).1
    rw [← hm] at hd
    have hk := le_six_of_two_pow_dvd hd
    omega
  · unfold ordTits at hm
    norm_num at hm

theorem not_char2Order_1814400 : ¬ Char2Order 1814400 := by
  intro h
  rcases h with ⟨r, f, hr, hf, hm⟩ | ⟨r, f, hr, hf, hm⟩ | ⟨r, f, hr, hf, hm⟩ | ⟨r, f, hr, hf, hm⟩ |
    ⟨r, f, hr, hf, hm⟩ | ⟨f, hf, hm⟩ | ⟨f, hf, hm⟩ | ⟨f, hf, hm⟩ | ⟨f, hf, hm⟩ | ⟨f, hf, hm⟩ |
    ⟨f, hf, hm⟩ | ⟨f, hf, hm⟩ | ⟨a, ha, hm⟩ | ⟨a, ha, hm⟩ | hm
  · have hd := (fam_A hr hf).1
    rw [← hm] at hd
    have hk := le_seven_of_two_pow_dvd hd
    exact enumA_1814400 r (by have := le_mul_tri hr hf; omega) f
      (by have := le_of_mul_le_left (tri_pos hr) hk; omega) hr hf hk hm.symm
  · have hd := (fam_twistedA hr hf).1
    rw [← hm] at hd
    have hk := le_seven_of_two_pow_dvd hd
    exact enumTwA_1814400 r (by have := le_mul_tri (by omega : 1 ≤ r) hf; omega) f
      (by have := le_of_mul_le_left (tri_pos (by omega : 1 ≤ r)) hk; omega) hr hk hm.symm
  · have hd := (fam_BC (by omega : 1 ≤ r) hf).1
    rw [← hm] at hd
    have hk := le_seven_of_two_pow_dvd hd
    exact enumBC_1814400 r (by have := le_mul_sq (by omega : 1 ≤ r) hf; omega) f
      (by have := le_of_mul_le_left (Nat.mul_pos (by omega : 0 < r) (by omega : 0 < r)) hk; omega) hr hk
      hm.symm
  · have hd := (fam_D hr hf).1
    rw [← hm] at hd
    have hk := le_seven_of_two_pow_dvd hd
    have h12 : 4 * 3 ≤ r * (r - 1) := Nat.mul_le_mul (by omega) (by omega)
    have := Nat.le_mul_of_pos_left (r * (r - 1)) hf
    omega
  · have hd := (fam_twistedD hr hf).1
    rw [← hm] at hd
    have hk := le_seven_of_two_pow_dvd hd
    have h12 : 4 * 3 ≤ r * (r - 1) := Nat.mul_le_mul (by omega) (by omega)
    have := Nat.le_mul_of_pos_left (r * (r - 1)) hf
    omega
  · have hd := (fam_E6 hf).1
    rw [← hm] at hd
    have hk := le_seven_of_two_pow_dvd hd
    omega
  · have hd := (fam_E7 hf).1
    rw [← hm] at hd
    have hk := le_seven_of_two_pow_dvd hd
    omega
  · have hd := (fam_E8 hf).1
    rw [← hm] at hd
    have hk := le_seven_of_two_pow_dvd hd
    omega
  · have hd := (fam_F4 hf).1
    rw [← hm] at hd
    have hk := le_seven_of_two_pow_dvd hd
    omega
  · have hd := (fam_G2 hf).1
    rw [← hm] at hd
    have hk := le_seven_of_two_pow_dvd hd
    have hf1 : f = 1 := by omega
    subst hf1
    norm_num [ordG2] at hm
  · have hd := (fam_twistedE6 hf).1
    rw [← hm] at hd
    have hk := le_seven_of_two_pow_dvd hd
    omega
  · have hd := (fam_trialityD4 hf).1
    rw [← hm] at hd
    have hk := le_seven_of_two_pow_dvd hd
    omega
  · have hd := (fam_suzuki ha).1
    rw [← hm] at hd
    have hk := le_seven_of_two_pow_dvd hd
    have ha1 : a = 1 := by omega
    subst ha1
    norm_num [ordSuzuki] at hm
  · have hd := (fam_twistedF4 ha).1
    rw [← hm] at hd
    have hk := le_seven_of_two_pow_dvd hd
    omega
  · unfold ordTits at hm
    norm_num at hm

end CFSG.LocalAnalysis.GLTheoremB.Prop95IvFact
