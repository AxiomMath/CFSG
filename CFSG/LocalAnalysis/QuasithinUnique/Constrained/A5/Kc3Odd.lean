module

public import CFSG.LocalAnalysis.QuasithinUnique.Constrained.A5.Kc3Families
public import CFSG.LocalAnalysis.QuasithinUnique.Constrained.A5.Delta5
public import CFSG.Timmesfeld.Orders.ExceptionalUntwisted
public import CFSG.Timmesfeld.Orders.ExceptionalTwisted
public import CFSG.Adapters.ProjectiveSpecialLinear

public section

namespace CFSG.QuasithinUnique.A5

open CFSG.Open CFSG.Quasithin CFSG.QuasithinUnique CFSG.QuasithinUnique.DoubleA3
  CFSG.Assembly.LowTwoRank

@[expose] def Kc3G2Ev (X : Type) [Group X] : Prop :=
  ∃ f : ℕ, 2 ≤ f ∧ Even f ∧ CFSG.Blueprint.ChevalleyExceptionalModel X .G2 2 f

@[expose] def Kc3D4Ev (X : Type) [Group X] : Prop :=
  ∃ f : ℕ, 2 ≤ f ∧ Even f ∧ CFSG.Blueprint.ChevalleyExceptionalModel X .trialityD4 2 f

theorem five_dvd_card_of_alt5 {G : Type} [Group G] [Finite G] {L : Subgroup G}
    (h5 : IsAltType L 5) : 5 ∣ Nat.card ↥L := by
  obtain ⟨α, hα, -⟩ := h5
  have h := Subgroup.card_dvd_of_surjective hα
  rw [Delta5.a5_card] at h
  exact dvd_trans (by norm_num) h

theorem five_dvd_card_quot {G : Type} [Group G] [Finite G] {K L : Subgroup G}
    (hZ : IsPGroup 2 ↥(Subgroup.center ↥K)) (hLK : L ≤ K) (h5 : IsAltType L 5) :
    5 ∣ Nat.card (↥K ⧸ Subgroup.center ↥K) := by
  have h1 : 5 ∣ Nat.card ↥L := five_dvd_card_of_alt5 h5
  have h2 : Nat.card ↥L ∣ Nat.card ↥K :=
    dvd_trans (Nat.card_congr (Subgroup.subgroupOfEquivOfLe hLK).toEquiv.symm ▸ dvd_rfl)
      (Subgroup.card_subgroup_dvd_card (L.subgroupOf K))
  have h3 : Nat.card ↥K = Nat.card (↥K ⧸ Subgroup.center ↥K) * Nat.card ↥(Subgroup.center ↥K) :=
    Subgroup.card_eq_card_quotient_mul_card_subgroup _
  obtain ⟨n, hn⟩ := IsPGroup.iff_card.1 hZ
  have h4 : Nat.Coprime 5 (Nat.card ↥(Subgroup.center ↥K)) := by
    rw [hn]
    exact Nat.Coprime.pow_right _ (by norm_num)
  have h5' : 5 ∣ Nat.card (↥K ⧸ Subgroup.center ↥K) * Nat.card ↥(Subgroup.center ↥K) := by
    rw [← h3]
    exact dvd_trans h1 h2
  exact h4.dvd_of_dvd_mul_right h5'

theorem two_pow_odd_mod_five {f : ℕ} (hf : Odd f) :
    ((2 ^ f : ℕ) : ZMod 5) = 2 ∨ ((2 ^ f : ℕ) : ZMod 5) = 3 := by
  obtain ⟨k, rfl⟩ := hf
  push_cast
  have h4 : (2 : ZMod 5) ^ (2 * k + 1) = (-1) ^ k * 2 := by
    rw [pow_succ, pow_mul]
    have : (2 : ZMod 5) ^ 2 = -1 := by decide
    rw [this]
  rw [h4]
  rcases neg_one_pow_eq_or (ZMod 5) k with h | h <;> rw [h]
  · left; simp
  · right; decide

theorem aux_g2 (r : ZMod 5) (hr : r = 2 ∨ r = 3) : r ^ 6 * (r ^ 6 - 1) * (r ^ 2 - 1) ≠ 0 := by
  rcases hr with rfl | rfl <;> decide

theorem aux_d4 (r : ZMod 5) (hr : r = 2 ∨ r = 3) :
    r ^ 12 * (r ^ 8 + r ^ 4 + 1) * (r ^ 6 - 1) * (r ^ 2 - 1) ≠ 0 := by
  rcases hr with rfl | rfl <;> decide

theorem not_five_dvd_ordG2 {q : ℕ} (hq : 1 ≤ q) (hr : (q : ZMod 5) = 2 ∨ (q : ZMod 5) = 3) :
    ¬ 5 ∣ ordG2 q := by
  intro h
  have h0 : ((ordG2 q : ℕ) : ZMod 5) = 0 := (ZMod.natCast_eq_zero_iff _ _).2 h
  unfold ordG2 at h0
  rw [Nat.cast_mul, Nat.cast_mul, Nat.cast_sub (Nat.one_le_pow _ _ hq),
    Nat.cast_sub (Nat.one_le_pow _ _ hq)] at h0
  simp only [Nat.cast_pow, Nat.cast_one] at h0
  exact aux_g2 _ hr h0

theorem not_five_dvd_ordTrialityD4 {q : ℕ} (hq : 1 ≤ q)
    (hr : (q : ZMod 5) = 2 ∨ (q : ZMod 5) = 3) : ¬ 5 ∣ ordTrialityD4 q := by
  intro h
  have h0 : ((ordTrialityD4 q : ℕ) : ZMod 5) = 0 := (ZMod.natCast_eq_zero_iff _ _).2 h
  unfold ordTrialityD4 at h0
  rw [Nat.cast_mul, Nat.cast_mul, Nat.cast_mul, Nat.cast_sub (Nat.one_le_pow _ _ hq),
    Nat.cast_sub (Nat.one_le_pow _ _ hq)] at h0
  simp only [Nat.cast_pow, Nat.cast_one, Nat.cast_add] at h0
  exact aux_d4 _ hr h0

theorem kc3For_g2_of_even
    (h : Kc3For Kc3G2Ev) : Kc3For Kc3G2 := by
  intro G _ _ K L S₀ T₀ hq hmod hZ hLK hL h5 hSL hS hT hST hTK hTS
  obtain ⟨f, hf, hm⟩ := hmod
  rcases Nat.even_or_odd f with hev | hodd
  · exact h G K L S₀ T₀ hq ⟨f, hf, hev, hm⟩ hZ hLK hL h5 hSL hS hT hST hTK hTS
  · exfalso
    have h5q := five_dvd_card_quot hZ hLK h5
    have hcard := CFSG.Timmesfeld.ExceptionalOrders.card_of_untwistedChevalleyModel_G2 hm.2
    rw [hcard] at h5q
    exact not_five_dvd_ordG2 Nat.one_le_two_pow (two_pow_odd_mod_five hodd) h5q

theorem kc3For_d4_of_even
    (h : Kc3For Kc3D4Ev) : Kc3For Kc3D4 := by
  intro G _ _ K L S₀ T₀ hq hmod hZ hLK hL h5 hSL hS hT hST hTK hTS
  obtain ⟨f, hf, hm⟩ := hmod
  rcases Nat.even_or_odd f with hev | hodd
  · exact h G K L S₀ T₀ hq ⟨f, by obtain ⟨k, hk⟩ := hev; omega, hev, hm⟩ hZ hLK hL h5 hSL hS hT hST hTK hTS
  · exfalso
    have h5q := five_dvd_card_quot hZ hLK h5
    have hcard := CFSG.Timmesfeld.ExceptionalOrders.card_of_twistedChevalleyModel_D4_two hf hm.2
    rw [hcard] at h5q
    exact not_five_dvd_ordTrialityD4 Nat.one_le_two_pow (two_pow_odd_mod_five hodd) h5q

end CFSG.QuasithinUnique.A5
