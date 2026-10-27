module

public import CFSG.CGT.T75G.Sec68Main
import CFSG.Adapters.StatedClassicalUnitaryOrders
public import CFSG.CGT.Timmesfeld75.Sec68FromCorB

public section

namespace CFSG.CGT.T75G

open CFSG.Open CFSG.Blueprint CFSG.Assembly.LowTwoRank CFSG.CGT.Timmesfeld75 CFSG.Timmesfeld
open CFSG.Timmesfeld.Orders

section Orders

theorem profile_ordA_two {f : ℕ} (hf : 1 ≤ f) : Profile (ordA 2 (2 ^ f)) (f * 3) (zA 2 f) :=
  profile_ordA (n := 2) (by norm_num) hf

theorem ordA_two_mul_gcd (f : ℕ) :
    ordA 2 (2 ^ f) * Nat.gcd 3 (2 ^ f - 1) =
      (2 ^ f) ^ 3 * (((2 ^ f) ^ 2 - 1) * ((2 ^ f) ^ 3 - 1)) := by
  have hdvd : Nat.gcd 3 (2 ^ f - 1) ∣
      (2 ^ f) ^ 3 * (((2 ^ f) ^ 2 - 1) * ((2 ^ f) ^ 3 - 1)) :=
    ((Nat.gcd_dvd_right 3 (2 ^ f - 1)).trans (Nat.sub_one_dvd_pow_sub_one (2 ^ f) 2)).trans
      ((dvd_mul_right _ _).trans (dvd_mul_left _ _))
  have h : ordA 2 (2 ^ f) =
      (2 ^ f) ^ 3 * (((2 ^ f) ^ 2 - 1) * ((2 ^ f) ^ 3 - 1)) / Nat.gcd 3 (2 ^ f - 1) := by
    unfold ordA
    rw [show Finset.Icc 2 (2 + 1) = {2, 3} by decide, Finset.prod_pair (by norm_num)]
  rw [h]
  exact Nat.div_mul_cancel hdvd

theorem three_dvd_two_pow_sub_one {f : ℕ} (hf : Even f) : 3 ∣ 2 ^ f - 1 := by
  obtain ⟨k, rfl⟩ := hf
  have : 2 ^ (k + k) = 4 ^ k := by rw [← two_mul, pow_mul]; norm_num
  rw [this]
  exact Nat.sub_one_dvd_pow_sub_one 4 k

theorem numeric_G2 {q X : ℕ} (hq : 2 ≤ q)
    (hX : X * 3 = (q ^ 2) ^ 3 * (((q ^ 2) ^ 2 - 1) * ((q ^ 2) ^ 3 - 1)))
    (h : X = q ^ 6 * (q ^ 6 - 1) * (q ^ 2 - 1)) : False := by
  subst h
  have h6 : q ^ 6 = (q ^ 2) ^ 3 := by ring
  rw [h6] at hX
  have hu : 4 ≤ q ^ 2 := by nlinarith
  generalize q ^ 2 = u at hX hu
  have h1 : 1 ≤ u := by omega
  have h2 : 1 ≤ u ^ 2 := Nat.one_le_pow _ _ (by omega)
  have h3 : 1 ≤ u ^ 3 := Nat.one_le_pow _ _ (by omega)
  zify [h1, h2, h3] at hX
  have hu' : (4 : ℤ) ≤ u := by exact_mod_cast hu
  have hu3 : (64 : ℤ) ≤ (u : ℤ) ^ 3 := by
    have := pow_le_pow_left₀ (by norm_num) hu' 3
    norm_num at this
    exact this
  have hP : (u : ℤ) ^ 3 * ((u : ℤ) ^ 3 - 1) * ((u : ℤ) - 1) ≠ 0 :=
    mul_ne_zero (mul_ne_zero (by positivity) (by linarith)) (by linarith)
  have e : ((u : ℤ) ^ 3 * ((u : ℤ) ^ 3 - 1) * ((u : ℤ) - 1)) * 3 =
      ((u : ℤ) ^ 3 * ((u : ℤ) ^ 3 - 1) * ((u : ℤ) - 1)) * ((u : ℤ) + 1) := by
    linear_combination hX
  have := mul_left_cancel₀ hP e
  linarith

theorem numeric_D4 {q X : ℕ} (hq : 2 ≤ q)
    (hX : X * 3 = (q ^ 4) ^ 3 * (((q ^ 4) ^ 2 - 1) * ((q ^ 4) ^ 3 - 1)))
    (h : X = q ^ 12 * (q ^ 8 + q ^ 4 + 1) * (q ^ 6 - 1) * (q ^ 2 - 1)) : False := by
  subst h
  obtain ⟨u, hu_def⟩ : ∃ u, u = q ^ 2 := ⟨_, rfl⟩
  have hu : 4 ≤ u := by rw [hu_def]; nlinarith
  have e4 : q ^ 4 = u ^ 2 := by rw [hu_def]; ring
  have e6 : q ^ 6 = u ^ 3 := by rw [hu_def]; ring
  have e8 : q ^ 8 = u ^ 4 := by rw [hu_def]; ring
  have e12 : q ^ 12 = u ^ 6 := by rw [hu_def]; ring
  rw [e12, e8, e4, e6, ← hu_def] at hX
  have h1 : 1 ≤ u := by omega
  have h2 : 1 ≤ (u ^ 2) ^ 2 := Nat.one_le_pow _ _ (Nat.one_le_pow _ _ h1)
  have h3 : 1 ≤ (u ^ 2) ^ 3 := Nat.one_le_pow _ _ (Nat.one_le_pow _ _ h1)
  have h4 : 1 ≤ u ^ 3 := Nat.one_le_pow _ _ h1
  zify [h1, h2, h3, h4] at hX
  have hu' : (4 : ℤ) ≤ u := by exact_mod_cast hu
  have hu3 : (64 : ℤ) ≤ (u : ℤ) ^ 3 := by
    have := pow_le_pow_left₀ (by norm_num) hu' 3
    norm_num at this
    exact this
  have hP : (u : ℤ) ^ 6 * ((u : ℤ) ^ 3 - 1) * ((u : ℤ) - 1) ≠ 0 :=
    mul_ne_zero (mul_ne_zero (by positivity) (by linarith)) (by linarith)
  have e : ((u : ℤ) ^ 6 * ((u : ℤ) ^ 3 - 1) * ((u : ℤ) - 1)) *
      (3 * ((u : ℤ) ^ 4 + (u : ℤ) ^ 2 + 1)) =
      ((u : ℤ) ^ 6 * ((u : ℤ) ^ 3 - 1) * ((u : ℤ) - 1)) *
      (((u : ℤ) + 1) * ((u : ℤ) ^ 2 + 1) * ((u : ℤ) ^ 3 + 1)) := by
    linear_combination hX
  have := mul_left_cancel₀ hP e
  nlinarith [pow_pos (show (0 : ℤ) < u by linarith) 5, pow_pos (show (0 : ℤ) < u by linarith) 4,
    pow_pos (show (0 : ℤ) < u by linarith) 3, pow_pos (show (0 : ℤ) < u by linarith) 2]

theorem ordA_two_ne_ordG2 {f g : ℕ} (hf : 1 ≤ f) (hg : 1 ≤ g) :
    ordA 2 (2 ^ f) ≠ ordG2 (2 ^ g) := by
  intro h
  have hG : Profile (ordA 2 (2 ^ f)) (g * 6) (zG2 g) := by
    rw [h]
    exact profile_ordG2 hg
  have hN : f * 3 = g * 6 := ((profile_ordA_two hf).transfer hG).1
  have hf2 : f = 2 * g := by omega
  subst hf2
  have hgcd : Nat.gcd 3 (2 ^ (2 * g) - 1) = 3 :=
    Nat.gcd_eq_left (three_dvd_two_pow_sub_one (even_two_mul g))
  have hX := ordA_two_mul_gcd (2 * g)
  rw [hgcd, pow_mul'] at hX
  rw [pow_mul'] at h
  have hq : 2 ≤ 2 ^ g := by
    calc 2 = 2 ^ 1 := by norm_num
      _ ≤ 2 ^ g := Nat.pow_le_pow_right (by norm_num) hg
  exact numeric_G2 hq hX h

theorem ordA_two_ne_ordTrialityD4 {f g : ℕ} (hf : 1 ≤ f) (hg : 1 ≤ g) :
    ordA 2 (2 ^ f) ≠ ordTrialityD4 (2 ^ g) := by
  intro h
  have hG : Profile (ordA 2 (2 ^ f)) (g * 12) (zD4 g) := by
    rw [h]
    exact profile_ordTrialityD4 hg
  have hN : f * 3 = g * 12 := ((profile_ordA_two hf).transfer hG).1
  have hf4 : f = 4 * g := by omega
  subst hf4
  have hgcd : Nat.gcd 3 (2 ^ (4 * g) - 1) = 3 :=
    Nat.gcd_eq_left (three_dvd_two_pow_sub_one ⟨2 * g, by ring⟩)
  have hX := ordA_two_mul_gcd (4 * g)
  rw [hgcd, pow_mul'] at hX
  rw [pow_mul'] at h
  have hq : 2 ≤ 2 ^ g := by
    calc 2 = 2 ^ 1 := by norm_num
      _ ≤ 2 ^ g := Nat.pow_le_pow_right (by norm_num) hg
  exact numeric_D4 hq hX h

theorem card_lieModel_psu33 {Y : Type} [Group Y] (h : LieModel Y .PSU 3 3 1) :
    Nat.card Y = 6048 :=
  CFSG.Open.StatedAPI.card_of_statedClassicalModel_psu_three_three (h.statedClassicalModel (by decide))

theorem ordA_two_ne_psu33 {f : ℕ} (hf : 1 ≤ f) : ordA 2 (2 ^ f) ≠ 6048 := fun h =>
  (profile_ordA_two hf).ne_of_ne (a := 5) (r := 189) (by decide) (by omega)
    (by rw [h]; norm_num)

theorem ordA_two_ne_j2 {f : ℕ} (hf : 1 ≤ f) : ordA 2 (2 ^ f) ≠ 2 ^ 7 * 3 ^ 3 * 5 ^ 2 * 7 := fun h =>
  (profile_ordA_two hf).ne_of_ne (a := 7) (r := 3 ^ 3 * 5 ^ 2 * 7) (by decide) (by omega)
    (by rw [h]; ring)

end Orders

section Final


theorem sec68Inspection_direct : Sec68Inspection := by
  intro G _ T T₁ m hy hm hq hT hnat hDD hcl hZ hab _ Y _ ⟨e⟩ hexc
  obtain ⟨f, hf, hLM⟩ := Cfg68.lieModel_psl3 (T := T) (T₁ := T₁)
    ⟨hy, hm, hq, hT, hnat, hDD, hcl, hZ, hab⟩
  have hcard : Nat.card Y = ordA 2 (2 ^ f) := by
    rw [← Nat.card_congr e.toEquiv]
    exact (card_statedClassicalModel_two
      (statedClassicalModel_of_lieModel_of_ne_zero (by norm_num) hLM)).1 rfl
  rcases hexc with ⟨g, hg⟩ | hU | ⟨g, hg⟩ | hJ
  · have hc := Final.chevalleyExceptionalModel_of_lieModel (by decide) hg
    exact ordA_two_ne_ordG2 hf hc.1.2.1 (hcard.symm.trans (card_chevalleyExceptionalModel_two hc))
  · exact ordA_two_ne_psu33 hf (hcard.symm.trans (card_lieModel_psu33 hU))
  · have hc := Final.chevalleyExceptionalModel_of_lieModel (by decide) hg
    exact ordA_two_ne_ordTrialityD4 hf hc.1.2.1
      (hcard.symm.trans (card_chevalleyExceptionalModel_two hc))
  · obtain ⟨e'⟩ := hJ
    exact ordA_two_ne_j2 hf (hcard.symm.trans ((Nat.card_congr e'.toEquiv).trans
      (CFSG.Sporadic.J2.card_J2.trans (by norm_num))))

end Final

end CFSG.CGT.T75G
