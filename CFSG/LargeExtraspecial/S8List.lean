module

public import CFSG.LargeExtraspecial.S8Dim4
public import CFSG.LargeExtraspecial.S8DimB
public import CFSG.LargeExtraspecial.S8One

public section

attribute [-instance] instAddCommGroupOfIsSimpleAddGroupOfIsNilpotent
  instCommGroupOfIsSimpleGroupOfIsNilpotent

namespace CFSG.LargeExtraspecial.S8

open Subgroup Module QuadraticMap CFSG.RankThree.OrthogonalInvolutions
open CFSG.LargeExtraspecial.S4 CFSG.LargeExtraspecial.S6

universe u

theorem eight_mul_lt_two_pow {m : ℕ} (hm : 7 ≤ m) : 8 * m < 2 ^ (m - 1) + 16 := by
  induction m, hm using Nat.le_induction with
  | base => norm_num
  | succ n hn ih =>
    have e : 2 ^ (n + 1 - 1) = 2 * 2 ^ (n - 1) := by
      rw [show n + 1 - 1 = (n - 1) + 1 by omega, pow_succ]
      ring
    have h8 : 8 ≤ 2 ^ (n - 1) := by
      calc 8 = 2 ^ 3 := by norm_num
        _ ≤ 2 ^ (n - 1) := Nat.pow_le_pow_right (by norm_num) (by omega)
    rw [e]
    omega

variable {G : Type u} [Group G] [Finite G] {S : Setting G} {g : G}

variable {H : Hyp4 S g} {C : Cons311 S g} {t : S.O} {ht : t ∈ S.Lbar g} {ht1 : t ≠ 1}
  {hVQ : ¬ V S g t ≤ S.Qa g}

theorem params_of_ineq {m d : ℕ} {minus : Prop} (hm : 2 ≤ m) (hd : 0 < d)
    (hdvd : 2 ^ (m - 1) ∣ d) (hdvd' : minus → 2 ^ m ∣ d) (h4 : ¬ minus → m = 3 → d ≠ 4)
    (h44 : ¬ (m = 2 ∧ ¬ minus)) (hineq : d + 16 ≤ 8 * m) :
    (minus ∧ m = 4 ∧ d = 16) ∨ (minus ∧ m = 3 ∧ d = 8) ∨ (¬ minus ∧ m = 6 ∧ d = 32) ∨
      (¬ minus ∧ m = 5 ∧ d = 16) ∨ (¬ minus ∧ m = 4 ∧ (d = 8 ∨ d = 16)) ∨
      (¬ minus ∧ m = 3 ∧ d = 8) := by
  have hle := Nat.le_of_dvd hd hdvd
  by_cases hmin : minus
  · have hle' := Nat.le_of_dvd hd (hdvd' hmin)
    obtain ⟨c, hc⟩ := hdvd' hmin
    have hm4 : m ≤ 4 := by
      by_contra h
      push Not at h
      have h8 : 8 * m < 2 ^ m + 16 := by
        rcases Nat.lt_or_ge m 7 with h7 | h7
        · interval_cases m <;> norm_num
        · have := eight_mul_lt_two_pow h7
          have : 2 ^ (m - 1) ≤ 2 ^ m := Nat.pow_le_pow_right (by norm_num) (by omega)
          omega
      omega
    interval_cases m
    · omega
    · right; left
      exact ⟨hmin, rfl, by norm_num at hc; omega⟩
    · left
      exact ⟨hmin, rfl, by norm_num at hc; omega⟩
  · obtain ⟨c, hc⟩ := hdvd
    have hm6 : m ≤ 6 := by
      by_contra h
      push Not at h
      have := eight_mul_lt_two_pow (show 7 ≤ m by omega)
      omega
    interval_cases m
    · exact absurd ⟨rfl, hmin⟩ h44
    · have := h4 hmin rfl
      right; right; right; right; right
      exact ⟨hmin, rfl, by norm_num at hc; omega⟩
    · right; right; right; right; left
      exact ⟨hmin, rfl, by norm_num at hc; omega⟩
    · right; right; right; left
      exact ⟨hmin, rfl, by norm_num at hc; omega⟩
    · right; right; left
      exact ⟨hmin, rfl, by norm_num at hc; omega⟩

theorem list_of_params (D : Std H C ht ht1 hVQ)
    (hp : (D.IsMinus ∧ D.m = 4 ∧ finrank (ZMod 2) ((Wt S g t).map (Vt S g t).mkQ) = 16) ∨
      (D.IsMinus ∧ D.m = 3 ∧ finrank (ZMod 2) ((Wt S g t).map (Vt S g t).mkQ) = 8) ∨
      (¬ D.IsMinus ∧ D.m = 6 ∧ finrank (ZMod 2) ((Wt S g t).map (Vt S g t).mkQ) = 32) ∨
      (¬ D.IsMinus ∧ D.m = 5 ∧ finrank (ZMod 2) ((Wt S g t).map (Vt S g t).mkQ) = 16) ∨
      (¬ D.IsMinus ∧ D.m = 4 ∧ (finrank (ZMod 2) ((Wt S g t).map (Vt S g t).mkQ) = 8 ∨
        finrank (ZMod 2) ((Wt S g t).map (Vt S g t).mkQ) = 16)) ∨
      (¬ D.IsMinus ∧ D.m = 3 ∧ finrank (ZMod 2) ((Wt S g t).map (Vt S g t).mkQ) = 8)) :
    (D.IsMinus ∧ D.m = 4 ∧ S.width = 16 ∧ Nat.card (Nbar S g t) = 2 ^ 17) ∨
      (D.IsMinus ∧ D.m = 3 ∧ S.width = 10 ∧ Nat.card (Nbar S g t) = 2 ^ 9) ∨
      (¬ D.IsMinus ∧ D.m = 6 ∧ S.width = 28 ∧ Nat.card (Nbar S g t) = 2 ^ 33) ∨
      (¬ D.IsMinus ∧ D.m = 5 ∧ S.width = 18 ∧ Nat.card (Nbar S g t) = 2 ^ 17) ∨
      (¬ D.IsMinus ∧ D.m = 4 ∧ ((S.width = 12 ∧ Nat.card (Nbar S g t) = 2 ^ 9) ∨
        (S.width = 16 ∧ Nat.card (Nbar S g t) = 2 ^ 17))) ∨
      (¬ D.IsMinus ∧ D.m = 3 ∧ S.width = 10 ∧ Nat.card (Nbar S g t) = 2 ^ 9) := by
  have hw := D.finrank_WV
  have hN := D.card_Nbar
  generalize S.width = n at hw hN ⊢
  generalize finrank (ZMod 2) ((Wt S g t).map (Vt S g t).mkQ) = d at hp hw
  generalize D.m = m at hp hw hN ⊢
  rcases hp with ⟨h1, rfl, rfl⟩ | ⟨h1, rfl, rfl⟩ | ⟨h1, rfl, rfl⟩ | ⟨h1, rfl, rfl⟩ |
      ⟨h1, rfl, rfl | rfl⟩ | ⟨h1, rfl, rfl⟩
  · left
    refine ⟨h1, rfl, by omega, ?_⟩
    rw [hN]; congr 1; omega
  · right; left
    refine ⟨h1, rfl, by omega, ?_⟩
    rw [hN]; congr 1; omega
  · right; right; left
    refine ⟨h1, rfl, by omega, ?_⟩
    rw [hN]; congr 1; omega
  · right; right; right; left
    refine ⟨h1, rfl, by omega, ?_⟩
    rw [hN]; congr 1; omega
  · right; right; right; right; left
    refine ⟨h1, rfl, Or.inl ⟨by omega, ?_⟩⟩
    rw [hN]; congr 1; omega
  · right; right; right; right; left
    refine ⟨h1, rfl, Or.inr ⟨by omega, ?_⟩⟩
    rw [hN]; congr 1; omega
  · right; right; right; right; right
    refine ⟨h1, rfl, by omega, ?_⟩
    rw [hN]; congr 1; omega

theorem timmesfeld_8_4 (hCorB : TimmesfeldCorBInput) (hFacts : CorBListFacts)
    (hCE : CentralExtInput.{u}) (hIrr : S5.Irr S) (hNo : NoA2 S g)
    (hΩ : OmegaCase H C ht ht1 hVQ) (D : Std H C ht ht1 hVQ)
    (hA7 : S.Lbar g ⊓ Nbar S g t ≠ zpowers t) (h44 : ¬ (D.m = 2 ∧ ¬ D.IsMinus))
    (h83 : (D.m = 2 ∧ D.IsMinus) ∨ (D.m = 3 ∧ ¬ D.IsMinus) ∨ (D.m = 4 ∧ ¬ D.IsMinus) →
      (∃ x ∈ S.Mbar, x * t * x⁻¹ ∈ S.Lbar g ∧ x * t * x⁻¹ ∉ Nbar S g t) ∨
        (D.m = 3 ∧ ¬ D.IsMinus ∧ S.width = 10) ∨ (D.m = 4 ∧ ¬ D.IsMinus ∧ S.width = 12)) :
    (D.IsMinus ∧ D.m = 4 ∧ S.width = 16 ∧ Nat.card (Nbar S g t) = 2 ^ 17) ∨
      (D.IsMinus ∧ D.m = 3 ∧ S.width = 10 ∧ Nat.card (Nbar S g t) = 2 ^ 9) ∨
      (¬ D.IsMinus ∧ D.m = 6 ∧ S.width = 28 ∧ Nat.card (Nbar S g t) = 2 ^ 33) ∨
      (¬ D.IsMinus ∧ D.m = 5 ∧ S.width = 18 ∧ Nat.card (Nbar S g t) = 2 ^ 17) ∨
      (¬ D.IsMinus ∧ D.m = 4 ∧ ((S.width = 12 ∧ Nat.card (Nbar S g t) = 2 ^ 9) ∨
        (S.width = 16 ∧ Nat.card (Nbar S g t) = 2 ^ 17))) ∨
      (¬ D.IsMinus ∧ D.m = 3 ∧ S.width = 10 ∧ Nat.card (Nbar S g t) = 2 ^ 9) := by
  apply list_of_params D
  have hm := D.hm
  have hw := D.finrank_WV
  have hpos := D.pos_finrank_WV hA7
  have hdvd := timmesfeld_6_1_two_dvd hCE H hNo C ht ht1 hVQ hΩ D.hh D.hb D.hX D.hE D.hQa
    D.polar_aV_bV (m := D.m) (by omega) D.hdim
  have hdvd' : D.IsMinus → 2 ^ D.m ∣ finrank (ZMod 2) ((Wt S g t).map (Vt S g t).mkQ) :=
    fun hmin => timmesfeld_6_1_two_dvd_minus hCE H hNo C ht ht1 hVQ hΩ D.hh D.hb D.hX D.hE
      D.hQa D.polar_aV_bV hm D.hdim hmin
  have hgen : 3 ≤ D.m ∨ D.IsMinus := by
    rcases Nat.lt_or_ge D.m 3 with h | h
    · right
      by_contra hmin
      exact h44 ⟨by omega, hmin⟩
    · left; exact h
  have h4 : ¬ D.IsMinus → D.m = 3 →
      finrank (ZMod 2) ((Wt S g t).map (Vt S g t).mkQ) ≠ 4 :=
    fun _ _ => finrank_WV_ne_four hCE hNo hΩ D hgen
  have hex : (∃ x ∈ S.Mbar, x * t * x⁻¹ ∈ S.Lbar g ∧ x * t * x⁻¹ ∉ Nbar S g t) ∨
      (D.m = 3 ∧ S.width = 10) ∨ (D.m = 4 ∧ ¬ D.IsMinus ∧ S.width = 12) := by
    by_cases hsmall : (D.m = 2 ∧ D.IsMinus) ∨ (D.m = 3 ∧ ¬ D.IsMinus) ∨ (D.m = 4 ∧ ¬ D.IsMinus)
    · rcases h83 hsmall with h | ⟨h3, -, hn⟩ | h
      · exact Or.inl h
      · exact Or.inr (Or.inl ⟨h3, hn⟩)
      · exact Or.inr (Or.inr h)
    · by_cases h3m : D.m = 3 ∧ D.IsMinus
      · rcases timmesfeld_8_2 hCorB hFacts hCE hIrr hNo hΩ D hA7 h3m.1 h3m.2 with h | h
        · exact Or.inl h
        · exact Or.inr (Or.inl ⟨h3m.1, h⟩)
      · rcases timmesfeld_8_1 hCorB hFacts hCE hIrr hNo hΩ D hA7 h44 with h | h
        · exact Or.inl h
        · exfalso
          rcases h with h | h | h
          · exact hsmall (Or.inl h)
          · by_cases hmin : D.IsMinus
            · exact h3m ⟨h, hmin⟩
            · exact hsmall (Or.inr (Or.inl ⟨h, hmin⟩))
          · exact hsmall (Or.inr (Or.inr h))
  rcases hex with ⟨x, -, hxL, hxN⟩ | ⟨h3, hn⟩ | ⟨h4m, hplus, hn⟩
  · have hineq := finrank_WV_add_sixteen_le hCE hNo hΩ D hgen rfl hxL hxN
    exact params_of_ineq hm hpos hdvd hdvd' h4 h44 hineq
  · have hd : finrank (ZMod 2) ((Wt S g t).map (Vt S g t).mkQ) = 8 := by omega
    by_cases hmin : D.IsMinus
    · exact Or.inr (Or.inl ⟨hmin, h3, hd⟩)
    · exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inr ⟨hmin, h3, hd⟩))))
  · have hd : finrank (ZMod 2) ((Wt S g t).map (Vt S g t).mkQ) = 8 := by omega
    exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inl ⟨hplus, h4m, Or.inl hd⟩))))

end CFSG.LargeExtraspecial.S8
