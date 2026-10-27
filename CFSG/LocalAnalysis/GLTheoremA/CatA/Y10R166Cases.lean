module

public import CFSG.LocalAnalysis.GLTheoremA.CatA.Y10F166
public import CFSG.LocalAnalysis.GLTheoremA.S11.LabelFacts

public section

namespace CFSG.LocalAnalysis.GLTheoremA.Y10F

open CFSG.Open CFSG.Yardstones.Md0ec50421ce4 CFSG.LocalAnalysis.GLTheoremB
open scoped commutatorElement

@[expose] def I166On (P : GLALabel → ℕ → Prop → Prop) : Prop :=
  ∀ (K : Type) [Group K] [Finite K] (lab : GLALabel) (p : ℕ),
    HasLabel K (fun l : GLALabel => l = lab) →
    P lab p (Subgroup.center K = ⊥) → p.Prime → p ≠ 2 →
    (∀ lab' : GLALabel, HasLabel K (fun l : GLALabel => l = lab') → ¬ GLASplit16 p lab') →
    4 ≤ evenRank K → GLATwoLocalRank p K + 1 = evenRank K →
    ∃ (q : ℕ) (B' : Subgroup K) (x' : K) (J : Subgroup K), Concl166S K p q B' x' J

theorem hasLabel_inLambda2 {X : Type} [Group X] {lab : GLALabel}
    (h : HasLabel X (fun l : GLALabel => l = lab)) : GLAInLambda2 lab := by
  obtain ⟨-, lab', hlab', R, _, I, F, θ, -, -, hP⟩ :=
    CFSG.StandardType.Canonical.largeEvenMarking_exists h
  simpa [hP] using hlab'

@[expose] def i166FamB (lab : GLALabel) (p : ℕ) (_z : Prop) : Prop :=
  lab.tag = .B ∧ 2 ≤ lab.n ∧ p ∣ 2 ^ lab.n + 1

@[expose] def i166FamD (lab : GLALabel) (p : ℕ) (_z : Prop) : Prop :=
  lab.tag = .D ∧ 2 ≤ lab.n ∧ p ∣ 2 ^ lab.n + 1

@[expose] def i166FamF4 (lab : GLALabel) (p : ℕ) (_z : Prop) : Prop :=
  lab.tag = .F4 ∧ 2 ≤ lab.n ∧ p ∣ 2 ^ lab.n + 1

@[expose] def i166FamE7 (lab : GLALabel) (p : ℕ) (_z : Prop) : Prop :=
  lab.tag = .E7 ∧ 2 ≤ lab.n ∧ p ∣ 2 ^ lab.n + 1

@[expose] def i166FamE8 (lab : GLALabel) (p : ℕ) (_z : Prop) : Prop :=
  lab.tag = .E8 ∧ 2 ≤ lab.n ∧ p ∣ 2 ^ lab.n + 1

@[expose] def i166FamTwA5 (lab : GLALabel) (p : ℕ) (_z : Prop) : Prop :=
  lab.tag = .twA ∧ lab.rank = 5 ∧ 2 ≤ lab.n ∧ p ∣ 2 ^ lab.n - 1

@[expose] def i166FamTwE6 (lab : GLALabel) (p : ℕ) (_z : Prop) : Prop :=
  lab.tag = .twE6 ∧ 2 ≤ lab.n ∧ p ∣ 2 ^ lab.n - 1

@[expose] def i166FamA5Four (lab : GLALabel) (p : ℕ) (z : Prop) : Prop :=
  lab = ⟨.A, 5, 2⟩ ∧ z ∧ p = 5

@[expose] def i166FamE6Four (lab : GLALabel) (p : ℕ) (z : Prop) : Prop :=
  lab = ⟨.E6, 0, 2⟩ ∧ z ∧ p = 5

@[expose] def i166FamA8Two (lab : GLALabel) (p : ℕ) (_z : Prop) : Prop :=
  lab = ⟨.A, 8, 1⟩ ∧ p = 7

theorem i166_label_cases {p : ℕ} (hp : p.Prime) (hp2 : p ≠ 2) {lab : GLALabel} {z : Prop}
    (hlab : GLAInLambda2 lab) (hh : GLAHalfSplit16 p lab z) (hns : ¬ GLASplit16 p lab)
    (hE6 : p = 7 → lab ≠ ⟨.E6, 0, 1⟩) :
    i166FamB lab p z ∨ i166FamD lab p z ∨ i166FamF4 lab p z ∨ i166FamE7 lab p z ∨
      i166FamE8 lab p z ∨ i166FamTwA5 lab p z ∨ i166FamTwE6 lab p z ∨ i166FamA5Four lab p z ∨
      i166FamE6Four lab p z ∨ i166FamA8Two lab p z := by
  have hlist : List110 p lab z := ⟨hh, hns⟩
  rcases List110.cases hlist with hA | hTw | hFour | hA8 | hE62
  ·
    obtain ⟨ht, hdvd⟩ := hA
    have hn2 : 2 ≤ lab.n := by
      have hn1 : 1 ≤ lab.n := hlab.1
      by_contra hlt
      have hn : lab.n = 1 := by omega
      have hp3 : p = 3 := by
        have h3 : p ∣ 3 := by simpa [hn] using hdvd
        exact (Nat.prime_dvd_prime_iff_eq hp Nat.prime_three).1 h3
      exact hns (Or.inr (Or.inr (Or.inr ⟨hn, hp3⟩)))
    rcases ht with hB | hD | hF4 | hE7 | hE8
    · left; exact ⟨hB, hn2, hdvd⟩
    · right; left; exact ⟨hD, hn2, hdvd⟩
    · right; right; left; exact ⟨hF4, hn2, hdvd⟩
    · right; right; right; left; exact ⟨hE7, hn2, hdvd⟩
    · right; right; right; right; left; exact ⟨hE8, hn2, hdvd⟩
  ·
    obtain ⟨htw, hdvd⟩ := hTw
    have hn2 : 2 ≤ lab.n := two_le_of_dvd_two_pow_sub_one hp hlab.1 hdvd
    rcases htw with ⟨ht, hr⟩ | ht
    · right; right; right; right; right; left; exact ⟨ht, hr, hn2, hdvd⟩
    · right; right; right; right; right; right; left; exact ⟨ht, hn2, hdvd⟩
  ·
    obtain ⟨⟨ht, hr⟩ | ht, hn, hz, hp5⟩ := hFour
    · right; right; right; right; right; right; right; left
      exact ⟨lab_eq_of ht hr hn, hz, hp5⟩
    · have hr : lab.rank = 0 := rank_zero_of_lam hlab (Or.inl ht)
      right; right; right; right; right; right; right; right; left
      exact ⟨lab_eq_of ht hr hn, hz, hp5⟩
  ·
    obtain ⟨ht, hr, hn, hp7⟩ := hA8
    right; right; right; right; right; right; right; right; right
    exact ⟨lab_eq_of ht hr hn, hp7⟩
  ·
    obtain ⟨ht, hn, hp7⟩ := hE62
    have hr : lab.rank = 0 := rank_zero_of_lam hlab (Or.inl ht)
    exact absurd (lab_eq_of ht hr hn) (hE6 hp7)

theorem i166Fact_of_families (hB : I166On i166FamB) (hD : I166On i166FamD)
    (hF4 : I166On i166FamF4) (hE7 : I166On i166FamE7) (hE8 : I166On i166FamE8)
    (hTwA5 : I166On i166FamTwA5) (hTwE6 : I166On i166FamTwE6)
    (hA5Four : I166On i166FamA5Four) (hE6Four : I166On i166FamE6Four)
    (hA8Two : I166On i166FamA8Two) : I166Fact := by
  intro K _ _ _ p hp hp2 hhalf hns he hr hE6
  obtain ⟨lab, hlab, hh⟩ := hhalf
  have hlab2 : GLAInLambda2 lab := hasLabel_inLambda2 hlab
  have hE6' : p = 7 → lab ≠ ⟨.E6, 0, 1⟩ := by
    intro hp7 hEq
    exact hE6 hp7 (by simpa [hEq] using hlab)
  rcases i166_label_cases hp hp2 hlab2 hh (hns lab hlab) hE6' with
    hfam | hfam | hfam | hfam | hfam | hfam | hfam | hfam | hfam | hfam
  · exact hB K lab p hlab hfam hp hp2 hns he hr
  · exact hD K lab p hlab hfam hp hp2 hns he hr
  · exact hF4 K lab p hlab hfam hp hp2 hns he hr
  · exact hE7 K lab p hlab hfam hp hp2 hns he hr
  · exact hE8 K lab p hlab hfam hp hp2 hns he hr
  · exact hTwA5 K lab p hlab hfam hp hp2 hns he hr
  · exact hTwE6 K lab p hlab hfam hp hp2 hns he hr
  · exact hA5Four K lab p hlab hfam hp hp2 hns he hr
  · exact hE6Four K lab p hlab hfam hp hp2 hns he hr
  · exact hA8Two K lab p hlab hfam hp hp2 hns he hr

end CFSG.LocalAnalysis.GLTheoremA.Y10F
