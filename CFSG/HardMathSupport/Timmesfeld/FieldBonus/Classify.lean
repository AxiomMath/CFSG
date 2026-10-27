module

public import CFSG.HardMathSupport.Timmesfeld.FieldBonus.Assembly
public import CFSG.Quasithin.H13.KGFactLieOutAbL
public import CFSG.Quasithin.Vol2.Ch4Sec2T425C27G

public section

namespace CFSG.HardMathSupport.Timmesfeld.FieldBonus

open CFSG.Assembly.LowTwoRank CFSG.SectionRank CFSG.SectionRank.ClassicalEven CFSG.Models
open CFSG.HardMathSupport.Timmesfeld.Tables.Census (TFAaModels)

theorem two_le_pRank_three_psl_three_of_dvd {X : Type} [Group X] [Finite X] {p f : ℕ}
    (hC : StatedClassicalModel X .PSL 3 p f) (h3 : 3 ∣ p ^ f - 1) :
    2 ≤ CFSG.Open.pRank 3 (⊤ : Subgroup X) := by
  obtain ⟨-, K, _, _, hK, ⟨e⟩⟩ := hC
  have : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  rw [pRank_top_eq_of_mulEquiv (by norm_num) e]
  exact CFSG.Quasithin.H13.Ch4.T425C27.two_le_pRank_psl3 (F := K) (by rw [hK]; exact h3)

theorem two_le_pRank_three_psu_three_of_dvd {X : Type} [Group X] [Finite X] {p f : ℕ}
    (hC : StatedClassicalModel X .PSU 3 p f) (h3 : 3 ∣ p ^ f + 1) :
    2 ≤ CFSG.Open.pRank 3 (⊤ : Subgroup X) := by
  obtain ⟨⟨hp, -⟩, K, _, _, hK, ⟨e⟩⟩ := hC
  have : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  rw [pRank_top_eq_of_mulEquiv (by norm_num) e]
  obtain ⟨A, hA, hc⟩ := CFSG.Quasithin.H13.KGLieOut.hasElemAb_nine_psu3
    (Nat.one_le_iff_ne_zero.2 (pow_pos hp.pos f).ne') hK h3
  exact le_pRank (by norm_num) le_top hA (k := 2) (by rw [hc]; norm_num)

theorem two_le_pRank_three_psu_four_of_dvd {X : Type} [Group X] [Finite X] {n p f : ℕ}
    (hn : 4 ≤ n) (hC : StatedClassicalModel X .PSU n p f) (h3 : 3 ∣ p ^ f + 1) :
    2 ≤ CFSG.Open.pRank 3 (⊤ : Subgroup X) := by
  obtain ⟨⟨hp, -⟩, K, _, _, hK, ⟨e⟩⟩ := hC
  have : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  have hq : p ^ f ≠ 0 := (pow_pos hp.pos f).ne'
  have hcard : Nat.card Kˣ = (p ^ f + 1) * (p ^ f - 1) := by
    rw [Nat.card_units, hK, ← Nat.sq_sub_sq, one_pow]
  obtain ⟨ζ, hζ⟩ := exists_prime_orderOf_dvd_card' (G := Kˣ) 3
    (by rw [hcard]; exact h3.mul_right _)
  have hζq : ζ ^ (p ^ f + 1) = 1 :=
    orderOf_dvd_iff_pow_eq_one.1 (by rw [hζ]; exact h3)
  have h3r := three_le_pRank_torus (H := StatedSU n (p ^ f) K) (r := 3) (by norm_num) hζ
    (i₀ := ⟨0, by omega⟩) (i₁ := ⟨1, by omega⟩) (i₂ := ⟨2, by omega⟩) (i₃ := ⟨3, by omega⟩)
    (by simp) (by simp) (by simp) (by simp) (by simp) (by simp)
    fun j => torusDiag_mem_SU hq (prod_torusVec ζ j _)
      (by rw [torusVec_pow, hζq, torusVec_one])
  rw [pRank_top_eq_of_mulEquiv (by norm_num) e]
  omega

theorem two_le_pRank_of_char_three {X : Type} [Group X] [Finite X] {t : StatedLieTag}
    {n f : ℕ} (hC : StatedClassicalModel X t n 3 f) : 2 ≤ CFSG.Open.pRank 3 (⊤ : Subgroup X) := by
  obtain ⟨-, hf, hr⟩ := classical_model_rank (by norm_num : (3 : ℕ) ≠ 2) hC
  cases t with
  | PSL =>
    obtain ⟨⟨-, -, hn2, -, hne3⟩, -⟩ := hC
    rcases hr with ⟨-, ⟨hn, hfr⟩ | ⟨h3, hfr⟩ | h4⟩ | ⟨h, -⟩ | ⟨h, -⟩ | h4
    · have : f ≠ 1 := by
        rintro rfl
        exact hne3 (by simp [hn])
      omega
    · omega
    · omega
    · exact absurd h (by decide)
    · exact absurd h (by decide)
    · omega
  | PSU =>
    rcases hr with ⟨h, -⟩ | ⟨-, ⟨h3, hfr⟩ | h4⟩ | ⟨h, -⟩ | h4
    · exact absurd h (by decide)
    · omega
    · omega
    · exact absurd h (by decide)
    · omega
  | PSp =>
    rcases hr with ⟨h, -⟩ | ⟨h, -⟩ | ⟨-, ⟨h3, hfr⟩ | h4⟩ | h4
    · exact absurd h (by decide)
    · exact absurd h (by decide)
    · omega
    · omega
    · omega
  | POmegaOdd =>
    rcases hr with ⟨h, -⟩ | ⟨h, -⟩ | ⟨h, -⟩ | h4
    · exact absurd h (by decide)
    · exact absurd h (by decide)
    · exact absurd h (by decide)
    · omega
  | POmegaPlus =>
    rcases hr with ⟨h, -⟩ | ⟨h, -⟩ | ⟨h, -⟩ | h4
    · exact absurd h (by decide)
    · exact absurd h (by decide)
    · exact absurd h (by decide)
    · omega
  | POmegaMinus =>
    rcases hr with ⟨h, -⟩ | ⟨h, -⟩ | ⟨h, -⟩ | h4
    · exact absurd h (by decide)
    · exact absurd h (by decide)
    · exact absurd h (by decide)
    · omega
  | _ => exact hC.2.elim

@[expose] def OpenRankOneCase (t : StatedLieTag) (n p f : ℕ) : Prop :=
  (t = .PSU ∧ 4 ≤ n ∧ p ≠ 3 ∧ p ^ f % 3 = 1) ∨ (t = .POmegaOdd ∧ p ≠ 3) ∨
    ((t = .POmegaPlus ∨ t = .POmegaMinus) ∧ p ≠ 2 ∧ p ≠ 3) ∨
    (t ≠ .PSL ∧ t ≠ .PSU ∧ t ≠ .PSp ∧ t ≠ .POmegaOdd ∧ t ≠ .POmegaPlus ∧ t ≠ .POmegaMinus)

@[expose] def LieRankOneOpen : Prop :=
  ∀ (X : Type) [Group X] [Finite X] (t : StatedLieTag) (n p f : ℕ), LieModel X t n p f →
    OpenRankOneCase t n p f → CFSG.Open.pRank 3 (⊤ : Subgroup X) ≠ 1

theorem eq_three_of_three_dvd_pow {p f : ℕ} (hp : p.Prime) (h : 3 ∣ p ^ f) : p = 3 :=
  ((Nat.prime_dvd_prime_iff_eq Nat.prime_three hp).1 (Nat.prime_three.dvd_of_dvd_pow h)).symm

theorem lieRankOneClassification_of_open (hO : LieRankOneOpen) : LieRankOneClassification := by
  intro X _ _ t n p f hm h1
  by_cases hopen : OpenRankOneCase t n p f
  · exact absurd h1 (hO X t n p f hm hopen)
  by_cases hex : t ≠ .PSL ∧ t ≠ .PSU ∧ t ≠ .PSp ∧ t ≠ .POmegaOdd ∧ t ≠ .POmegaPlus ∧
      t ≠ .POmegaMinus
  · exact absurd (Or.inr (Or.inr (Or.inr hex))) hopen
  have hcl : t = .PSL ∨ t = .PSU ∨ t = .PSp ∨ t = .POmegaOdd ∨ t = .POmegaPlus ∨
      t = .POmegaMinus := by
    by_contra hc
    push Not at hc
    exact hex hc
  have hC : StatedClassicalModel X t n p f := statedClassicalModel_of_lieModel hcl hm
  have hp : p.Prime := hC.1.1
  have hp1f : 1 ≤ p ^ f := Nat.one_le_pow _ _ hp.pos
  have hp3 : p ≠ 3 := fun h => by
    subst h
    have := two_le_pRank_of_char_three hC
    omega
  have hno3 : ¬ 3 ∣ p ^ f := fun h => hp3 (eq_three_of_three_dvd_pow hp h)
  rcases hcl with rfl | rfl | rfl | rfl | rfl | rfl
  ·
    obtain ⟨⟨-, -, hn2, -, -⟩, K, _, _, hK, ⟨e⟩⟩ := id hC
    rcases (show n = 2 ∨ n = 3 ∨ 4 ≤ n by omega) with rfl | rfl | hn4
    · exact Or.inl ⟨rfl, rfl⟩
    · refine Or.inr (Or.inl ⟨rfl, rfl, ?_⟩)
      by_contra hne
      have h1' : p ^ f % 3 = 1 := by omega
      have := two_le_pRank_three_psl_three_of_dvd hC (by omega)
      omega
    · exfalso
      have := QuasithinUnique.Vol2Native.EvenWit.two_le_pRank_three_psl (K := K) hn4
      rw [← pRank_top_eq_of_mulEquiv (by norm_num) e] at this
      omega
  ·
    have hn3 : 3 ≤ n := hC.1.2.2.1
    rcases (show n = 3 ∨ 4 ≤ n by omega) with rfl | hn4
    · refine Or.inr (Or.inr ⟨rfl, rfl, ?_⟩)
      by_contra hne
      have h2 : p ^ f % 3 = 2 := by omega
      have := two_le_pRank_three_psu_three_of_dvd hC (by omega)
      omega
    · by_cases h2 : p ^ f % 3 = 2
      · exfalso
        have := two_le_pRank_three_psu_four_of_dvd hn4 hC (by omega)
        omega
      · exact absurd (Or.inl ⟨rfl, hn4, hp3, by omega⟩) hopen
  ·
    exfalso
    obtain ⟨⟨-, -, hn2, -⟩, K, _, _, hK, ⟨e⟩⟩ := hC
    have := QuasithinUnique.Vol2Native.EvenWit.two_le_pRank_three_psp (K := K) hn2
    rw [← pRank_top_eq_of_mulEquiv (by norm_num) e] at this
    omega
  · exact absurd (Or.inr (Or.inl ⟨rfl, hp3⟩)) hopen
  · by_cases hp2 : p = 2
    · exfalso
      subst hp2
      obtain ⟨⟨-, -, hn4⟩, K, _, _, hK, ⟨e⟩⟩ := hC
      have : CharP K 2 := ClassicalOdd.charP_of_card hK
      have := omegaPlus_three_le_pRank_three (K := K) hn4
      rw [← pRank_top_eq_of_mulEquiv (by norm_num) e] at this
      omega
    · exact absurd (Or.inr (Or.inr (Or.inl ⟨Or.inl rfl, hp2, hp3⟩))) hopen
  · by_cases hp2 : p = 2
    · exfalso
      subst hp2
      obtain ⟨⟨-, -, hn4⟩, K, _, _, hK, b, c, -, ⟨e⟩⟩ := hC
      have : CharP K 2 := ClassicalOdd.charP_of_card hK
      have := omegaMinus_three_le_pRank_three (K := K) hn4 b c
      rw [← pRank_top_eq_of_mulEquiv (by norm_num) e] at this
      omega
    · exact absurd (Or.inr (Or.inr (Or.inl ⟨Or.inr rfl, hp2, hp3⟩))) hopen

theorem tfaaModels_of_open (hO : LieRankOneOpen) : TFAaModels :=
  tfaaModels_of_classification (lieRankOneClassification_of_open hO)

end CFSG.HardMathSupport.Timmesfeld.FieldBonus
