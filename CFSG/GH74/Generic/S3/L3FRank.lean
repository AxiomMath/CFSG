module

public import CFSG.GH74.Generic.S3.L3FRankNum
public import CFSG.GH74.Generic.S3.L3FRankGen4
public import CFSG.GH74.Generic.S3.L3FRankGlue
public import CFSG.GH74.Generic.S3.L3FRankArith

public section

namespace CFSG.GH74.Generic.S3

open CFSG CFSG.GH74 CFSG.GH74.Generic CFSG.Blueprint CFSG.Assembly.LowTwoRank CFSG.GH74.Generic.S3.L3Ord
open CFSG.Open (ordA ordTwistedA ordBC ordG2 ordTrialityD4 ordRee ordSuzuki)

theorem le_six_pow_four {q : ℕ} (hq : 5 ≤ q) : 3750 ≤ q ^ 4 * 6 := by
  have : 5 ^ 4 ≤ q ^ 4 := Nat.pow_le_pow_left hq 4
  omega

theorem lieModel_n_zero {X : Type} [Group X] {t : StatedLieTag} {n p f : ℕ}
    (ht : t ∉ classicalTags) (h : LieModel X t n p f) : n = 0 := by
  rcases h with ⟨h1, -⟩ | ⟨hn, -, -⟩ | ⟨hn, -, -⟩ | ⟨hn, -, -⟩
  · exact absurd h1 ht
  all_goals exact hn

theorem lieModel_prime {X : Type} [Group X] {t : StatedLieTag} {n p f : ℕ}
    (h : LieModel X t n p f) : p.Prime ∧ 1 ≤ f := by
  rcases h with ⟨-, hadm, -⟩ | ⟨-, -, hadm, -⟩ | ⟨-, -, hadm, -⟩ | ⟨-, -, hp, a, ha, -, -, -, hf, -⟩
  · exact ⟨hadm.1, hadm.2.1⟩
  · exact ⟨hadm.1, hadm.2.1⟩
  · exact ⟨hadm.1, hadm.2.1⟩
  · exact ⟨hp ▸ Nat.prime_two, by omega⟩


theorem fValue_le_of_model
    {X : Type} [Group X] [Finite X] {p f : ℕ} (hp : p.Prime) (hp2 : p ≠ 2) (hq : 5 ≤ p ^ f)
    (hN : Nat.card X = ordA 2 (p ^ f) ∨ Nat.card X = ordTwistedA 2 (p ^ f)) (hX : Gen4 X)
    {t' : StatedLieTag} {n' p' f' : ℕ} (h' : LieModel X t' n' p' f') :
    FValue t' n' p' f' ≤ (p ^ f) ^ 4 * 6 := by
  have hf : 1 ≤ f := by
    rcases Nat.eq_zero_or_pos f with h | h
    · subst h; simp at hq
    · exact h
  obtain ⟨hp', hf'⟩ := lieModel_prime h'
  have h3N := three_mul_ge (q := p ^ f) (by omega) hN
  have h124 := le_of_ord hq hN
  have hkey : ∀ {k : ℕ}, (p' ^ f') ^ k ∣ Nat.card X → (p' ^ f') ^ k ≤ (p ^ f) ^ 3 :=
    fun hd => qpow_le_a2 hp hp2 hf hq hN hp' hd
  have hgen := gen4Model_of_lieModel hX h'
  cases t' with
  | PSL =>
    obtain ⟨-, -, hn2, -, -⟩ := (stated_of_lieModel_PSL h').1
    exact bound_PSL hq hp' hf' hn2 hgen (card_of_lieModel_PSL (by omega) h') hkey h3N
  | PSU =>
    obtain ⟨-, -, hn3, -⟩ := (stated_of_lieModel_PSU h').1
    rcases hgen with ⟨hn5, hp2'⟩ | ⟨hp2', hle⟩
    · exact bound_PSU_odd hq hp' hf' hn3 hn5 (card_of_lieModel_PSU (by omega) hp2' h') hkey h3N
    · subst hp2'
      exact (bound_PSU_even hn3 hf' hle).trans (le_six_pow_four hq)
  | PSp =>
    obtain ⟨-, -, hn2, -⟩ := (stated_of_lieModel_PSp h').1
    rcases hgen with ⟨hn, hp2'⟩ | ⟨hp2', hle⟩
    · exact bound_PSp_odd hq hp' hf' hn (card_of_lieModel_PSp (by omega) hp2' h') hkey
    · subst hp2'
      exact (bound_PSp_even hn2 hf' hle).trans (le_six_pow_four hq)
  | POmegaOdd => exact False.elim hgen
  | POmegaPlus => exact False.elim hgen
  | POmegaMinus => exact False.elim hgen
  | G2 => exact bound_G2 hq (card_of_lieModel_G2 hgen h') hkey
  | F4 => exact False.elim hgen
  | E6 => exact False.elim hgen
  | E7 => exact False.elim hgen
  | E8 => exact False.elim hgen
  | twistedE6 => exact False.elim hgen
  | trialityD4 =>
    exact (bound_D4 hq hp' hf' (card_of_lieModel_trialityD4 hgen h') hkey h3N).elim
  | twistedB2 =>
    obtain ⟨hp2', a, ha, hfa, hcard⟩ := card_of_suzukiModel (suzuki_clause h')
    have hf3 : f' = 3 := by
      have : f' ≤ 4 := hgen
      omega
    subst hp2' hf3
    exact (bound_Sz (by simpa using hcard) h124).elim
  | twistedG2 =>
    have hn0 : n' = 0 := lieModel_n_zero (by decide) h'
    subst hn0
    obtain ⟨-, -, -, hp3, -, -⟩ := (reeTits_clause (by decide) h').1
    subst hp3
    obtain ⟨k, hk, hcard⟩ := card_of_lieModel_twistedG2 h'
    have hQ : 2 ≤ 3 ^ (2 * k + 1) := by
      have : 1 < 3 ^ (2 * k + 1) := Nat.one_lt_pow (by omega) (by norm_num)
      omega
    exact (bound_Ree hq hQ hcard (fun hd => qpow_le_a2 hp hp2 hf hq hN Nat.prime_three hd) h3N).elim
  | twistedF4 => exact False.elim hgen
  | Tits => exact False.elim hgen

theorem l3_fRank
    : L3FRank :=
  l3_fRank_of_bound fun X _ t p f ht hp hp2 hq hG hM t' n' p' f' h' => by
    have hf : 1 ≤ f := by
      rcases Nat.eq_zero_or_pos f with h | h
      · subst h; simp at hq
      · exact h
    obtain ⟨hpos, -⟩ := l3_card_facts ht hp hp2 hf hq hM
    have : Finite X := Nat.finite_of_card_ne_zero hpos.ne'
    have hN : Nat.card X = ordA 2 (p ^ f) ∨ Nat.card X = ordTwistedA 2 (p ^ f) := by
      rcases ht with rfl | rfl
      · exact Or.inl (card_of_lieModel_PSL (by norm_num) hM)
      · exact Or.inr (card_of_lieModel_PSU (by norm_num) hp2 hM)
    exact fValue_le_of_model hp hp2 hq hN hG.1 h'

end CFSG.GH74.Generic.S3
