module

public import CFSG.LocalAnalysis.SectionRank.QTK.CoverBOdd
import CFSG.LocalAnalysis.SectionRank.QTK.CoverBMain

public section

namespace CFSG.SectionRank.QTK.CentreFact

open CFSG.Open CFSG.Blueprint CFSG.SectionRank.QTK.CoverB

@[expose] def TableRestricted (S : Type) [Group S] (r : ℕ) : Prop :=
  ∀ (t : StatedLieTag) (n p f : ℕ), LieModel S t n p f → TablePrime t n p f r

theorem TableRestricted.classical {S : Type} [Group S] {r : ℕ} (hT : TableRestricted S r)
    {t : StatedLieTag} {n p f : ℕ} (hm : StatedClassicalModel S t n p f) :
    TablePrime t n p f r :=
  hT t n p f (lieModel_of_statedClassicalModel hm)

theorem TableRestricted.chevalley {S : Type} [Group S] {r : ℕ} (hT : TableRestricted S r)
    {t : StatedLieTag} {p f : ℕ} (ht : t ∈ chevalleyExceptionalTags)
    (hm : ChevalleyExceptionalModel S t p f) : TablePrime t 0 p f r :=
  hT t 0 p f (Or.inr (Or.inl ⟨rfl, ht, hm⟩))

theorem TableRestricted.reeTits {S : Type} [Group S] {r : ℕ} (hT : TableRestricted S r)
    {t : StatedLieTag} {p f : ℕ} (ht : t ∈ reeTitsTags) (hm : ReeTitsModel S t p f) :
    TablePrime t 0 p f r :=
  hT t 0 p f (Or.inr (Or.inr (Or.inl ⟨rfl, ht, hm⟩)))

theorem TableRestricted.suzuki {S : Type} [Group S] {r : ℕ} (hT : TableRestricted S r)
    {p f : ℕ} (hm : SuzukiModel S p f) : TablePrime .twistedB2 0 p f r :=
  hT .twistedB2 0 p f (Or.inr (Or.inr (Or.inr ⟨rfl, rfl, hm⟩)))

section Tags

variable {n p f r : ℕ}

theorem tablePrime_psl_iff :
    TablePrime .PSL n p f r ↔ (r ∣ n ∧ r ∣ p ^ f - 1) ∨ (r = 3 ∧ n = 2 ∧ p = 3 ∧ f = 2) := by
  simp [TablePrime]

theorem tablePrime_psu_iff :
    TablePrime .PSU n p f r ↔ (r ∣ n ∧ r ∣ p ^ f + 1) ∨ (r = 3 ∧ n = 4 ∧ p = 3 ∧ f = 1) := by
  simp [TablePrime]

theorem tablePrime_g2_iff : TablePrime .G2 n p f r ↔ r = 3 ∧ n = 0 ∧ p = 3 ∧ f = 1 := by
  simp [TablePrime]

theorem not_tablePrime_psp : ¬ TablePrime .PSp n p f r := by
  simp [TablePrime]

theorem not_tablePrime_trialityD4 : ¬ TablePrime .trialityD4 n p f r := by
  simp [TablePrime]

theorem not_tablePrime_twistedF4 : ¬ TablePrime .twistedF4 n p f r := by
  simp [TablePrime]

theorem not_tablePrime_twistedB2 : ¬ TablePrime .twistedB2 n p f r := by
  simp [TablePrime]

theorem not_tablePrime_tits : ¬ TablePrime .Tits n p f r := by
  simp [TablePrime]

end Tags

section List

variable {p f r : ℕ}

theorem tablePrime_psl_two (hr : r.Prime) (hr2 : r ≠ 2) (h : TablePrime .PSL 2 p f r) :
    r = 3 ∧ p = 3 ∧ f = 2 := by
  rcases tablePrime_psl_iff.1 h with ⟨h2, -⟩ | ⟨h3, -, hp, hf⟩
  · exact absurd ((Nat.prime_dvd_prime_iff_eq hr Nat.prime_two).1 h2) hr2
  · exact ⟨h3, hp, hf⟩

theorem tablePrime_psl_three (h : TablePrime .PSL 3 p f r) : r ∣ 3 ∧ r ∣ p ^ f - 1 := by
  rcases tablePrime_psl_iff.1 h with h | ⟨-, h2, -⟩
  · exact h
  · omega

theorem tablePrime_psu_three (h : TablePrime .PSU 3 p f r) : r ∣ 3 ∧ r ∣ p ^ f + 1 := by
  rcases tablePrime_psu_iff.1 h with h | ⟨-, h4, -⟩
  · exact h
  · omega

theorem not_tablePrime_psl_four (hr : r.Prime) (hr2 : r ≠ 2) : ¬ TablePrime .PSL 4 p f r := by
  intro h
  rcases tablePrime_psl_iff.1 h with ⟨h4, -⟩ | ⟨-, h2, -⟩
  · exact not_dvd_four_of_odd_prime hr hr2 h4
  · omega

theorem tablePrime_psu_four (hr : r.Prime) (hr2 : r ≠ 2) (h : TablePrime .PSU 4 p f r) :
    r = 3 ∧ p = 3 ∧ f = 1 := by
  rcases tablePrime_psu_iff.1 h with ⟨h4, -⟩ | ⟨h3, -, hp, hf⟩
  · exact absurd h4 (not_dvd_four_of_odd_prime hr hr2)
  · exact ⟨h3, hp, hf⟩

theorem tablePrime_g2 (h : TablePrime .G2 0 p f r) : r = 3 ∧ p = 3 ∧ f = 1 := by
  obtain ⟨h3, -, hp, hf⟩ := tablePrime_g2_iff.1 h
  exact ⟨h3, hp, hf⟩

theorem tablePrime_psu_five_two_two (hr : r.Prime) (h : TablePrime .PSU 5 2 2 r) : r = 5 := by
  rcases tablePrime_psu_iff.1 h with ⟨h5, -⟩ | ⟨-, h4, -⟩
  · exact (Nat.prime_dvd_prime_iff_eq hr Nat.prime_five).1 h5
  · omega

theorem not_tablePrime_psl_two_one {n : ℕ} (hr : r.Prime) : ¬ TablePrime .PSL n 2 1 r := by
  intro h
  rcases tablePrime_psl_iff.1 h with ⟨-, h1⟩ | ⟨-, -, hp, -⟩
  · exact hr.not_dvd_one (by simpa using h1)
  · omega

end List

end CFSG.SectionRank.QTK.CentreFact
