module

public import CFSG.LocalAnalysis.GLTheoremA.CatA.Y10R166Label
public import CFSG.LocalAnalysis.GLTheoremA.S11.Lemma116
public import CFSG.LocalAnalysis.GLTheoremA.CatA.Rk2Tab.TablesHolds

public section

namespace CFSG.LocalAnalysis.GLTheoremA.Y10F

open CFSG.Open CFSG.Yardstones.Md0ec50421ce4 CFSG.LocalAnalysis.GLTheoremA
  CFSG.LocalAnalysis.GLTheoremB

theorem dvd_two_pow_sub_one_or_eq_three_of_split16_of_untwisted {q : ℕ} {lab : GLALabel}
    (hs : GLASplit16 q lab) (hu : CFSG.Assembly.LargeEvenUntwisted lab.tag) :
    q ∣ 2 ^ lab.n - 1 ∨ lab.n = 1 ∧ q = 3 := by
  change CFSG.Assembly.LargeEvenSplit16 q lab at hs
  unfold CFSG.Assembly.LargeEvenSplit16 at hs
  rcases hs with ⟨-, h⟩ | ⟨hnu, -⟩ | ⟨ht, -⟩ | h
  · exact Or.inl h
  · exact absurd hu hnu
  · rcases ht with ht | ht | ht | ht
    · rw [ht] at hu
      simp [CFSG.Assembly.LargeEvenUntwisted] at hu
    · rw [ht] at hu
      simp [CFSG.Assembly.LargeEvenUntwisted] at hu
    · rw [ht] at hu
      simp [CFSG.Assembly.LargeEvenUntwisted] at hu
    · rw [ht] at hu
      simp [CFSG.Assembly.LargeEvenUntwisted] at hu
  · exact Or.inr h

theorem dvd_two_pow_add_one_of_split16_of_twA_or_twE6 {q : ℕ} {lab : GLALabel}
    (hs : GLASplit16 q lab) (ht : lab.tag = .twA ∨ lab.tag = .twE6) :
    q ∣ 2 ^ lab.n + 1 := by
  have hnu : ¬ CFSG.Assembly.LargeEvenUntwisted lab.tag := by
    rcases ht with ht | ht <;> rw [ht] <;>
      simp [CFSG.Assembly.LargeEvenUntwisted]
  change CFSG.Assembly.LargeEvenSplit16 q lab at hs
  unfold CFSG.Assembly.LargeEvenSplit16 at hs
  rcases hs with ⟨hu, -⟩ | ⟨-, -, -, h⟩ | ⟨h, -⟩ | ⟨hn, hq⟩
  · exact absurd hu hnu
  · exact h
  · rcases ht with ht | ht
    · rw [ht] at h
      rcases h with h | h | h | h <;> exact absurd h (by decide)
    · rw [ht] at h
      rcases h with h | h | h | h <;> exact absurd h (by decide)
  · rw [hn, hq]
    norm_num

theorem dvd_two_pow_sub_one_or_add_one_of_split16_of_twD {q : ℕ} {lab : GLALabel}
    (hs : GLASplit16 q lab) (ht : lab.tag = .twD) :
    q ∣ 2 ^ lab.n - 1 ∨ q ∣ 2 ^ lab.n + 1 := by
  change CFSG.Assembly.LargeEvenSplit16 q lab at hs
  unfold CFSG.Assembly.LargeEvenSplit16 at hs
  rcases hs with ⟨hu, -⟩ | ⟨-, -, -, h⟩ | ⟨-, h⟩ | ⟨hn, hq⟩
  · rw [ht] at hu
    simp [CFSG.Assembly.LargeEvenUntwisted] at hu
  · exact Or.inr h
  · exact Or.inl h
  · rw [hn, hq]
    norm_num

section Certificate

theorem split16_of_hasLabel_of_eq_or_BC {K : Type} [Group K] [Finite K] {q : ℕ}
    (he : 4 ≤ evenRank K) {lab₁ lab₂ : GLALabel}
    (h₁ : HasLabel K (fun l : GLALabel => l = lab₁))
    (h₂ : HasLabel K (fun l : GLALabel => l = lab₂))
    (hs : GLASplit16 q lab₁) : GLASplit16 q lab₂ := by
  rcases label_eq_or_BC he h₁ h₂ with rfl | ⟨ht₁, ht₂, hr, hn⟩
  · exact hs
  · obtain ⟨t₁, r₁, n₁⟩ := lab₁
    obtain ⟨t₂, r₂, n₂⟩ := lab₂
    simp only at ht₁ ht₂ hr hn
    subst hr
    subst hn
    rcases ht₁ with rfl | rfl <;> rcases ht₂ with rfl | rfl
    · exact hs
    · exact (CFSG.LocalAnalysis.GLTheoremA.S11.split16_swap q r₁ n₁).1 hs
    · exact (CFSG.LocalAnalysis.GLTheoremA.S11.split16_swap q r₁ n₁).2 hs
    · exact hs

theorem dvd_two_pow_sub_one_or_eq_three_of_hasLabel_of_exists_split16 {K : Type} [Group K]
    [Finite K] {q : ℕ} {lab : GLALabel} (he : 4 ≤ evenRank K)
    (h : HasLabel K (fun l : GLALabel => l = lab))
    (hs : ∃ lab' : GLALabel, HasLabel K (fun l : GLALabel => l = lab') ∧ GLASplit16 q lab')
    (hu : CFSG.Assembly.LargeEvenUntwisted lab.tag) :
    q ∣ 2 ^ lab.n - 1 ∨ lab.n = 1 ∧ q = 3 := by
  obtain ⟨lab', h', hs'⟩ := hs
  exact dvd_two_pow_sub_one_or_eq_three_of_split16_of_untwisted
    (split16_of_hasLabel_of_eq_or_BC he h' h hs') hu

theorem dvd_two_pow_add_one_of_hasLabel_of_exists_split16 {K : Type} [Group K] [Finite K]
    {q : ℕ} {lab : GLALabel} (he : 4 ≤ evenRank K)
    (h : HasLabel K (fun l : GLALabel => l = lab))
    (hs : ∃ lab' : GLALabel, HasLabel K (fun l : GLALabel => l = lab') ∧ GLASplit16 q lab')
    (ht : lab.tag = .twA ∨ lab.tag = .twE6) : q ∣ 2 ^ lab.n + 1 := by
  obtain ⟨lab', h', hs'⟩ := hs
  exact dvd_two_pow_add_one_of_split16_of_twA_or_twE6
    (split16_of_hasLabel_of_eq_or_BC he h' h hs') ht

theorem dvd_two_pow_sub_one_or_add_one_of_hasLabel_of_exists_split16 {K : Type} [Group K]
    [Finite K] {q : ℕ} {lab : GLALabel} (he : 4 ≤ evenRank K)
    (h : HasLabel K (fun l : GLALabel => l = lab))
    (hs : ∃ lab' : GLALabel, HasLabel K (fun l : GLALabel => l = lab') ∧ GLASplit16 q lab')
    (ht : lab.tag = .twD) : q ∣ 2 ^ lab.n - 1 ∨ q ∣ 2 ^ lab.n + 1 := by
  obtain ⟨lab', h', hs'⟩ := hs
  exact dvd_two_pow_sub_one_or_add_one_of_split16_of_twD
    (split16_of_hasLabel_of_eq_or_BC he h' h hs') ht

theorem rk2_split16_of_tables_holds {K : Type} [Group K] [Finite K] {q : ℕ} (hq : q.Prime)
    (hq2 : q ≠ 2) (hK2 : HasLabel K (fun _ => True)) (h3 : 3 ≤ GLATwoLocalRank q K)
    (heq : GLATwoLocalRank q K = evenRank K) :
    ∃ lab : GLALabel, HasLabel K (fun l : GLALabel => l = lab) ∧ GLASplit16 q lab :=
  rk2_split16_of_tables rk2KRank rk2Lower_holds rk2Upper_holds hq hq2 hK2 h3 heq

end Certificate

end CFSG.LocalAnalysis.GLTheoremA.Y10F
