module

public import CFSG.CharacterTheory.Wreathed.FourPointGaussianColumnsSupport

public noncomputable section

namespace CFSG.Wreathed.FourPointGaussianColumns

open scoped BigOperators Classical

variable {ι : Type*}

theorem sum_three {M : Type*} [AddCommMonoid M] {a b c : ι} (hab : a ≠ b) (hac : a ≠ c)
    (hbc : b ≠ c) (f : ι → M) : ∑ x ∈ ({a, b, c} : Finset ι), f x = f a + f b + f c := by
  rw [Finset.sum_insert (by simp [hab, hac]), Finset.sum_insert (by simp [hbc]),
    Finset.sum_singleton, add_assoc]

theorem sum_eq_two_mul_sum_pos_add_sum_zero (B : Finset ι) (σ : ι → ι)
    (hσB : ∀ χ ∈ B, σ χ ∈ B) (hσσ : ∀ χ, σ (σ χ) = χ) (f : ι → ℤ)
    (hf : ∀ χ ∈ B, f (σ χ) = -f χ) (g : ι → ℤ) (hg : ∀ χ ∈ B, g (σ χ) = g χ) :
    ∑ χ ∈ B, g χ = 2 * ∑ χ ∈ B.filter (fun χ => 0 < f χ), g χ +
      ∑ χ ∈ B.filter (fun χ => f χ = 0), g χ := by
  rw [sum_eq_sum_pos_add_sum_neg_add_sum_zero B f g,
    sum_filter_neg_eq_sum_filter_pos B σ hσB hσσ f hf g hg]
  ring

theorem eq_of_sq_sum_le {ι : Type*} (P : Finset ι) (k : ι → ℤ) {s m : ℤ} (hm : 0 < m)
    (hsum : ∑ χ ∈ P, k χ ^ 2 = s) (hs : s < (2 * m) ^ 2) (hpos : ∀ χ ∈ P, 0 < k χ)
    (hdvd : ∀ χ ∈ P, m ∣ k χ) : ∀ χ ∈ P, k χ = m := by
  intro χ hχ
  obtain ⟨c, hc⟩ := hdvd χ hχ
  have hle : k χ ^ 2 ≤ s := hsum ▸
    Finset.single_le_sum (f := fun χ' => k χ' ^ 2) (fun χ' _ => sq_nonneg (k χ')) hχ
  have hc1 : 0 < c := by
    by_contra h
    have : k χ ≤ 0 := by rw [hc]; nlinarith
    linarith [hpos χ hχ]
  have hc2 : c < 2 := by
    by_contra h
    have h2 : 2 * m ≤ k χ := by rw [hc]; nlinarith
    nlinarith
  have : c = 1 := by omega
  rw [hc, this, mul_one]

section Dichotomy

variable (B : Finset ι) (σ : ι → ι) (hσB : ∀ χ ∈ B, σ χ ∈ B) (hσσ : ∀ χ, σ (σ χ) = χ)
  (kT kU : ι → ℤ) (hT : ∀ χ ∈ B, kT (σ χ) = -kT χ) (hU : ∀ χ ∈ B, kU (σ χ) = -kU χ)

include hσB hσσ hU in
theorem dichotomy_positive_part (hUU : ∑ χ ∈ B, kU χ ^ 2 = 6) :
    (∀ χ ∈ B.filter (fun χ => 0 < kU χ), kU χ = 1) ∧
    (B.filter (fun χ => 0 < kU χ)).card = 3 ∧
    (∀ χ ∈ B, kU χ ≠ 0 → χ ∈ B.filter (fun χ => 0 < kU χ) ∨
      σ χ ∈ B.filter (fun χ => 0 < kU χ)) := by
  have hsum : ∑ χ ∈ B.filter (fun χ => 0 < kU χ), kU χ ^ 2 = 3 := by
    have h := sum_eq_two_mul_sum_pos_add_sum_zero B σ hσB hσσ kU hU (fun χ => kU χ ^ 2)
      (fun χ hχ => by rw [hU χ hχ]; ring)
    have h0 : ∑ χ ∈ B.filter (fun χ => kU χ = 0), kU χ ^ 2 = 0 :=
      Finset.sum_eq_zero fun χ hχ => by
        rw [(Finset.mem_filter.mp hχ).2]
        norm_num
    omega
  have hP1 : ∀ χ ∈ B.filter (fun χ => 0 < kU χ), kU χ = 1 :=
    eq_of_sq_sum_le _ kU (by norm_num) hsum (by norm_num)
      (fun χ hχ => (Finset.mem_filter.mp hχ).2) (fun χ _ => one_dvd _)
  refine ⟨hP1, ?_, ?_⟩
  · have h : ∑ χ ∈ B.filter (fun χ => 0 < kU χ), kU χ ^ 2 =
        ∑ χ ∈ B.filter (fun χ => 0 < kU χ), (1 : ℤ) :=
      Finset.sum_congr rfl fun χ hχ => by rw [hP1 χ hχ]; norm_num
    rw [hsum, Finset.sum_const, nsmul_eq_mul, mul_one] at h
    exact_mod_cast h.symm
  · intro χ hχ hne
    rcases lt_or_gt_of_ne hne with hneg | hpos
    · right
      exact Finset.mem_filter.mpr ⟨hσB χ hχ, by rw [hU χ hχ]; omega⟩
    · left
      exact Finset.mem_filter.mpr ⟨hχ, hpos⟩

include hσB hσσ hT hU in
theorem dichotomy_sums (hTT : ∑ χ ∈ B, kT χ ^ 2 = 48) (hTU : ∑ χ ∈ B, kT χ * kU χ = 0)
    (hP1 : ∀ χ ∈ B.filter (fun χ => 0 < kU χ), kU χ = 1) :
    ∑ χ ∈ B.filter (fun χ => 0 < kU χ), kT χ = 0 ∧
    2 * ∑ χ ∈ B.filter (fun χ => 0 < kU χ), kT χ ^ 2 +
      ∑ χ ∈ B.filter (fun χ => kU χ = 0), kT χ ^ 2 = 48 := by
  constructor
  · have h := sum_eq_two_mul_sum_pos_add_sum_zero B σ hσB hσσ kU hU (fun χ => kT χ * kU χ)
      (fun χ hχ => by rw [hT χ hχ, hU χ hχ]; ring)
    have h0 : ∑ χ ∈ B.filter (fun χ => kU χ = 0), kT χ * kU χ = 0 :=
      Finset.sum_eq_zero fun χ hχ => by rw [(Finset.mem_filter.mp hχ).2, mul_zero]
    have h1 : ∑ χ ∈ B.filter (fun χ => 0 < kU χ), kT χ * kU χ =
        ∑ χ ∈ B.filter (fun χ => 0 < kU χ), kT χ :=
      Finset.sum_congr rfl fun χ hχ => by rw [hP1 χ hχ, mul_one]
    omega
  · have h := sum_eq_two_mul_sum_pos_add_sum_zero B σ hσB hσσ kU hU (fun χ => kT χ ^ 2)
      (fun χ hχ => by rw [hT χ hχ]; ring)
    omega

theorem dichotomy_values (P : Finset ι) (hP1 : ∀ χ ∈ P, kU χ = 1)
    (hmod : ∀ χ ∈ P, 3 ∣ kT χ - kU χ) (hle : ∑ χ ∈ P, kT χ ^ 2 ≤ 24) :
    ∀ χ ∈ P, kT χ = -2 ∨ kT χ = 1 ∨ kT χ = 4 := by
  intro χ hχ
  obtain ⟨c, hc⟩ := hmod χ hχ
  rw [hP1 χ hχ] at hc
  have hsq : kT χ ^ 2 ≤ 24 := le_trans
    (Finset.single_le_sum (f := fun χ' => kT χ' ^ 2) (fun χ' _ => sq_nonneg (kT χ')) hχ) hle
  have hlo : -4 ≤ kT χ := by nlinarith
  have hhi : kT χ ≤ 4 := by nlinarith
  omega

include hσB hσσ hT hU in
theorem dichotomy_two_further_pairs (hmod : ∀ χ ∈ B, 3 ∣ kT χ - kU χ)
    (h36 : ∑ χ ∈ B.filter (fun χ => kU χ = 0), kT χ ^ 2 = 36) :
    ∃ ψ₁ ∈ B, ∃ ψ₂ ∈ B, ψ₁ ≠ ψ₂ ∧ ψ₁ ≠ σ ψ₂ ∧ kT ψ₁ = 3 ∧ kT ψ₂ = 3 ∧ kU ψ₁ = 0 ∧
      kU ψ₂ = 0 ∧ ∀ χ ∈ B, kT χ ≠ 0 → kU χ ≠ 0 ∨
        χ = ψ₁ ∨ χ = σ ψ₁ ∨ χ = ψ₂ ∨ χ = σ ψ₂ := by
  set Q := B.filter (fun χ => kU χ = 0) with hQdef
  have hQB : ∀ χ ∈ Q, χ ∈ B := fun χ hχ => (Finset.mem_filter.mp hχ).1
  have hσQ : ∀ χ ∈ Q, σ χ ∈ Q := fun χ hχ => Finset.mem_filter.mpr
    ⟨hσB χ (hQB χ hχ), by rw [hU χ (hQB χ hχ), (Finset.mem_filter.mp hχ).2, neg_zero]⟩
  have hsum : ∑ χ ∈ Q.filter (fun χ => 0 < kT χ), kT χ ^ 2 = 18 := by
    have h := sum_eq_two_mul_sum_pos_add_sum_zero Q σ hσQ hσσ kT
      (fun χ hχ => hT χ (hQB χ hχ)) (fun χ => kT χ ^ 2)
      (fun χ hχ => by rw [hT χ (hQB χ hχ)]; ring)
    have h0 : ∑ χ ∈ Q.filter (fun χ => kT χ = 0), kT χ ^ 2 = 0 :=
      Finset.sum_eq_zero fun χ hχ => by
        rw [(Finset.mem_filter.mp hχ).2]
        norm_num
    omega
  set Q' := Q.filter (fun χ => 0 < kT χ) with hQ'def
  have hQ'Q : ∀ χ ∈ Q', χ ∈ Q := fun χ hχ => (Finset.mem_filter.mp hχ).1
  have hQ'3 : ∀ χ ∈ Q', kT χ = 3 :=
    eq_of_sq_sum_le Q' kT (by norm_num) hsum (by norm_num)
      (fun χ hχ => (Finset.mem_filter.mp hχ).2) fun χ hχ => by
        have h := hmod χ (hQB χ (hQ'Q χ hχ))
        rwa [(Finset.mem_filter.mp (hQ'Q χ hχ)).2, sub_zero] at h
  have hQ'card : Q'.card = 2 := by
    have h : ∑ χ ∈ Q', kT χ ^ 2 = ∑ χ ∈ Q', (9 : ℤ) :=
      Finset.sum_congr rfl fun χ hχ => by rw [hQ'3 χ hχ]; norm_num
    rw [hsum, Finset.sum_const, nsmul_eq_mul] at h
    have h' : (Q'.card : ℤ) = 2 := by linarith
    exact_mod_cast h'
  obtain ⟨ψ₁, ψ₂, hψ12, hQ'eq⟩ := Finset.card_eq_two.mp hQ'card
  have hψ₁ : ψ₁ ∈ Q' := by rw [hQ'eq]; simp
  have hψ₂ : ψ₂ ∈ Q' := by rw [hQ'eq]; simp
  have hψ₁B := hQB ψ₁ (hQ'Q ψ₁ hψ₁)
  have hψ₂B := hQB ψ₂ (hQ'Q ψ₂ hψ₂)
  refine ⟨ψ₁, hψ₁B, ψ₂, hψ₂B, hψ12, ?_, hQ'3 ψ₁ hψ₁, hQ'3 ψ₂ hψ₂,
    (Finset.mem_filter.mp (hQ'Q ψ₁ hψ₁)).2, (Finset.mem_filter.mp (hQ'Q ψ₂ hψ₂)).2, ?_⟩
  · intro h
    have h1 := hQ'3 ψ₁ hψ₁
    rw [h, hT ψ₂ hψ₂B, hQ'3 ψ₂ hψ₂] at h1
    norm_num at h1
  · intro χ hχ hne
    by_cases hkU : kU χ = 0
    · right
      have hχQ : χ ∈ Q := Finset.mem_filter.mpr ⟨hχ, hkU⟩
      rcases lt_or_gt_of_ne hne with hneg | hpos
      · have hσχ : σ χ ∈ Q' := Finset.mem_filter.mpr ⟨hσQ χ hχQ, by rw [hT χ hχ]; omega⟩
        rw [hQ'eq, Finset.mem_insert, Finset.mem_singleton] at hσχ
        rcases hσχ with h | h
        · exact Or.inr (Or.inl (by rw [← h, hσσ]))
        · exact Or.inr (Or.inr (Or.inr (by rw [← h, hσσ])))
      · have hχ' : χ ∈ Q' := Finset.mem_filter.mpr ⟨hχQ, hpos⟩
        rw [hQ'eq, Finset.mem_insert, Finset.mem_singleton] at hχ'
        rcases hχ' with h | h
        · exact Or.inl h
        · exact Or.inr (Or.inr (Or.inl h))
    · exact Or.inl hkU

@[expose] def DichotomyConclusion (c₁ c₂ c₃ : ι) : Prop :=
  c₁ ∈ B ∧ c₂ ∈ B ∧ c₃ ∈ B ∧ c₁ ≠ c₂ ∧ c₁ ≠ c₃ ∧ c₂ ≠ c₃ ∧
    kU c₁ = 1 ∧ kU c₂ = 1 ∧ kU c₃ = 1 ∧
    (∀ χ ∈ B, kU χ = 1 ↔ χ = c₁ ∨ χ = c₂ ∨ χ = c₃) ∧
    (∀ χ ∈ B, kU χ ≠ 0 →
      χ = c₁ ∨ χ = σ c₁ ∨ χ = c₂ ∨ χ = σ c₂ ∨ χ = c₃ ∨ χ = σ c₃) ∧
    ((kT c₁ = -2 ∧ kT c₂ = 1 ∧ kT c₃ = 1 ∧
      ∃ ψ₁ ∈ B, ∃ ψ₂ ∈ B, ψ₁ ≠ ψ₂ ∧ ψ₁ ≠ σ ψ₂ ∧ kT ψ₁ = 3 ∧ kT ψ₂ = 3 ∧ kU ψ₁ = 0 ∧
        kU ψ₂ = 0 ∧ ∀ χ ∈ B, kT χ ≠ 0 →
          χ = c₁ ∨ χ = σ c₁ ∨ χ = c₂ ∨ χ = σ c₂ ∨ χ = c₃ ∨ χ = σ c₃ ∨
            χ = ψ₁ ∨ χ = σ ψ₁ ∨ χ = ψ₂ ∨ χ = σ ψ₂) ∨
     (kT c₁ = 4 ∧ kT c₂ = -2 ∧ kT c₃ = -2 ∧ ∀ χ ∈ B, kT χ ≠ 0 →
        χ = c₁ ∨ χ = σ c₁ ∨ χ = c₂ ∨ χ = σ c₂ ∨ χ = c₃ ∨ χ = σ c₃))

include hσB hσσ hT hU in
theorem dichotomy_assemble (hmod : ∀ χ ∈ B, 3 ∣ kT χ - kU χ)
    (hP1 : ∀ χ ∈ B.filter (fun χ => 0 < kU χ), kU χ = 1)
    (hPσ : ∀ χ ∈ B, kU χ ≠ 0 → χ ∈ B.filter (fun χ => 0 < kU χ) ∨
      σ χ ∈ B.filter (fun χ => 0 < kU χ))
    (hTT' : 2 * ∑ χ ∈ B.filter (fun χ => 0 < kU χ), kT χ ^ 2 +
      ∑ χ ∈ B.filter (fun χ => kU χ = 0), kT χ ^ 2 = 48)
    (c₁ c₂ c₃ : ι) (hc : ∀ χ, χ ∈ B.filter (fun χ => 0 < kU χ) ↔ χ = c₁ ∨ χ = c₂ ∨ χ = c₃)
    (h12 : c₁ ≠ c₂) (h13 : c₁ ≠ c₃) (h23 : c₂ ≠ c₃)
    (hcase : (kT c₁ = -2 ∧ kT c₂ = 1 ∧ kT c₃ = 1) ∨ (kT c₁ = 4 ∧ kT c₂ = -2 ∧ kT c₃ = -2)) :
    DichotomyConclusion B σ kT kU c₁ c₂ c₃ := by
  have hPc : B.filter (fun χ => 0 < kU χ) = {c₁, c₂, c₃} := Finset.ext fun χ => by
    rw [hc χ]
    simp
  have hmem : ∀ c, (c = c₁ ∨ c = c₂ ∨ c = c₃) → c ∈ B ∧ kU c = 1 := fun c h =>
    ⟨(Finset.mem_filter.mp ((hc c).mpr h)).1, hP1 c ((hc c).mpr h)⟩
  have hpairs : ∀ χ ∈ B, kU χ ≠ 0 →
      χ = c₁ ∨ χ = σ c₁ ∨ χ = c₂ ∨ χ = σ c₂ ∨ χ = c₃ ∨ χ = σ c₃ := by
    intro χ hχ hne
    rcases hPσ χ hχ hne with h | h
    · rcases (hc χ).mp h with h' | h' | h'
      · exact Or.inl h'
      · exact Or.inr (Or.inr (Or.inl h'))
      · exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h'))))
    · rcases (hc (σ χ)).mp h with h' | h' | h'
      · exact Or.inr (Or.inl (by rw [← h', hσσ]))
      · exact Or.inr (Or.inr (Or.inr (Or.inl (by rw [← h', hσσ]))))
      · exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (by rw [← h', hσσ])))))
  have hsq : ∑ χ ∈ B.filter (fun χ => 0 < kU χ), kT χ ^ 2 =
      kT c₁ ^ 2 + kT c₂ ^ 2 + kT c₃ ^ 2 := by
    rw [hPc, sum_three h12 h13 h23]
  refine ⟨(hmem c₁ (Or.inl rfl)).1, (hmem c₂ (Or.inr (Or.inl rfl))).1,
    (hmem c₃ (Or.inr (Or.inr rfl))).1, h12, h13, h23, (hmem c₁ (Or.inl rfl)).2,
    (hmem c₂ (Or.inr (Or.inl rfl))).2, (hmem c₃ (Or.inr (Or.inr rfl))).2,
    fun χ hχ => ?_, hpairs, ?_⟩
  · rw [← hc χ]
    constructor
    · intro h
      exact Finset.mem_filter.mpr ⟨hχ, by omega⟩
    · exact hP1 χ
  rcases hcase with ⟨e1, e2, e3⟩ | ⟨e1, e2, e3⟩
  · left
    rw [e1, e2, e3] at hsq
    obtain ⟨ψ₁, hψ₁, ψ₂, hψ₂, hψ12, hψσ, hT1, hT2, hU1, hU2, hrest⟩ :=
      dichotomy_two_further_pairs B σ hσB hσσ kT kU hT hU hmod (by omega)
    refine ⟨e1, e2, e3, ψ₁, hψ₁, ψ₂, hψ₂, hψ12, hψσ, hT1, hT2, hU1, hU2, fun χ hχ hne => ?_⟩
    rcases hrest χ hχ hne with h | h
    · rcases hpairs χ hχ h with h' | h' | h' | h' | h' | h'
      · exact Or.inl h'
      · exact Or.inr (Or.inl h')
      · exact Or.inr (Or.inr (Or.inl h'))
      · exact Or.inr (Or.inr (Or.inr (Or.inl h')))
      · exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h'))))
      · exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h')))))
    · exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr h)))))
  · right
    rw [e1, e2, e3] at hsq
    refine ⟨e1, e2, e3, fun χ hχ hne => hpairs χ hχ fun hkU => hne ?_⟩
    have hzero : ∑ χ ∈ B.filter (fun χ => kU χ = 0), kT χ ^ 2 = 0 := by omega
    have hχQ : χ ∈ B.filter (fun χ => kU χ = 0) := Finset.mem_filter.mpr ⟨hχ, hkU⟩
    have hle : kT χ ^ 2 ≤ 0 := hzero ▸
      Finset.single_le_sum (f := fun χ' => kT χ' ^ 2) (fun χ' _ => sq_nonneg (kT χ')) hχQ
    nlinarith [sq_nonneg (kT χ)]

include hσB hσσ hT hU in
theorem conjugate_pair_dichotomy (hUU : ∑ χ ∈ B, kU χ ^ 2 = 6) (hTT : ∑ χ ∈ B, kT χ ^ 2 = 48)
    (hTU : ∑ χ ∈ B, kT χ * kU χ = 0) (hmod : ∀ χ ∈ B, 3 ∣ kT χ - kU χ) :
    ∃ χ₁ χ₂ χ₃ : ι, DichotomyConclusion B σ kT kU χ₁ χ₂ χ₃ := by
  obtain ⟨hP1, hPcard, hPσ⟩ := dichotomy_positive_part B σ hσB hσσ kU hU hUU
  obtain ⟨hTU', hTT'⟩ := dichotomy_sums B σ hσB hσσ kT kU hT hU hTT hTU hP1
  have hQnn : 0 ≤ ∑ χ ∈ B.filter (fun χ => kU χ = 0), kT χ ^ 2 :=
    Finset.sum_nonneg fun χ _ => sq_nonneg _
  have hval := dichotomy_values kT kU _ hP1
    (fun χ hχ => hmod χ (Finset.mem_filter.mp hχ).1) (by omega)
  obtain ⟨χ₁, χ₂, χ₃, h12, h13, h23, hPeq⟩ := Finset.card_eq_three.mp hPcard
  have hmemP : ∀ χ, χ ∈ B.filter (fun χ => 0 < kU χ) ↔ χ = χ₁ ∨ χ = χ₂ ∨ χ = χ₃ :=
    fun χ => by
      rw [hPeq]
      simp
  have hv₁ := hval χ₁ ((hmemP χ₁).mpr (Or.inl rfl))
  have hv₂ := hval χ₂ ((hmemP χ₂).mpr (Or.inr (Or.inl rfl)))
  have hv₃ := hval χ₃ ((hmemP χ₃).mpr (Or.inr (Or.inr rfl)))
  have hsum3 : kT χ₁ + kT χ₂ + kT χ₃ = 0 := by
    rw [← sum_three h12 h13 h23, ← hPeq]
    exact hTU'
  have perm : ∀ p q r : Prop, (p ∨ q ∨ r ↔ r ∨ q ∨ p) := by
    intro p q r
    tauto
  have hA := dichotomy_assemble B σ hσB hσσ kT kU hT hU hmod hP1 hPσ hTT'
  clear hTT' hTU' hval hPσ hP1 hTT hTU hUU hQnn
  rcases hv₁ with e1 | e1 | e1 <;> rcases hv₂ with e2 | e2 | e2 <;>
    rcases hv₃ with e3 | e3 | e3
  all_goals try (exfalso; omega)
  · exact ⟨χ₃, χ₂, χ₁, hA χ₃ χ₂ χ₁ (fun χ => (hmemP χ).trans (perm _ _ _)) h23.symm
      h13.symm h12.symm (Or.inr ⟨e3, e2, e1⟩)⟩
  · exact ⟨χ₁, χ₂, χ₃, hA χ₁ χ₂ χ₃ hmemP h12 h13 h23 (Or.inl ⟨e1, e2, e3⟩)⟩
  · exact ⟨χ₂, χ₁, χ₃, hA χ₂ χ₁ χ₃ (fun χ => (hmemP χ).trans or_left_comm) h12.symm h23 h13
      (Or.inr ⟨e2, e1, e3⟩)⟩
  · exact ⟨χ₂, χ₁, χ₃, hA χ₂ χ₁ χ₃ (fun χ => (hmemP χ).trans or_left_comm) h12.symm h23 h13
      (Or.inl ⟨e2, e1, e3⟩)⟩
  · exact ⟨χ₃, χ₂, χ₁, hA χ₃ χ₂ χ₁ (fun χ => (hmemP χ).trans (perm _ _ _)) h23.symm
      h13.symm h12.symm (Or.inl ⟨e3, e2, e1⟩)⟩
  · exact ⟨χ₁, χ₂, χ₃, hA χ₁ χ₂ χ₃ hmemP h12 h13 h23 (Or.inr ⟨e1, e2, e3⟩)⟩

end Dichotomy

end CFSG.Wreathed.FourPointGaussianColumns
