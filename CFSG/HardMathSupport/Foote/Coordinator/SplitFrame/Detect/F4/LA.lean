module

public import CFSG.HardMathSupport.Foote.Coordinator.SplitFrame.Detect.F4.Leaf.LAWords

public noncomputable section

namespace CFSG.HardMathSupport.Foote.Coordinator.SplitFrame.DetectF4

open CFSG.Blueprint CFSG.Blueprint.Chevalley CFSG.LieType.Chevalley CFSG.SeitzReduction

variable {K : Type} [Field K]
  {a1 a2 : (Fin Tag.F4.rank → ℤ) → (Fin Tag.F4.rank → ℤ) → ℤ}

theorem two_term {A B t₀ : K} (ht0 : t₀ ≠ 0) (ht1 : t₀ ≠ 1)
    (h1 : 1 * A + 1 ^ 2 * B = 0) (h2 : t₀ * A + t₀ ^ 2 * B = 0) : A = 0 ∧ B = 0 := by
  have hB : B * (t₀ * (t₀ - 1)) = 0 := by linear_combination h2 - t₀ * h1
  have hB0 : B = 0 := by
    rcases mul_eq_zero.1 hB with h | h
    · exact h
    · exact absurd h (mul_ne_zero ht0 (sub_ne_zero.2 ht1))
  refine ⟨?_, hB0⟩
  rw [hB0] at h1
  linear_combination h1

theorem cast_ne_zero_of_abs_eq_one {z : ℤ} (h : |z| = 1) : (z : K) ≠ 0 := by
  rcases (abs_eq zero_le_one).1 h with rfl | rfl <;> simp

theorem cast_ne_zero_of_abs_eq_two {z : ℤ} (h : |z| = 2) (h2 : (2 : K) ≠ 0) : (z : K) ≠ 0 := by
  rcases (abs_eq (by norm_num : (0 : ℤ) ≤ 2)).1 h with rfl | rfl
  · simpa using h2
  · simpa using h2

theorem fixed_eq {γ : Fin Tag.F4.rank → ℤ} {c : (Fin Tag.F4.rank → ℤ) → K}
    (hfix : ∀ t : K, actFun a1 a2 γ t c = c) (ν : Fin Tag.F4.rank → ℤ) (t : K) :
    t * (a1 γ (ν - γ) : K) * c (ν - γ) + t ^ 2 * (a2 γ (ν - 2 • γ) : K) * c (ν - 2 • γ) = 0 := by
  have := congrFun (hfix t) ν
  simp only [actFun] at this
  linear_combination this

theorem coeff_vanish {γ : Fin Tag.F4.rank → ℤ} {c : (Fin Tag.F4.rank → ℤ) → K}
    (hK : ∃ t : K, t ≠ 0 ∧ t ≠ 1) (hfix : ∀ t : K, actFun a1 a2 γ t c = c)
    (ν : Fin Tag.F4.rank → ℤ) :
    (a1 γ ν : K) * c ν = 0 ∧ (a2 γ ν : K) * c ν = 0 := by
  obtain ⟨t₀, ht0, ht1⟩ := hK
  have e1 : ν + γ - 2 • γ = ν - γ := by rw [two_smul]; abel
  have e2 : ν + γ - γ = ν := by abel
  have e3 : ν + 2 • γ - γ = ν + γ := by rw [two_smul]; abel
  have e4 : ν + 2 • γ - 2 • γ = ν := by abel
  have h1a := fixed_eq hfix (ν + γ) 1
  have h1b := fixed_eq hfix (ν + γ) t₀
  rw [e1, e2] at h1a h1b
  have hA := two_term (A := (a1 γ ν : K) * c ν) (B := (a2 γ (ν - γ) : K) * c (ν - γ)) ht0 ht1
    (by linear_combination h1a) (by linear_combination h1b)
  have h2a := fixed_eq hfix (ν + 2 • γ) 1
  have h2b := fixed_eq hfix (ν + 2 • γ) t₀
  rw [e3, e4] at h2a h2b
  have hB := two_term (A := (a1 γ (ν + γ) : K) * c (ν + γ)) (B := (a2 γ ν : K) * c ν) ht0 ht1
    (by linear_combination h2a) (by linear_combination h2b)
  exact ⟨hA.1, hB.2⟩

theorem fixed_support_tops (hK : ∃ t : K, t ≠ 0 ∧ t ≠ 1) (h1 : Adm1 a1) (h2 : Adm2 a2)
    {c : (Fin Tag.F4.rank → ℤ) → K} (hsupp : ∀ ν, c ν ≠ 0 → ν ∈ mRoots)
    (hfix : ∀ γ ∈ s2pos, ∀ t : K, actFun a1 a2 γ t c = c) :
    ∀ ν, c ν ≠ 0 → ((2 : K) = 0 → ν ∈ topsTwo) ∧ ((2 : K) ≠ 0 → ν ∈ topsOdd) := by
  intro ν hν
  have hνM := hsupp ν hν
  have hνD : ν ∈ deg1Roots := List.mem_append_left _ hνM
  refine ⟨fun _ => ?_, fun h2K => ?_⟩
  · by_contra hnot
    obtain ⟨γ, hγ, hcase⟩ := non_top_two ν hνM hnot
    have hγS := (s2pos_data γ hγ).1
    have hco := coeff_vanish hK (hfix γ hγ) ν
    rcases hcase with ⟨hr, hnr⟩ | hr
    · have hab := (h1.short γ hγS ν hνD).1 hr
      rw [if_neg hnr] at hab
      exact hν ((mul_eq_zero.1 hco.1).resolve_left (cast_ne_zero_of_abs_eq_one hab))
    · have hab := (h2.short γ hγS ν hνD).1 hr
      exact hν ((mul_eq_zero.1 hco.2).resolve_left (cast_ne_zero_of_abs_eq_one hab))
  · by_contra hnot
    obtain ⟨γ, hγ, hr⟩ := non_top_odd ν hνM hnot
    have hγS := (s2pos_data γ hγ).1
    have hco := coeff_vanish hK (hfix γ hγ) ν
    have hab := (h1.short γ hγS ν hνD).1 hr
    by_cases hmem : ν - γ ∈ rootFinset .F4
    · rw [if_pos hmem] at hab
      exact hν ((mul_eq_zero.1 hco.1).resolve_left (cast_ne_zero_of_abs_eq_two hab h2K))
    · rw [if_neg hmem] at hab
      exact hν ((mul_eq_zero.1 hco.1).resolve_left (cast_ne_zero_of_abs_eq_one hab))

theorem exists_max_aux {P : ℕ → Prop} (h0 : P 0) : ∀ n, ¬ P n → ∃ k, P k ∧ ¬ P (k + 1)
  | 0, h => absurd h0 h
  | n + 1, h => by
    by_cases hn : P n
    · exact ⟨n, hn, h⟩
    · exact exists_max_aux h0 n hn

theorem exists_fixed_vector
    (W : Set ((Fin Tag.F4.rank → ℤ) → K))
    (hadd : ∀ c ∈ W, ∀ c' ∈ W, c + c' ∈ W) (hneg : ∀ c ∈ W, -c ∈ W)
    (hsupp : ∀ c ∈ W, ∀ ν, c ν ≠ 0 → ν ∈ mRoots)
    (hstab : ∀ γ ∈ f4ShortList, ∀ t : K, ∀ c ∈ W, actFun a1 a2 γ t c ∈ W)
    (hne : ∃ c ∈ W, c ≠ 0) :
    ∃ c ∈ W, c ≠ 0 ∧ ∀ γ ∈ s2pos, ∀ t : K, actFun a1 a2 γ t c = c := by
  classical
  let P : ℕ → Prop := fun k => ∃ c ∈ W, c ≠ 0 ∧ ∀ ν, c ν ≠ 0 → (k : ℤ) ≤ height ν
  have hP0 : P 0 := by
    obtain ⟨c, hc, hc0⟩ := hne
    refine ⟨c, hc, hc0, fun ν hν => ?_⟩
    have := (mRoots_height ν (hsupp c hc ν hν)).1
    simp only [Nat.cast_zero]
    omega
  have hP13 : ¬ P 13 := by
    rintro ⟨c, hc, hc0, h⟩
    obtain ⟨ν, hν⟩ : ∃ ν, c ν ≠ 0 := by
      by_contra hcon
      push Not at hcon
      exact hc0 (funext hcon)
    have h13 := h ν hν
    have := (mRoots_height ν (hsupp c hc ν hν)).2
    push_cast at h13
    omega
  obtain ⟨k, ⟨c, hcW, hc0, hck⟩, hk'⟩ := exists_max_aux hP0 13 hP13
  refine ⟨c, hcW, hc0, fun γ hγ t => ?_⟩
  have hγS := s2pos_data γ hγ
  have hdW : actFun a1 a2 γ t c + -c ∈ W := hadd _ (hstab γ hγS.1 t c hcW) _ (hneg c hcW)
  by_contra hne'
  apply hk'
  refine ⟨actFun a1 a2 γ t c + -c, hdW, ?_, fun ν hν => ?_⟩
  · intro h0
    apply hne'
    funext x
    have := congrFun h0 x
    simp only [Pi.add_apply, Pi.neg_apply, Pi.zero_apply] at this
    linear_combination this
  · have hν' : t * (a1 γ (ν - γ) : K) * c (ν - γ) +
        t ^ 2 * (a2 γ (ν - 2 • γ) : K) * c (ν - 2 • γ) ≠ 0 := by
      intro h0
      apply hν
      simp only [Pi.add_apply, Pi.neg_apply, actFun]
      linear_combination h0
    have hcase : c (ν - γ) ≠ 0 ∨ c (ν - 2 • γ) ≠ 0 := by
      by_contra hboth
      push Not at hboth
      apply hν'
      rw [hboth.1, hboth.2]
      ring
    have hγh := hγS.2
    push_cast
    rcases hcase with hc1 | hc2
    · have hk1 := hck _ hc1
      have := height_sub' ν γ
      omega
    · have hk2 := hck _ hc2
      have := height_sub' ν (2 • γ)
      rw [height_two_smul] at this
      omega

theorem LA_core (hK : ∃ t : K, t ≠ 0 ∧ t ≠ 1) (h1 : Adm1 a1) (h2 : Adm2 a2)
    (W : Set ((Fin Tag.F4.rank → ℤ) → K))
    (hadd : ∀ c ∈ W, ∀ c' ∈ W, c + c' ∈ W) (hneg : ∀ c ∈ W, -c ∈ W)
    (hsupp : ∀ c ∈ W, ∀ ν, c ν ≠ 0 → ν ∈ mRoots)
    (hstab : ∀ γ ∈ f4ShortList, ∀ t : K, ∀ c ∈ W, actFun a1 a2 γ t c ∈ W)
    (hne : ∃ c ∈ W, c ≠ 0) :
    ∃ ν ∈ mRoots, ∃ e : K, e ≠ 0 ∧ Pi.single ν e ∈ W := by
  obtain ⟨c, hcW, hc0, hfix⟩ := exists_fixed_vector W hadd hneg hsupp hstab hne
  exact words_extract h1 h2 W hadd hneg hstab hcW hc0
    (fixed_support_tops hK h1 h2 (hsupp c hcW) hfix)

end CFSG.HardMathSupport.Foote.Coordinator.SplitFrame.DetectF4
