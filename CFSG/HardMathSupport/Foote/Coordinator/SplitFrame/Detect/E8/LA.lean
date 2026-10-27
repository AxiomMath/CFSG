module

public import CFSG.HardMathSupport.Foote.Coordinator.SplitFrame.Detect.E8.LAData

public noncomputable section

namespace CFSG.HardMathSupport.Foote.Coordinator.SplitFrame.DetectE8

open CFSG.Blueprint CFSG.Blueprint.Chevalley CFSG.LieType.Chevalley CFSG.SeitzReduction

variable {K : Type} [Field K] {a : (Fin Tag.E8.rank → ℤ) → (Fin Tag.E8.rank → ℤ) → ℤ}

theorem cast_ne_zero_of_abs_eq_one {z : ℤ} (h : |z| = 1) : (z : K) ≠ 0 := by
  rcases (abs_eq zero_le_one).1 h with rfl | rfl <;> simp

theorem deg1_of_mRoots {μ : Fin Tag.E8.rank → ℤ} (h : μ ∈ mRoots) : μ ∈ deg1Roots :=
  Finset.mem_filter.2 ⟨(Finset.mem_filter.1 h).1, (Finset.mem_filter.1 h).2.1⟩

theorem lxPos_sub : ∀ γ ∈ lxPos, γ ∈ lxRoots := fun γ hγ =>
  Finset.mem_filter.2 ⟨(Finset.mem_filter.1 hγ).1, (Finset.mem_filter.1 hγ).2.1,
    (Finset.mem_filter.1 hγ).2.2.1⟩

theorem top_words : ∀ μ ∈ topsE8, ∃ γ ∈ lxRoots, γ + μ ∈ rootFinset .E8 ∧ γ + μ ∉ topsE8 ∧
    ∀ μ' ∈ topsE8, μ' ≠ μ → γ + μ' ∉ rootFinset .E8 := by
  simp only [topsE8, lxRoots, rootFinset_E8_eq]
  decide +kernel

theorem exists_max_aux {P : ℕ → Prop} (h0 : P 0) : ∀ n, ¬ P n → ∃ k, P k ∧ ¬ P (k + 1)
  | 0, h => absurd h0 h
  | n + 1, h => by
    by_cases hn : P n
    · exact ⟨n, hn, h⟩
    · exact exists_max_aux h0 n hn

theorem exists_fixed_vector
    (W : Set ((Fin Tag.E8.rank → ℤ) → K))
    (hadd : ∀ c ∈ W, ∀ c' ∈ W, c + c' ∈ W) (hneg : ∀ c ∈ W, -c ∈ W)
    (hsupp : ∀ c ∈ W, ∀ ν, c ν ≠ 0 → ν ∈ mRoots)
    (hstab : ∀ γ ∈ lxRoots, ∀ t : K, ∀ c ∈ W, actFun a γ t c ∈ W)
    (hne : ∃ c ∈ W, c ≠ 0) :
    ∃ c ∈ W, c ≠ 0 ∧ ∀ γ ∈ lxPos, ∀ t : K, actFun a γ t c = c := by
  classical
  let P : ℕ → Prop := fun k => ∃ c ∈ W, c ≠ 0 ∧ ∀ ν, c ν ≠ 0 → (k : ℤ) ≤ height ν
  have hP0 : P 0 := by
    obtain ⟨c, hc, hc0⟩ := hne
    refine ⟨c, hc, hc0, fun ν hν => ?_⟩
    have := (mRoots_height ν (hsupp c hc ν hν)).1
    simp only [Nat.cast_zero]
    omega
  have hP30 : ¬ P 30 := by
    rintro ⟨c, hc, hc0, h⟩
    obtain ⟨ν, hν⟩ : ∃ ν, c ν ≠ 0 := by
      by_contra hcon
      push Not at hcon
      exact hc0 (funext hcon)
    have h30 := h ν hν
    have := (mRoots_height ν (hsupp c hc ν hν)).2
    push_cast at h30
    omega
  obtain ⟨k, ⟨c, hcW, hc0, hck⟩, hk'⟩ := exists_max_aux hP0 30 hP30
  refine ⟨c, hcW, hc0, fun γ hγ t => ?_⟩
  have hγd := lxPos_data γ hγ
  have hdW : actFun a γ t c + -c ∈ W := hadd _ (hstab γ (lxPos_sub γ hγ) t c hcW) _ (hneg c hcW)
  by_contra hne'
  apply hk'
  refine ⟨actFun a γ t c + -c, hdW, ?_, fun ν hν => ?_⟩
  · intro h0
    apply hne'
    funext x
    have := congrFun h0 x
    simp only [Pi.add_apply, Pi.neg_apply, Pi.zero_apply] at this
    linear_combination this
  · have hν' : t * (a γ (ν - γ) : K) * c (ν - γ) ≠ 0 := by
      intro h0
      apply hν
      simp only [Pi.add_apply, Pi.neg_apply, actFun]
      linear_combination h0
    have hc1 : c (ν - γ) ≠ 0 := fun h0 => hν' (by rw [h0]; ring)
    have hk1 := hck _ hc1
    have := height_sub' ν γ
    push_cast
    omega

theorem fixed_support_tops (h : Adm a) {c : (Fin Tag.E8.rank → ℤ) → K}
    (hsupp : ∀ ν, c ν ≠ 0 → ν ∈ mRoots)
    (hfix : ∀ γ ∈ lxPos, ∀ t : K, actFun a γ t c = c) : ∀ ν, c ν ≠ 0 → ν ∈ topsE8 := by
  intro ν hν
  by_contra hnot
  obtain ⟨γ, hγ, hr⟩ := non_top ν (hsupp ν hν) hnot
  have hγd := lxPos_data γ hγ
  have h1 := congrFun (hfix γ hγ 1) (γ + ν)
  simp only [actFun, add_sub_cancel_left, one_mul] at h1
  have h2 : (a γ ν : K) * c ν = 0 := by linear_combination h1
  have hab := (h γ hγd.1 hγd.2.1 ν (deg1_of_mRoots (hsupp ν hν))).1 hr
  exact hν ((mul_eq_zero.1 h2).resolve_left (cast_ne_zero_of_abs_eq_one hab))

theorem words_extract (h : Adm a) (W : Set ((Fin Tag.E8.rank → ℤ) → K))
    (hadd : ∀ c ∈ W, ∀ c' ∈ W, c + c' ∈ W) (hneg : ∀ c ∈ W, -c ∈ W)
    (hstab : ∀ γ ∈ lxRoots, ∀ t : K, ∀ c ∈ W, actFun a γ t c ∈ W)
    {c : (Fin Tag.E8.rank → ℤ) → K} (hc : c ∈ W) (hc0 : c ≠ 0)
    (hsupp : ∀ ν, c ν ≠ 0 → ν ∈ topsE8) :
    ∃ ν ∈ mRoots, ∃ e : K, e ≠ 0 ∧ Pi.single ν e ∈ W := by
  classical
  obtain ⟨μ, hμ⟩ : ∃ μ, c μ ≠ 0 := by
    by_contra hcon
    push Not at hcon
    exact hc0 (funext hcon)
  obtain ⟨γ, hγ, hμγ, hnotop, hother⟩ := top_words μ (hsupp μ hμ)
  have hdW : actFun a γ 1 c + -c ∈ W := hadd _ (hstab γ hγ 1 c hc) _ (hneg c hc)
  have hμM : μ ∈ mRoots := topsE8_data μ (hsupp μ hμ)
  have hγd := lxRoots_data γ hγ
  have hmem : γ + μ ∈ mRoots := add_mem_mRoots γ hγ μ hμM hμγ
  have hneμ : (a γ μ : K) ≠ 0 :=
    cast_ne_zero_of_abs_eq_one ((h γ hγd.1 hγd.2.1 μ (deg1_of_mRoots hμM)).1 hμγ)
  refine ⟨γ + μ, hmem, (a γ μ : K) * c μ, mul_ne_zero hneμ hμ, ?_⟩
  have e : actFun a γ 1 c + -c = Pi.single (γ + μ) ((a γ μ : K) * c μ) := by
    funext ν
    simp only [Pi.add_apply, Pi.neg_apply, actFun, one_mul]
    by_cases hν : ν = γ + μ
    · subst hν
      rw [Pi.single_eq_same, add_sub_cancel_left]
      have h0 : c (γ + μ) = 0 := by
        by_contra hne
        exact hnotop (hsupp _ hne)
      rw [h0]
      ring
    · rw [Pi.single_eq_of_ne hν]
      by_cases hc' : c (ν - γ) = 0
      · rw [hc']
        ring
      · have hμ' := hsupp _ hc'
        have hne : ν - γ ≠ μ := fun e' => hν (by rw [← e']; abel)
        have hnr := hother _ hμ' hne
        have ha0 : a γ (ν - γ) = 0 :=
          (h γ hγd.1 hγd.2.1 (ν - γ) (deg1_of_mRoots (topsE8_data _ hμ'))).2 hnr
        rw [ha0]
        simp
  rw [← e]
  exact hdW

end CFSG.HardMathSupport.Foote.Coordinator.SplitFrame.DetectE8
