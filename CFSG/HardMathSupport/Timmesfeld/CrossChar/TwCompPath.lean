module

public import CFSG.HardMathSupport.Timmesfeld.CrossChar.TwCompChain
public import CFSG.HardMathSupport.Timmesfeld.CrossChar.TwCompAlcove

public section

namespace CFSG.HardMathSupport.Timmesfeld.CrossChar

open CFSG.Blueprint.Chevalley CFSG.LieType.Chevalley CFSG.LieType.Steinberg.Adjoint

section Seq

theorem sum_sq_diff_eq (e : ℕ → ℤ) (n : ℕ) :
    ∑ j ∈ Finset.range (n + 1), (e (j + 1) - e j) ^ 2 =
      ∑ c ∈ Finset.range n, e (c + 1) * (2 * e (c + 1) - e (c + 2) - e c) +
        e 0 * (e 0 - e 1) + e (n + 1) * (e (n + 1) - e n) := by
  induction n with
  | zero => simp; ring
  | succ n ih =>
    rw [Finset.sum_range_succ, ih, Finset.sum_range_succ]
    ring

theorem eq_zero_of_sum_sq_diff_eq_zero (e : ℕ → ℤ) (h0 : e 0 = 0) (n : ℕ)
    (h : ∑ j ∈ Finset.range n, (e (j + 1) - e j) ^ 2 = 0) : ∀ t ≤ n, e t = 0 := by
  have hj : ∀ j ∈ Finset.range n, (e (j + 1) - e j) ^ 2 = 0 :=
    (Finset.sum_eq_zero_iff_of_nonneg fun j _ => sq_nonneg _).1 h
  intro t
  induction t with
  | zero => exact fun _ => h0
  | succ t ih =>
    intro ht
    have h1 := hj t (Finset.mem_range.2 (by omega))
    have h2 : e (t + 1) - e t = 0 := pow_eq_zero_iff (n := 2) (by norm_num) |>.1 h1
    rw [← ih (by omega)]
    linarith

theorem sq_eq_zero_or_one_of_le_one {d : ℤ} (h : d ^ 2 ≤ 1) : d ^ 2 = 0 ∨ d ^ 2 = 1 := by
  have h1 : -1 ≤ d := by nlinarith
  have h2 : d ≤ 1 := by nlinarith
  interval_cases d <;> simp

theorem step_of_sum_sq_eq_one (e : ℕ → ℤ) (h0 : e 0 = 0) (n : ℕ)
    (h : ∑ j ∈ Finset.range n, (e (j + 1) - e j) ^ 2 = 1) :
    ∃ i < n, ∃ s : ℤ, s ^ 2 = 1 ∧ ∀ t ≤ n, e t = if i < t then s else 0 := by
  induction n with
  | zero => simp at h
  | succ n ih =>
    rw [Finset.sum_range_succ] at h
    have hS : 0 ≤ ∑ j ∈ Finset.range n, (e (j + 1) - e j) ^ 2 :=
      Finset.sum_nonneg fun j _ => sq_nonneg _
    have hd : (e (n + 1) - e n) ^ 2 ≤ 1 := by linarith
    rcases sq_eq_zero_or_one_of_le_one hd with hd0 | hd1
    · obtain ⟨i, hi, s, hs, he⟩ := ih (by linarith)
      have hen : e (n + 1) = e n := by
        have := pow_eq_zero_iff (n := 2) (by norm_num) |>.1 hd0
        linarith
      refine ⟨i, by omega, s, hs, fun t ht => ?_⟩
      rcases (by omega : t ≤ n ∨ t = n + 1) with ht' | rfl
      · exact he t ht'
      · rw [hen, he n le_rfl, ite_eq_left hi, ite_eq_left (by omega)]
    · have hz := eq_zero_of_sum_sq_diff_eq_zero e h0 n (by linarith)
      refine ⟨n, by omega, e (n + 1), ?_, fun t ht => ?_⟩
      · rw [hz n le_rfl, sub_zero] at hd1
        exact hd1
      · rcases (by omega : t ≤ n ∨ t = n + 1) with ht' | rfl
        · rw [hz t ht', ite_eq_right (by omega)]
        · rw [ite_eq_left (by omega)]

theorem interval_of_sum_sq_eq_two (e : ℕ → ℤ) (h0 : e 0 = 0) (m : ℕ) (hm : e (m + 1) = 0)
    (h : ∑ j ∈ Finset.range (m + 1), (e (j + 1) - e j) ^ 2 = 2) :
    ∃ i j : ℕ, i < j ∧ j ≤ m ∧ ∃ s : ℤ, s ^ 2 = 1 ∧
      ∀ t ≤ m + 1, e t = if i < t ∧ t ≤ j then s else 0 := by
  induction m with
  | zero =>
    rw [Finset.sum_range_one, hm, h0] at h
    norm_num at h
  | succ m ih =>
    rw [Finset.sum_range_succ, hm, zero_sub, neg_sq] at h
    have hS : 0 ≤ ∑ j ∈ Finset.range (m + 1), (e (j + 1) - e j) ^ 2 :=
      Finset.sum_nonneg fun j _ => sq_nonneg _
    by_cases he : e (m + 1) = 0
    · rw [he] at h
      obtain ⟨i, j, hij, hjm, s, hs, het⟩ := ih he (by linarith)
      refine ⟨i, j, hij, by omega, s, hs, fun t ht => ?_⟩
      rcases (by omega : t ≤ m + 1 ∨ t = m + 2) with ht' | rfl
      · exact het t ht'
      · rw [hm, ite_eq_right (by omega)]
    · have hpos : 0 < e (m + 1) ^ 2 := by positivity
      have hle : e (m + 1) ^ 2 ≤ 1 := by
        by_contra hc
        push Not at hc
        have : 2 ≤ e (m + 1) ^ 2 := by
          have h1 : e (m + 1) ≤ -2 ∨ 2 ≤ e (m + 1) := by
            by_contra h'
            push Not at h'
            have : e (m + 1) = -1 ∨ e (m + 1) = 1 := by
              have := h'.1; have := h'.2; omega
            rcases this with h'' | h'' <;> rw [h''] at hc <;> norm_num at hc
          rcases h1 with h1 | h1 <;> nlinarith
        have : e (m + 1) ^ 2 ≤ 2 := by linarith
        have h3 : e (m + 1) ^ 2 = 2 := by omega
        have h4 : e (m + 1) ≤ 1 := by nlinarith
        have h5 : -1 ≤ e (m + 1) := by nlinarith
        interval_cases (e (m + 1)) <;> simp at h3
      have h1 : e (m + 1) ^ 2 = 1 := by omega
      obtain ⟨i, hi, s, hs, het⟩ := step_of_sum_sq_eq_one e h0 (m + 1) (by linarith)
      refine ⟨i, m + 1, hi, le_rfl, s, hs, fun t ht => ?_⟩
      rcases (by omega : t ≤ m + 1 ∨ t = m + 2) with ht' | rfl
      · rw [het t ht']
        by_cases hit : i < t
        · rw [ite_eq_left hit, ite_eq_left ⟨hit, ht'⟩]
        · rw [ite_eq_right hit, ite_eq_right (fun h' => hit h'.1)]
      · rw [hm, ite_eq_right (by omega)]

end Seq

section Chain

variable {τ : Tag} {m : ℕ}

@[expose] def chainSeq (k : Fin m → ℤ) (t : ℕ) : ℤ :=
  if h : 1 ≤ t ∧ t ≤ m then k ⟨t - 1, by omega⟩ else 0

theorem chainSeq_succ (k : Fin m → ℤ) (c : Fin m) : chainSeq k ((c : ℕ) + 1) = k c := by
  have h : 1 ≤ (c : ℕ) + 1 ∧ (c : ℕ) + 1 ≤ m := ⟨by omega, by omega⟩
  simp only [chainSeq, h, and_self, dite_true]
  congr 1

theorem chainSeq_zero (k : Fin m → ℤ) : chainSeq k 0 = 0 := by
  simp [chainSeq]

theorem chainSeq_of_lt (k : Fin m → ℤ) {t : ℕ} (ht : m < t) : chainSeq k t = 0 := by
  simp only [chainSeq]
  rw [dite_eq_right_iff.2 fun h => absurd h.2 (by omega)]

theorem sum_mul_chainGram (k : Fin m → ℤ) (d : Fin m) :
    ∑ c : Fin m, k c * chainGram c d =
      2 * chainSeq k ((d : ℕ) + 1) - chainSeq k d - chainSeq k ((d : ℕ) + 2) := by
  classical
  have hG : ∀ c : Fin m, chainGram c d = (if c = d then 2 else 0) -
      (if (c : ℕ) + 1 = d then 1 else 0) - (if (d : ℕ) + 1 = c then 1 else 0) := by
    intro c
    simp only [chainGram]
    by_cases h1 : c = d
    · subst h1
      simp
    · have : (c : ℕ) ≠ d := fun h => h1 (Fin.ext h)
      by_cases h2 : (c : ℕ) + 1 = d
      · simp [h1, h2, show ¬ (d : ℕ) + 1 = c by omega]
      · by_cases h3 : (d : ℕ) + 1 = c
        · simp [h1, h2, h3]
        · simp [h1, h2, h3]
  simp only [hG, mul_sub, mul_ite, mul_zero, mul_one, Finset.sum_sub_distrib]
  rw [Finset.sum_ite_eq']
  simp only [Finset.mem_univ, ite_true]
  have h1 : ∑ c : Fin m, (if (c : ℕ) + 1 = d then k c else 0) = chainSeq k d := by
    by_cases hd : (d : ℕ) = 0
    · rw [Finset.sum_eq_zero fun c _ => by rw [ite_eq_right (by omega)]]
      rw [hd, chainSeq_zero]
    · have hlt : (d : ℕ) - 1 < m := by omega
      rw [Finset.sum_eq_single (⟨d - 1, hlt⟩ : Fin m) (fun c _ hc => by
          rw [ite_eq_right fun h => hc (Fin.ext (by simp; omega))]) (by simp)]
      rw [ite_eq_left (by simp; omega)]
      have := chainSeq_succ k ⟨d - 1, hlt⟩
      rw [← this]
      congr 1
      simp
      omega
  have h2 : ∑ c : Fin m, (if (d : ℕ) + 1 = c then k c else 0) = chainSeq k ((d : ℕ) + 2) := by
    by_cases hd : (d : ℕ) + 1 < m
    · rw [Finset.sum_eq_single (⟨d + 1, hd⟩ : Fin m) (fun c _ hc => by
          rw [ite_eq_right fun h => hc (Fin.ext (by simp; omega))]) (by simp)]
      rw [ite_eq_left rfl]
      exact (chainSeq_succ k ⟨d + 1, hd⟩).symm
    · rw [Finset.sum_eq_zero fun c _ => by rw [ite_eq_right (by omega)], chainSeq_of_lt k
        (by omega)]
  rw [h1, h2, chainSeq_succ]
  ring

theorem iform_chain_sum
    {β : Fin m → Fin τ.rank → ℤ} (hG : ∀ c d, iform (β c) (β d) = chainGram c d)
    (k : Fin m → ℤ) :
    iform (∑ c, k c • β c) (∑ c, k c • β c) =
      ∑ j ∈ Finset.range (m + 1), (chainSeq k (j + 1) - chainSeq k j) ^ 2 := by
  have h1 : iform (∑ c, k c • β c) (∑ c, k c • β c) =
      ∑ d : Fin m, k d * ∑ c : Fin m, k c * chainGram c d := by
    rw [iform_finset_sum_right]
    refine Finset.sum_congr rfl fun d _ => ?_
    rw [iform_smul_right, iform_finset_sum_left]
    congr 1
    exact Finset.sum_congr rfl fun c _ => by rw [iform_smul_left, hG]
  rw [h1, sum_sq_diff_eq, chainSeq_zero, chainSeq_of_lt k (by omega : m < m + 1)]
  simp only [zero_mul, add_zero]
  rw [← Fin.sum_univ_eq_sum_range (fun c => chainSeq k (c + 1) *
    (2 * chainSeq k (c + 1) - chainSeq k (c + 2) - chainSeq k c))]
  refine Finset.sum_congr rfl fun d _ => ?_
  rw [sum_mul_chainGram, chainSeq_succ]
  ring

theorem mem_frameRoots_of_isRoot
    (hτ : τ = .D4 ∨ τ = .E6 ∨ τ = .E7 ∨ τ = .E8) {β : Fin m → Fin τ.rank → ℤ}
    (hG : ∀ c d, iform (β c) (β d) = chainGram c d) {k : Fin m → ℤ} (hk : ∀ c, 0 ≤ k c)
    {γ : Fin τ.rank → ℤ} (hγ : IsRoot τ γ)
    (hγk : γ = ∑ c, k c • β c ∨ γ = -∑ c, k c • β c) : γ ∈ frameRoots (chainσ β) := by
  have h2 : iform (∑ c, k c • β c) (∑ c, k c • β c) = 2 := by
    have := CFSG.LieType.Chevalley.EvenOddRadical.iform_self_eq_two hτ hγ
    rcases hγk with e | e
    · rwa [e] at this
    · rw [e, show ∀ v : Fin τ.rank → ℤ, -v = (-1 : ℤ) • v from fun v => by rw [neg_one_smul],
        iform_smul_left, iform_smul_right] at this
      linarith
  rw [iform_chain_sum hG] at h2
  obtain ⟨i, j, hij, hjm, s, hs, he⟩ := interval_of_sum_sq_eq_two (chainSeq k) (chainSeq_zero k)
    m (chainSeq_of_lt k (by omega)) h2
  have hs1 : s = 1 := by
    have h := he (i + 1) (by omega)
    rw [ite_eq_left ⟨by omega, by omega⟩] at h
    have hpos : 0 ≤ s := by
      rw [← h, chainSeq]
      split_ifs with hh
      · exact hk _
      · exact le_rfl
    have : s ≤ 1 := by nlinarith
    have : s ≠ 0 := fun h0 => by rw [h0] at hs; norm_num at hs
    omega
  subst hs1
  have hkc : ∀ c : Fin m, k c = if i ≤ (c : ℕ) ∧ (c : ℕ) < j then 1 else 0 := by
    intro c
    have := he ((c : ℕ) + 1) (by omega)
    rw [chainSeq_succ] at this
    rw [this]
    by_cases h : i < (c : ℕ) + 1 ∧ (c : ℕ) + 1 ≤ j
    · rw [ite_eq_left h, ite_eq_left ⟨by omega, by omega⟩]
    · rw [ite_eq_right h, ite_eq_right fun h' => h ⟨by omega, by omega⟩]
  have hsum : ∑ c, k c • β c = chainσ β ⟨i, by omega⟩ ⟨j, by omega⟩ := by
    simp only [chainσ, chainω]
    rw [← Finset.sum_sub_distrib]
    refine Finset.sum_congr rfl fun c _ => ?_
    rw [hkc]
    by_cases h1 : (c : ℕ) < j <;> by_cases h2 : (c : ℕ) < i <;> simp [h1, h2]
    all_goals omega
  have hne : (⟨i, by omega⟩ : Fin (m + 1)) ≠ ⟨j, by omega⟩ := fun h => by
    have := congrArg Fin.val h
    simp at this
    omega
  rcases hγk with e | e
  · exact ⟨_, _, hne, by rw [e, hsum]⟩
  · exact ⟨_, _, hne.symm, by rw [e, hsum, chainσ_neg β ⟨j, by omega⟩, neg_neg]⟩

theorem exists_coeff_of_mem_frameRoots {β : Fin m → Fin τ.rank → ℤ} {γ : Fin τ.rank → ℤ}
    (hγ : γ ∈ frameRoots (chainσ β)) :
    ∃ k : Fin m → ℕ, γ = ∑ c, (k c : ℤ) • β c ∨ γ = -∑ c, (k c : ℤ) • β c := by
  classical
  obtain ⟨a, b, -, rfl⟩ := hγ
  have key : ∀ a b : Fin (m + 1), a ≤ b →
      chainσ β a b = ∑ c : Fin m,
        ((if (a : ℕ) ≤ (c : ℕ) ∧ (c : ℕ) < b then 1 else 0 : ℕ) : ℤ) • β c := by
    intro a b hab
    simp only [chainσ, chainω]
    rw [← Finset.sum_sub_distrib]
    refine Finset.sum_congr rfl fun c _ => ?_
    by_cases h1 : (c : ℕ) < b <;> by_cases h2 : (c : ℕ) < a <;> simp [h1, h2]
    all_goals omega
  rcases le_total a b with h | h
  · exact ⟨_, Or.inl (key a b h)⟩
  · exact ⟨_, Or.inr (by rw [chainσ_neg, key b a h])⟩

end Chain

namespace KacData

variable {τ : Tag} (K : KacData τ)
  {m : ℕ}

theorem combo_eq_sum_of_supp {l : Fin m → Option (Fin τ.rank)} (hl : Function.Injective l)
    {n : Option (Fin τ.rank) → ℕ} (hn : ∀ x, n x ≠ 0 → x ∈ Set.range l) :
    K.combo n = ∑ c, (n (l c) : ℤ) • K.extRoot (l c) := by
  classical
  rw [combo, ← Finset.sum_image (f := fun x => (n x : ℤ) • K.extRoot x)
    (fun c _ c' _ h => hl h)]
  refine (Finset.sum_subset (Finset.subset_univ _) fun x _ hx => ?_).symm
  have : n x = 0 := by
    by_contra h
    obtain ⟨c, rfl⟩ := hn x h
    exact hx (Finset.mem_image_of_mem l (Finset.mem_univ c))
  rw [this, Nat.cast_zero, zero_smul]

theorem rootsOf_range_eq_frameRoots (hτ : τ = .D4 ∨ τ = .E6 ∨ τ = .E7 ∨ τ = .E8)
    {l : Fin m → Option (Fin τ.rank)} (hl : Function.Injective l)
    (hG : ∀ c d, iform (K.extRoot (l c)) (K.extRoot (l d)) = chainGram c d) :
    K.rootsOf (Set.range l) = frameRoots (chainσ (fun c => K.extRoot (l c))) := by
  classical
  ext γ
  constructor
  · rintro ⟨hγ, n, hn, hγn⟩
    rw [K.combo_eq_sum_of_supp hl hn] at hγn
    exact mem_frameRoots_of_isRoot hτ hG (k := fun c => (n (l c) : ℤ))
      (fun c => Nat.cast_nonneg _) hγ hγn
  · intro hγ
    have hroot : IsRoot τ γ := by
      obtain ⟨a, b, hab, rfl⟩ := hγ
      exact isRoot_chainσ (fun c => K.isRoot_extRoot (l c)) hG hab
    obtain ⟨k, hk⟩ := exists_coeff_of_mem_frameRoots hγ
    set n : Option (Fin τ.rank) → ℕ := fun x => if h : ∃ c, l c = x then k h.choose else 0
      with hn
    have hsupp : ∀ x, n x ≠ 0 → x ∈ Set.range l := fun x hx => by
      by_contra h
      apply hx
      have h' : ¬ ∃ c, l c = x := fun ⟨c, hc⟩ => h ⟨c, hc⟩
      simp only [hn, h', dite_false]
    refine ⟨hroot, n, hsupp, ?_⟩
    rw [K.combo_eq_sum_of_supp hl hsupp]
    have hval : ∀ c, n (l c) = k c := fun c => by
      have h : ∃ c', l c' = l c := ⟨c, rfl⟩
      simp only [hn, h, dite_true]
      congr 1
      exact hl h.choose_spec
    simp only [hval]
    exact hk

end KacData

end CFSG.HardMathSupport.Timmesfeld.CrossChar
