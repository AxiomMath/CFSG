module

public import CFSG.LieType.SeitzGeneration.SpF2.ConfigRat

public section

namespace CFSG.LieType.SeitzGeneration.SpF2

open CFSG.RankThree.Classical CFSG.LieType.SeitzGeneration.RootPair

variable {r : ℕ} {K : Type} [Field K] {k : Subfield K}

theorem exists_ratio_not_mem {b : Fin r ⊕ Fin r → K}
    (hb : ¬∃ (c : K) (v₀ : Fin r ⊕ Fin r → k), b = c • ratVec v₀) :
    ∃ i j, b i ≠ 0 ∧ b j / b i ∉ k := by
  by_contra h
  push Not at h
  apply hb
  by_cases hb0 : b = 0
  · exact ⟨0, 0, by rw [hb0, zero_smul]⟩
  obtain ⟨i, hi⟩ : ∃ i, b i ≠ 0 := by
    by_contra h'
    push Not at h'
    exact hb0 (funext h')
  refine ⟨b i, fun j => ⟨b j / b i, h i j hi⟩, funext fun j => ?_⟩
  change b j = b i * (b j / b i)
  rw [mul_div_cancel₀ _ hi]

theorem exists_orth_pair_of_third {b : Fin r ⊕ Fin r → K} {i j x : Fin r ⊕ Fin r}
    (hxi : (dualVec x : Fin r ⊕ Fin r → K) i = 0) (hxj : (dualVec x : Fin r ⊕ Fin r → K) j = 0)
    (hi : b i ≠ 0) (hj : b j / b i ∉ k) (hx : b x ≠ 0) :
    ∃ a₀ a₀'' : Fin r ⊕ Fin r → k, spForm r K (ratVec a₀) (ratVec a₀'') = 0 ∧
      spForm r K (ratVec a₀) b ≠ 0 ∧
      spForm r K (ratVec a₀'') b / spForm r K (ratVec a₀) b ∉ k := by
  by_cases h1 : b x / b i ∈ k
  · have hj0 : b j ≠ 0 := fun h => hj (by rw [h, zero_div]; exact k.zero_mem)
    refine ⟨dualVec j, dualVec x, ?_, ?_, ?_⟩ <;> simp only [ratVec_dualVec, spForm_dualVec]
    · exact hxj
    · exact hj0
    · intro h2
      apply hj
      have h3 : b j / b i = b x / b i / (b x / b j) := by
        field_simp
      rw [h3]
      exact k.div_mem h1 h2
  · refine ⟨dualVec i, dualVec x, ?_, ?_, ?_⟩ <;> simp only [ratVec_dualVec, spForm_dualVec]
    · exact hxi
    · exact hi
    · exact h1

theorem exists_orth_pair_of_indices {b : Fin r ⊕ Fin r → K} {i j x y : Fin r ⊕ Fin r}
    (hxi : (dualVec x : Fin r ⊕ Fin r → K) i = 0) (hxj : (dualVec x : Fin r ⊕ Fin r → K) j = 0)
    (hyi : (dualVec y : Fin r ⊕ Fin r → K) i = 0) (hyj : (dualVec y : Fin r ⊕ Fin r → K) j = 0)
    (hsum : (dualVec j : Fin r ⊕ Fin r → K) i + (dualVec y : Fin r ⊕ Fin r → K) x = 0)
    (hi : b i ≠ 0) (hj : b j / b i ∉ k) :
    ∃ a₀ a₀'' : Fin r ⊕ Fin r → k, spForm r K (ratVec a₀) (ratVec a₀'') = 0 ∧
      spForm r K (ratVec a₀) b ≠ 0 ∧
      spForm r K (ratVec a₀'') b / spForm r K (ratVec a₀) b ∉ k := by
  by_cases hx : b x = 0
  · by_cases hy : b y = 0
    · have hjx : (dualVec j : Fin r ⊕ Fin r → K) x = 0 := by
        have h := spForm_isAlt.neg_eq (dualVec j : Fin r ⊕ Fin r → K) (dualVec x)
        rw [spForm_dualVec, spForm_dualVec, hxj, neg_zero] at h
        exact h.symm
      refine ⟨dualVec i + dualVec x, dualVec j + dualVec y, ?_, ?_, ?_⟩ <;>
        simp only [ratVec_add, ratVec_dualVec, map_add, LinearMap.add_apply, spForm_dualVec,
          hx, hy, hyi, hjx, add_zero, zero_add]
      · exact hsum
      · exact hi
      · exact hj
    · exact exists_orth_pair_of_third hyi hyj hi hj hy
  · exact exists_orth_pair_of_third hxi hxj hi hj hx

theorem exists_orth_pair (hr : 2 ≤ r) {b : Fin r ⊕ Fin r → K} {i j : Fin r ⊕ Fin r}
    (hi : b i ≠ 0) (hj : b j / b i ∉ k) :
    ∃ a₀ a₀'' : Fin r ⊕ Fin r → k, spForm r K (ratVec a₀) (ratVec a₀'') = 0 ∧
      spForm r K (ratVec a₀) b ≠ 0 ∧
      spForm r K (ratVec a₀'') b / spForm r K (ratVec a₀) b ∉ k := by
  by_cases hij : (dualVec j : Fin r ⊕ Fin r → K) i = 0
  · refine ⟨dualVec i, dualVec j, ?_, ?_, ?_⟩ <;> simp only [ratVec_dualVec, spForm_dualVec]
    · exact hij
    · exact hi
    · exact hj
  have : Nontrivial (Fin r) := Fin.nontrivial_iff_two_le.mpr hr
  rcases i with c | c <;> rcases j with c₂ | c₂
  · simp [dualVec] at hij
  · simp [dualVec, Pi.single_apply] at hij
    subst hij
    obtain ⟨c', hc'⟩ := exists_ne c
    exact exists_orth_pair_of_indices (x := Sum.inr c') (y := Sum.inl c')
      (by simp [dualVec, Ne.symm hc']) (by simp [dualVec]) (by simp [dualVec])
      (by simp [dualVec, Ne.symm hc']) (by simp [dualVec]) hi hj
  · simp [dualVec, Pi.single_apply] at hij
    subst hij
    obtain ⟨c', hc'⟩ := exists_ne c
    exact exists_orth_pair_of_indices (x := Sum.inl c') (y := Sum.inr c')
      (by simp [dualVec, Ne.symm hc']) (by simp [dualVec]) (by simp [dualVec])
      (by simp [dualVec, Ne.symm hc']) (by simp [dualVec]) hi hj
  · simp [dualVec] at hij

end CFSG.LieType.SeitzGeneration.SpF2
