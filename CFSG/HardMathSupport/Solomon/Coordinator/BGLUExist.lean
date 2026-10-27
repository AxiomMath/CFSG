module

public import CFSG.HardMathSupport.Solomon.Coordinator.BGLUExistBasic
public import CFSG.HardMathSupport.Solomon.Coordinator.BGLUQuad

public section

namespace CFSG.HardMathSupport.Solomon.Coordinator.BGL

open Matrix CFSG.ClassicalGroups.Unitary

variable {K : Type*} [Field K] {ι ρ : K ≃+* K}

variable (ι ρ) in
@[expose] def AllNorm (M : Matrix (Fin 3) (Fin 3) K) : Prop :=
  ∀ a b : Fin 3 → K, Ratv ρ a → Ratv ρ b → herm ι a a = 0 → herm ι b b = 0 →
    ρ (ι (Bf ι M a b) * Bf ι M a b) = ι (Bf ι M a b) * Bf ι M a b

variable (ι ρ) in
structure IsoBasis where
  g : Fin 3 → Fin 3 → K
  rat : ∀ k, Ratv ρ (g k)
  iso : ∀ k, herm ι (g k) (g k) = 0
  nonorth : ∀ k l, k ≠ l → herm ι (g k) (g l) ≠ 0
  span : ∀ j, ∃ κ : Fin 3 → K, (∀ k, ρ (κ k) = κ k) ∧
    (Pi.single j 1 : Fin 3 → K) = ∑ k, κ k • g k

variable (C : UCtx ι ρ) (M : Matrix (Fin 3) (Fin 3) K)

include C

theorem iso_add {e f : Fin 3 → K} (heI : herm ι e e = 0) (hfI : herm ι f f = 0)
    (hef : herm ι e f = 1) {t : K} (ht : t + ι t = 0) :
    herm ι (f + t • e) (f + t • e) = 0 := by
  have hfe : herm ι f e = 1 := by rw [herm_conj ι C.ιinv, hef, map_one]
  simp only [herm_add_left, herm_add_right, herm_smul_left, herm_smul_right, hfI, heI, hef, hfe]
  linear_combination ht

omit C in
theorem Bf_sum_right (a : Fin 3 → K) (κ : Fin 3 → K) (g : Fin 3 → Fin 3 → K) :
    Bf ι M a (∑ k, κ k • g k) = ∑ k, κ k * Bf ι M a (g k) := by
  simp only [Fin.sum_univ_three, Bf_add_right, Bf_smul_right]

omit C in
theorem rowv_sum (κ : Fin 3 → K) (g : Fin 3 → Fin 3 → K) :
    rowv ι M (∑ k, κ k • g k) = ∑ k, ι (κ k) • rowv ι M (g k) := by
  simp only [Fin.sum_univ_three, rowv_add, rowv_smul]

theorem layer1 (hall : AllNorm ι ρ M) {a e f : Fin 3 → K} (ha : Ratv ρ a) (he : Ratv ρ e)
    (hf : Ratv ρ f) (haI : herm ι a a = 0) (heI : herm ι e e = 0) (hfI : herm ι f f = 0)
    (hef : herm ι e f = 1) (hy : Bf ι M a e ≠ 0) :
    ρ (Bf ι M a f / Bf ι M a e) = Bf ι M a f / Bf ι M a e := by
  obtain ⟨c, hc0, hρc, hιc⟩ := C.c₀
  obtain ⟨r, hr0, hr1, hρr, hιr⟩ := C.r₂
  have hb1 : Ratv ρ (f + c • e) := ratv_add hf (ratv_smul hρc he)
  have hb2 : Ratv ρ (f + (c * r) • e) := ratv_add hf (ratv_smul (by rw [map_mul, hρc, hρr]) he)
  have hi1 : herm ι (f + c • e) (f + c • e) = 0 :=
    iso_add C heI hfI hef (by rw [hιc]; ring)
  have hi2 : herm ι (f + (c * r) • e) (f + (c * r) • e) = 0 :=
    iso_add C heI hfI hef (by rw [map_mul, hιc, hιr]; ring)
  refine ratio_fixed_of_norms C.ιinv C.ρ3 hρc hιc hc0 hρr hιr hr0 hr1 ?_ ?_ ?_ hy
  · exact hall a f ha hf haI hfI
  · have := hall a _ ha hb1 haI hi1
    rwa [Bf_add_right, Bf_smul_right] at this
  · have := hall a _ ha hb2 haI hi2
    rwa [Bf_add_right, Bf_smul_right] at this

omit C in
theorem Bf_rowv_single (a : Fin 3 → K) (j : Fin 3) : rowv ι M a j = Bf ι M a (Pi.single j 1) := rfl

theorem rows_onLine (hall : AllNorm ι ρ M) (B : IsoBasis ι ρ) (hM : ∀ z, ∃ y, M *ᵥ y = z)
    {a : Fin 3 → K} (ha : Ratv ρ a) (haI : herm ι a a = 0) (ha0 : a ≠ 0) :
    ∃ c : K, c ≠ 0 ∧ OnLine ρ c (rowv ι M a) := by
  have hrow : ∀ j, rowv ι M a j = ∑ k, (B.span j).choose k * Bf ι M a (B.g k) := by
    intro j
    rw [Bf_rowv_single]
    conv_lhs => rw [(B.span j).choose_spec.2]
    exact Bf_sum_right M a _ _
  have hex : ∃ k, Bf ι M a (B.g k) ≠ 0 := by
    by_contra hcon
    push Not at hcon
    apply ha0
    refine (rowv_eq_zero_iff (ι := ι) M hM a).mp ?_
    funext j
    rw [hrow j]
    simp [hcon]
  obtain ⟨k₀, hk₀⟩ := hex
  set d₀ := Bf ι M a (B.g k₀) with hd₀
  have hrat : ∀ k, ρ (Bf ι M a (B.g k) / d₀) = Bf ι M a (B.g k) / d₀ := by
    intro k
    by_cases hk : k = k₀
    · subst hk; rw [← hd₀, div_self hk₀, map_one]
    · set sc := herm ι (B.g k₀) (B.g k) with hsc
      have hsc0 : sc ≠ 0 := B.nonorth k₀ k (Ne.symm hk)
      have hρs : ρ sc = sc := UCtx.ρ_herm C (B.rat k₀) (B.rat k)
      have hf : Ratv ρ (sc⁻¹ • B.g k) := ratv_smul (by rw [map_inv₀, hρs]) (B.rat k)
      have hfI : herm ι (sc⁻¹ • B.g k) (sc⁻¹ • B.g k) = 0 := by
        rw [herm_smul_left, herm_smul_right, B.iso k, mul_zero, mul_zero]
      have hef : herm ι (B.g k₀) (sc⁻¹ • B.g k) = 1 := by
        rw [herm_smul_right, ← hsc, inv_mul_cancel₀ hsc0]
      have := layer1 C M hall ha (B.rat k₀) hf haI (B.iso k₀) hfI hef hk₀
      rw [Bf_smul_right, ← hd₀] at this
      have e : sc⁻¹ * Bf ι M a (B.g k) / d₀ = sc⁻¹ * (Bf ι M a (B.g k) / d₀) := by ring
      rw [e, map_mul, map_inv₀, hρs] at this
      have hsinv : sc⁻¹ ≠ 0 := inv_ne_zero hsc0
      exact mul_left_cancel₀ hsinv this
  refine ⟨d₀, hk₀, fun j => ∑ k, (B.span j).choose k * (Bf ι M a (B.g k) / d₀), ?_, ?_⟩
  · intro j
    rw [map_sum]
    refine Finset.sum_congr rfl fun k _ => ?_
    rw [map_mul, (B.span j).choose_spec.1 k, hrat k]
  · funext j
    rw [hrow j]
    simp only [Pi.smul_apply, smul_eq_mul, Finset.mul_sum]
    refine Finset.sum_congr rfl fun k _ => ?_
    field_simp

theorem line_pair (hall : AllNorm ι ρ M) (B : IsoBasis ι ρ) (hM : ∀ z, ∃ y, M *ᵥ y = z)
    {e f : Fin 3 → K} (he : Ratv ρ e) (hf : Ratv ρ f) (heI : herm ι e e = 0)
    (hfI : herm ι f f = 0) (hγ : herm ι e f ≠ 0) :
    ∃ c : K, c ≠ 0 ∧ OnLine ρ c (rowv ι M e) ∧ OnLine ρ c (rowv ι M f) := by
  obtain ⟨c₀, hc0, hρc, hιc⟩ := C.c₀
  set γ := herm ι e f with hγdef
  have hργ : ρ γ = γ := UCtx.ρ_herm C he hf
  have hf' : Ratv ρ (γ⁻¹ • f) := ratv_smul (by rw [map_inv₀, hργ]) hf
  have hf'I : herm ι (γ⁻¹ • f) (γ⁻¹ • f) = 0 := by
    rw [herm_smul_left, herm_smul_right, hfI, mul_zero, mul_zero]
  have hef' : herm ι e (γ⁻¹ • f) = 1 := by
    rw [herm_smul_right, ← hγdef, inv_mul_cancel₀ hγ]
  have hfrow : f = γ • (γ⁻¹ • f) := by rw [smul_smul, mul_inv_cancel₀ hγ, one_smul]
  generalize γ⁻¹ • f = f' at hf' hf'I hef' hfrow
  have he0 : e ≠ 0 := by
    rintro rfl
    simp at hef'
  have hf'0 : f' ≠ 0 := by
    intro h
    rw [h] at hef'
    simp at hef'
  have ha₃ : Ratv ρ (f' + c₀ • e) := ratv_add hf' (ratv_smul hρc he)
  have ha₃I : herm ι (f' + c₀ • e) (f' + c₀ • e) = 0 :=
    iso_add C heI hf'I hef' (by rw [hιc]; ring)
  have ha₃0 : f' + c₀ • e ≠ 0 := by
    intro h
    have := congrArg (herm ι e) h
    rw [herm_add_right, herm_smul_right, hef', heI, mul_zero, add_zero, herm_zero_right] at this
    exact one_ne_zero this
  obtain ⟨c₂, hc₂, μ₂, hμ₂, hr₂⟩ := rows_onLine C M hall B hM he heI he0
  obtain ⟨c₁, hc₁, μ₁, hμ₁, hr₁⟩ := rows_onLine C M hall B hM hf' hf'I hf'0
  obtain ⟨c₃, hc₃, μ₃, hμ₃, hr₃⟩ := rows_onLine C M hall B hM ha₃ ha₃I ha₃0
  have hx : rowv ι M (f' + c₀ • e) = rowv ι M f' + (-c₀) • rowv ι M e := by
    rw [rowv_add, rowv_smul, hιc]
  have hfe : herm ι f' e = 1 := by rw [herm_conj ι C.ιinv, hef', map_one]
  have hind : ∀ α β : K, α • rowv ι M f' + β • rowv ι M e = 0 → α = 0 ∧ β = 0 := by
    intro α β h
    have h1 : rowv ι M (ι α • f' + ι β • e) = 0 := by
      rw [rowv_add, rowv_smul, rowv_smul, C.ιinv, C.ιinv]
      exact h
    have h2 := (rowv_eq_zero_iff M hM _).mp h1
    have h3 := congrArg (herm ι e) h2
    have h4 := congrArg (herm ι f') h2
    rw [herm_add_right, herm_smul_right, herm_smul_right, hef', heI, herm_zero_right] at h3
    rw [herm_add_right, herm_smul_right, herm_smul_right, hf'I, hfe,
      herm_zero_right] at h4
    refine ⟨?_, ?_⟩
    · have : ι α = 0 := by linear_combination h3
      simpa using congrArg ι this
    · have : ι β = 0 := by linear_combination h4
      simpa using congrArg ι this
  have hrat := ratio_fixed_of_three (ρ := ρ) (t := -c₀) (by rw [map_neg, hρc]) (neg_ne_zero.mpr hc0)
    hr₁ hr₂ hr₃ hμ₁ hμ₂ hμ₃ hc₁ hc₂ hc₃ hx hind
  have hργ' : ρ (ι γ) = ι γ := by rw [C.comm, hργ]
  refine ⟨c₂, hc₂, ⟨μ₂, hμ₂, hr₂⟩, ?_⟩
  refine ⟨(ι γ * (c₁ / c₂)) • μ₁, ratv_smul (by rw [map_mul, hργ', hrat]) hμ₁, ?_⟩
  rw [hfrow, rowv_smul, hr₁, smul_smul, smul_smul]
  congr 1
  field_simp

omit C in
theorem onLine_trans {n : ℕ} {c c' : K} {v w : Fin n → K} (hv : OnLine ρ c v)
    (hv' : OnLine ρ c' v) (hv0 : v ≠ 0) (hw : OnLine ρ c w) : OnLine ρ c' w := by
  obtain ⟨μ, hμ, rfl⟩ := hv
  obtain ⟨μ', hμ', h'⟩ := hv'
  obtain ⟨ν, hν, rfl⟩ := hw
  obtain ⟨i, hi⟩ : ∃ i, μ i ≠ 0 := by
    by_contra hcon
    push Not at hcon
    apply hv0
    funext i
    simp [hcon i]
  have hc' : c' ≠ 0 := by
    rintro rfl
    apply hv0
    simpa using h'
  have hi' := congrFun h' i
  simp only [Pi.smul_apply, smul_eq_mul] at hi'
  have hcc : ρ (c / c') = c / c' := by
    have hrat : c / c' = μ' i / μ i := by
      field_simp
      linear_combination hi'
    rw [hrat, map_div₀, hμ i, hμ' i]
  refine ⟨(c / c') • ν, fun j => ?_, ?_⟩
  · simp [map_mul, hcc, hν j]
  · funext j
    simp only [Pi.smul_apply, smul_eq_mul]
    field_simp

theorem exists_ratline (hall : AllNorm ι ρ M) (B : IsoBasis ι ρ) (hM : ∀ z, ∃ y, M *ᵥ y = z) :
    ∃ c : K, c ≠ 0 ∧ ∀ k, OnLine ρ c (rowv ι M (B.g k)) := by
  have hrow0 : ∀ k, rowv ι M (B.g k) ≠ 0 := by
    intro k h
    have h0 := (rowv_eq_zero_iff M hM _).mp h
    obtain ⟨l, hl⟩ := exists_ne k
    have h2 := B.nonorth k l hl.symm
    rw [h0] at h2
    simp at h2
  obtain ⟨c, hc, h0, h1⟩ := line_pair C M hall B hM (B.rat 0) (B.rat 1) (B.iso 0) (B.iso 1)
    (B.nonorth 0 1 (by decide))
  obtain ⟨c', hc', h1', h2'⟩ := line_pair C M hall B hM (B.rat 1) (B.rat 2) (B.iso 1) (B.iso 2)
    (B.nonorth 1 2 (by decide))
  have h2 : OnLine ρ c (rowv ι M (B.g 2)) := onLine_trans (v := rowv ι M (B.g 1)) h1' h1
    (hrow0 1) h2'
  exact ⟨c, hc, fun k => by fin_cases k; exacts [h0, h1, h2]⟩

theorem exists_irrational_pair (B : IsoBasis ι ρ) (hM : ∀ z, ∃ y, M *ᵥ y = z)
    (hnot : ¬ ∃ c : K, c ≠ 0 ∧ ∀ i j, ρ (c * M i j) = c * M i j) :
    ∃ a b : Fin 3 → K, Ratv ρ a ∧ Ratv ρ b ∧ herm ι a a = 0 ∧ herm ι b b = 0 ∧
      ρ (ι (Bf ι M a b) * Bf ι M a b) ≠ ι (Bf ι M a b) * Bf ι M a b := by
  by_contra hcon
  push Not at hcon
  have hall : AllNorm ι ρ M := fun a b ha hb haI hbI => hcon a b ha hb haI hbI
  obtain ⟨c, hc, hline⟩ := exists_ratline C M hall B hM
  apply hnot
  refine ⟨c⁻¹, inv_ne_zero hc, fun i j => ?_⟩
  obtain ⟨κ, hκ, hκs⟩ := B.span i
  have hMij : M i j = rowv ι M (Pi.single i 1) j := by
    simp [rowv, Bf, herm_single_left]
  have hrow : rowv ι M (Pi.single i 1) j = c * ∑ k, ι (κ k) * (hline k).choose j := by
    rw [hκs, rowv_sum]
    simp only [Finset.sum_apply, Pi.smul_apply, smul_eq_mul, Finset.mul_sum]
    refine Finset.sum_congr rfl fun k _ => ?_
    have := congrFun (hline k).choose_spec.2 j
    simp only [Pi.smul_apply, smul_eq_mul] at this
    rw [this]
    ring
  have hν : ρ (∑ k, ι (κ k) * (hline k).choose j) = ∑ k, ι (κ k) * (hline k).choose j := by
    rw [map_sum]
    refine Finset.sum_congr rfl fun k _ => ?_
    rw [map_mul, C.comm, hκ k, (hline k).choose_spec.1 j]
  rw [hMij, hrow, ← mul_assoc, inv_mul_cancel₀ hc, one_mul]
  exact hν

end CFSG.HardMathSupport.Solomon.Coordinator.BGL
