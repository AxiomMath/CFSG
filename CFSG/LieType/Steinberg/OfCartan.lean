module

public import CFSG.LieType.Steinberg.Basic
public import CFSG.LieType.RootSystem.Parabolic

public section

namespace CFSG.LieType.Steinberg

namespace OfCartan

open CFSG.LieType.RootSystem

variable {I : Type} [Fintype I] [DecidableEq I]

omit [DecidableEq I] in
private theorem ht_sub (v v' : I → ℤ) : ht (v - v') = ht v - ht v' := by
  simp [ht, Finset.sum_sub_distrib]

omit [DecidableEq I] in
private theorem ht_add (v v' : I → ℤ) : ht (v + v') = ht v + ht v' := by
  simp [ht, Finset.sum_add_distrib]

omit [DecidableEq I] in
private theorem ht_two_nsmul (v : I → ℤ) : ht (2 • v) = 2 * ht v := by
  rw [two_nsmul, ht_add, two_mul]

omit [DecidableEq I] in
theorem sum_toRat (v : I → ℤ) : ∑ k, toRat v k = (ht v : ℚ) := by
  simp [ht]

omit [DecidableEq I] in
theorem ht_eq_mul_of_toRat_eq_smul {x y : I → ℤ} {t : ℚ} (h : toRat x = t • toRat y) :
    (ht x : ℚ) = t * ht y := by
  rw [← sum_toRat, ← sum_toRat, h, Finset.mul_sum]
  simp

variable {A : Matrix I I ℤ} (hA : TauCeti.IsFiniteType A)

theorem ht_weylAction_single_ne_zero (w : (coxeterMatrix hA).Group) (i : I) :
    ht (weylAction hA w (Pi.single i 1)) ≠ 0 := by
  have hne := weylAction_single_ne_zero hA w i
  rcases weylAction_single_nonneg_or_nonpos hA w i with h | h
  · have := one_le_sum_of_nonneg h hne
    simp only [ht]
    omega
  · have := one_le_sum_of_nonneg (neg_nonneg.mpr h) (neg_ne_zero.mpr hne)
    simp only [Pi.neg_apply, Finset.sum_neg_distrib] at this
    simp only [ht]
    omega

theorem weylAction_wordProd (ω : List I) (v : I → ℤ) :
    weylAction hA ((coxeterMatrix hA).toCoxeterSystem.wordProd ω) v =
      wordAct (fun i => (reflection A i).toAddMonoidHom) ω v := by
  induction ω with
  | nil => simp [wordAct]
  | cons i ω ih =>
    rw [CoxeterSystem.wordProd_cons, weylAction_mul_apply, ih, weylAction_simple]
    simp [wordAct]

theorem neg_mem_roots {D : Set I} {γ : I → ℤ} (hγ : γ ∈ roots hA D) : -γ ∈ roots hA D := by
  rcases hγ with ⟨w, i, rfl⟩ | ⟨w, i, hi, rfl⟩
  · exact Or.inl ⟨w * (coxeterMatrix hA).toCoxeterSystem.simple i, i, by
      rw [weylAction_mul_apply, weylAction_simple_single, map_neg]⟩
  · exact Or.inr ⟨w * (coxeterMatrix hA).toCoxeterSystem.simple i, i, hi, by
      rw [weylAction_mul_apply, weylAction_simple_single, map_neg, smul_neg]⟩

theorem eq_one_or_eq_neg_one_of_weylAction_eq_smul {v : (coxeterMatrix hA).Group} {i j : I}
    {c : ℤ} (h : weylAction hA v (Pi.single j 1) = c • Pi.single i 1) : c = 1 ∨ c = -1 := by
  have h1 := weylAction_inv_apply_apply hA v (Pi.single j 1)
  rw [h, map_zsmul] at h1
  have h2 := congrFun h1 j
  simp only [Pi.smul_apply, smul_eq_mul, Pi.single_eq_same] at h2
  exact Int.eq_one_or_neg_one_of_mul_eq_one h2

theorem eq_or_eq_neg_of_smul_eq_smul (w w' : (coxeterMatrix hA).Group) (i j : I) {p q : ℤ}
    (hq : q ≠ 0)
    (h : p • weylAction hA w (Pi.single i 1) = q • weylAction hA w' (Pi.single j 1)) :
    weylAction hA w' (Pi.single j 1) = weylAction hA w (Pi.single i 1) ∨
      weylAction hA w' (Pi.single j 1) = -weylAction hA w (Pi.single i 1) := by
  have h1 : p • (Pi.single i 1 : I → ℤ) = q • weylAction hA (w⁻¹ * w') (Pi.single j 1) := by
    have := congrArg (weylAction hA w⁻¹) h
    rwa [map_zsmul, map_zsmul, weylAction_inv_apply_apply, ← weylAction_mul_apply] at this
  have h2 : weylAction hA (w⁻¹ * w') (Pi.single j 1) =
      weylAction hA (w⁻¹ * w') (Pi.single j 1) i • Pi.single i 1 := by
    funext k
    by_cases hk : k = i
    · subst hk
      simp
    · have := congrFun h1 k
      simp only [Pi.smul_apply, smul_eq_mul, Pi.single_eq_of_ne hk, mul_zero] at this ⊢
      exact (mul_eq_zero.mp this.symm).resolve_left hq
  have hw' : weylAction hA w' (Pi.single j 1) =
      weylAction hA w (weylAction hA (w⁻¹ * w') (Pi.single j 1)) := by
    rw [weylAction_mul_apply, weylAction_apply_inv_apply]
  rcases eq_one_or_eq_neg_one_of_weylAction_eq_smul hA h2 with h3 | h3
  · left
    rw [hw', h2, h3, one_smul]
  · right
    rw [hw', h2, h3, neg_one_smul, map_neg]

theorem exists_eq_of_indiv {D : Set I} {γ : I → ℤ} (hγ : γ ∈ roots hA D)
    (h : ∀ δ ∈ roots hA D, γ ≠ 2 • δ) :
    ∃ (w : (coxeterMatrix hA).Group) (i : I), γ = weylAction hA w (Pi.single i 1) := by
  rcases hγ with ⟨w, i, rfl⟩ | ⟨w, i, -, rfl⟩
  · exact ⟨w, i, rfl⟩
  · exact absurd rfl (h _ (Or.inl ⟨w, i, rfl⟩))

omit [Fintype I] [DecidableEq I] in
private theorem zsmul_two_nsmul (p : ℤ) (v : I → ℤ) : p • (2 • v) = (p * 2) • v := by
  rw [two_nsmul, ← two_zsmul, smul_smul]

omit [Fintype I] [DecidableEq I] in
private theorem two_nsmul_neg (v : I → ℤ) : (2 • (-v) : I → ℤ) = -(2 • v) := smul_neg 2 v

theorem proportional {D : Set I} {γ δ : I → ℤ} (hγ : γ ∈ roots hA D) (hδ : δ ∈ roots hA D)
    (h : ¬ LinIndepPair γ δ) :
    γ = δ ∨ γ = -δ ∨ γ = 2 • δ ∨ γ = -(2 • δ) ∨ δ = 2 • γ ∨ δ = -(2 • γ) := by
  simp only [LinIndepPair, not_forall, not_and_or] at h
  obtain ⟨a, b, hab, hne⟩ := h
  have hγ0 := ne_zero_of_mem_roots hA D hγ
  have hb : b ≠ 0 := by
    rintro rfl
    rw [zero_smul, add_zero] at hab
    have ha := (smul_eq_zero.mp hab).resolve_right hγ0
    exact hne.elim (· ha) (· rfl)
  have hab' : a • γ = (-b) • δ := by
    rw [neg_smul]
    exact eq_neg_of_add_eq_zero_left hab
  have hb' : -b ≠ 0 := neg_ne_zero.mpr hb
  have hb2 : -b * 2 ≠ 0 := mul_ne_zero hb' two_ne_zero
  rcases hγ with ⟨w, i, rfl⟩ | ⟨w, i, -, rfl⟩ <;> rcases hδ with ⟨w', j, rfl⟩ | ⟨w', j, -, rfl⟩
  · rcases eq_or_eq_neg_of_smul_eq_smul hA w w' i j hb' hab' with h | h
    · exact Or.inl h.symm
    · exact Or.inr (Or.inl (by rw [h, neg_neg]))
  · rw [zsmul_two_nsmul] at hab'
    rcases eq_or_eq_neg_of_smul_eq_smul hA w w' i j hb2 hab' with h | h
    · exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inl (by rw [h])))))
    · exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (by rw [h, two_nsmul_neg])))))
  · rw [zsmul_two_nsmul] at hab'
    rcases eq_or_eq_neg_of_smul_eq_smul hA w w' i j hb' hab' with h | h
    · exact Or.inr (Or.inr (Or.inl (by rw [h])))
    · exact Or.inr (Or.inr (Or.inr (Or.inl (by rw [← two_nsmul_neg, h, neg_neg]))))
  · rw [zsmul_two_nsmul, zsmul_two_nsmul] at hab'
    rcases eq_or_eq_neg_of_smul_eq_smul hA w w' i j hb2 hab' with h | h
    · exact Or.inl (by rw [h])
    · exact Or.inr (Or.inl (by rw [h, two_nsmul_neg, neg_neg]))

theorem form_weylAction_single_left (w : (coxeterMatrix hA).Group) (i : I) (v : I → ℤ) :
    form hA (toRat (weylAction hA w (Pi.single i 1))) (toRat v) =
      symmetrizer hA i * (coroot A i (weylAction hA w⁻¹ v) : ℚ) := by
  conv_lhs => rw [← weylAction_apply_inv_apply hA w v]
  rw [form_weylAction, toRat_single, form_single_left, coroot_apply]
  push_cast
  simp

theorem form_weylAction_single_self (w : (coxeterMatrix hA).Group) (i : I) :
    form hA (toRat (weylAction hA w (Pi.single i 1))) (toRat (weylAction hA w (Pi.single i 1))) =
      2 * symmetrizer hA i := by
  rw [form_weylAction, toRat_single, form_single_single]

theorem coroot_mul_form_self (w : (coxeterMatrix hA).Group) (i : I) (v : I → ℤ) :
    (coroot A i (weylAction hA w⁻¹ v) : ℚ) *
        form hA (toRat (weylAction hA w (Pi.single i 1)))
          (toRat (weylAction hA w (Pi.single i 1))) =
      2 * form hA (toRat (weylAction hA w (Pi.single i 1))) (toRat v) := by
  rw [form_weylAction_single_self, form_weylAction_single_left]
  ring

theorem weylAction_conj_simple (w : (coxeterMatrix hA).Group) (i : I) (v : I → ℤ) :
    weylAction hA (w * (coxeterMatrix hA).toCoxeterSystem.simple i * w⁻¹) v =
      v - coroot A i (weylAction hA w⁻¹ v) • weylAction hA w (Pi.single i 1) := by
  rw [weylAction_mul_apply, weylAction_mul_apply, weylAction_simple, reflection_apply_coroot,
    map_sub, map_zsmul, weylAction_apply_inv_apply]

theorem toRat_weylAction_single_ne_zero (w : (coxeterMatrix hA).Group) (i : I) :
    toRat (weylAction hA w (Pi.single i 1)) ≠ 0 := fun h =>
  weylAction_single_ne_zero hA w i (toRat_injective (by rw [h, map_zero]))

theorem sq_form_lt {x y : I → ℚ} (hy : y ≠ 0) (hxy : ∀ t : ℚ, x ≠ t • y) :
    form hA x y ^ 2 < form hA x x * form hA y y := by
  have hyy := form_pos hA hy
  set t := form hA x y / form hA y y
  have h := form_pos hA (sub_ne_zero.mpr (hxy t))
  simp only [map_sub, map_smul, LinearMap.sub_apply, LinearMap.smul_apply, smul_eq_mul] at h
  rw [form_comm hA y x] at h
  have ht : t * form hA y y = form hA x y := div_mul_cancel₀ _ hyy.ne'
  have h' : t * form hA x y * form hA y y = form hA x y ^ 2 := by
    rw [mul_right_comm, ht]
    ring
  nlinarith

theorem mul_lt_four {x y : I → ℚ} (hx : x ≠ 0) (hy : y ≠ 0) (hxy : ∀ t : ℚ, x ≠ t • y)
    {a b : ℤ} (ha : (a : ℚ) * form hA x x = 2 * form hA x y)
    (hb : (b : ℚ) * form hA y y = 2 * form hA x y) : a * b < 4 := by
  have hxx := form_pos hA hx
  have hyy := form_pos hA hy
  have hcs := sq_form_lt hA hy hxy
  have h : ((a * b : ℤ) : ℚ) * (form hA x x * form hA y y) = 4 * form hA x y ^ 2 := by
    push_cast
    linear_combination (b * form hA y y) * ha + (2 * form hA x y) * hb
  have : ((a * b : ℤ) : ℚ) < 4 := by
    by_contra hc
    push Not at hc
    nlinarith [mul_pos hxx hyy]
  exact_mod_cast this

theorem le_three {x y : I → ℚ} (hx : x ≠ 0) (hy : y ≠ 0) (hxy : ∀ t : ℚ, x ≠ t • y)
    {a b : ℤ} (ha : (a : ℚ) * form hA x x = 2 * form hA x y)
    (hb : (b : ℚ) * form hA y y = 2 * form hA x y) : a ≤ 3 := by
  have hlt := mul_lt_four hA hx hy hxy ha hb
  have hxx := form_pos hA hx
  have hyy := form_pos hA hy
  by_contra h4
  push Not at h4
  have ha' : (4 : ℚ) ≤ a := by exact_mod_cast h4
  have hb' : (0 : ℚ) < b := by nlinarith
  have hb1 : 1 ≤ b := by exact_mod_cast hb'
  nlinarith

theorem form_nonpos_of_ht_eq (w w' : (coxeterMatrix hA).Group) (i k : I)
    (hht : ht (weylAction hA w (Pi.single i 1)) = ht (weylAction hA w' (Pi.single k 1)))
    (hne : weylAction hA w (Pi.single i 1) ≠ weylAction hA w' (Pi.single k 1)) :
    form hA (toRat (weylAction hA w (Pi.single i 1)))
      (toRat (weylAction hA w' (Pi.single k 1))) ≤ 0 := by
  set cs := (coxeterMatrix hA).toCoxeterSystem
  set δ := weylAction hA w (Pi.single i 1) with hδ
  set ε := weylAction hA w' (Pi.single k 1) with hε
  by_contra hpos
  push Not at hpos
  have hδ0 : toRat δ ≠ 0 := toRat_weylAction_single_ne_zero hA w i
  have hε0 : toRat ε ≠ 0 := toRat_weylAction_single_ne_zero hA w' k
  have hprop : ∀ t : ℚ, toRat δ ≠ t • toRat ε := by
    intro t hts
    have h1 := ht_eq_mul_of_toRat_eq_smul hts
    rw [hht] at h1
    have hε1 : (ht ε : ℚ) ≠ 0 := by exact_mod_cast ht_weylAction_single_ne_zero hA w' k
    have ht1 : t = 1 := by
      have : (t - 1) * (ht ε : ℚ) = 0 := by linear_combination -h1
      exact sub_eq_zero.mp ((mul_eq_zero.mp this).resolve_right hε1)
    rw [ht1, one_smul] at hts
    exact hne (toRat_injective hts)
  have h1 := coroot_mul_form_self hA w i ε
  have h2 := coroot_mul_form_self hA w' k δ
  rw [form_comm hA (toRat ε) (toRat δ)] at h2
  have hlt := mul_lt_four hA hδ0 hε0 hprop h1 h2
  have hδδ := form_pos hA hδ0
  have hεε := form_pos hA hε0
  have hc1 : (0 : ℚ) < coroot A i (weylAction hA w⁻¹ ε) := by nlinarith
  have hc2 : (0 : ℚ) < coroot A k (weylAction hA w'⁻¹ δ) := by nlinarith
  have hc1' : 0 < coroot A i (weylAction hA w⁻¹ ε) := by exact_mod_cast hc1
  have hc2' : 0 < coroot A k (weylAction hA w'⁻¹ δ) := by exact_mod_cast hc2
  have hone : coroot A i (weylAction hA w⁻¹ ε) = 1 ∨ coroot A k (weylAction hA w'⁻¹ δ) = 1 := by
    by_contra h
    push Not at h
    have : 2 ≤ coroot A i (weylAction hA w⁻¹ ε) := by omega
    have : 2 ≤ coroot A k (weylAction hA w'⁻¹ δ) := by omega
    nlinarith
  rcases hone with h | h
  ·
    have hs := weylAction_conj_simple hA w i ε
    rw [h, one_smul] at hs
    apply ht_weylAction_single_ne_zero hA (w * cs.simple i * w⁻¹ * w') k
    rw [weylAction_mul_apply, ← hε, hs, ht_sub, hht, sub_self]
  ·
    have hs := weylAction_conj_simple hA w' k δ
    rw [h, one_smul] at hs
    apply ht_weylAction_single_ne_zero hA (w' * cs.simple k * w'⁻¹ * w) i
    rw [weylAction_mul_apply, ← hδ, hs, ht_sub, hht, sub_self]

theorem pairing_le_three (w w' : (coxeterMatrix hA).Group) (k j : I)
    (hprop : ∀ t : ℚ, toRat (weylAction hA w (Pi.single k 1)) ≠
      t • toRat (weylAction hA w' (Pi.single j 1))) :
    coroot A k (weylAction hA w⁻¹ (weylAction hA w' (Pi.single j 1))) ≤ 3 := by
  have h2 := coroot_mul_form_self hA w' j (weylAction hA w (Pi.single k 1))
  rw [form_comm hA (toRat (weylAction hA w' (Pi.single j 1)))
    (toRat (weylAction hA w (Pi.single k 1)))] at h2
  exact le_three hA (toRat_weylAction_single_ne_zero hA w k)
    (toRat_weylAction_single_ne_zero hA w' j) hprop (coroot_mul_form_self hA w k _) h2

theorem not_proportional_of_ht_eq_two_mul (w w' : (coxeterMatrix hA).Group) (k j : I)
    (hh : ht (weylAction hA w' (Pi.single j 1)) = 2 * ht (weylAction hA w (Pi.single k 1)))
    (hne : weylAction hA w' (Pi.single j 1) ≠ 2 • weylAction hA w (Pi.single k 1)) :
    ∀ t : ℚ, toRat (weylAction hA w (Pi.single k 1)) ≠
      t • toRat (weylAction hA w' (Pi.single j 1)) := by
  intro t hts
  have h1 := ht_eq_mul_of_toRat_eq_smul hts
  rw [hh] at h1
  push_cast at h1
  have hζ1 : (ht (weylAction hA w (Pi.single k 1)) : ℚ) ≠ 0 := by
    exact_mod_cast ht_weylAction_single_ne_zero hA w k
  have ht2 : 2 * t = 1 := by
    have : (2 * t - 1) * (ht (weylAction hA w (Pi.single k 1)) : ℚ) = 0 := by
      linear_combination -h1
    exact sub_eq_zero.mp ((mul_eq_zero.mp this).resolve_right hζ1)
  have h2 : toRat (weylAction hA w' (Pi.single j 1)) =
      (2 : ℚ) • toRat (weylAction hA w (Pi.single k 1)) := by
    rw [hts, smul_smul, ht2, one_smul]
  apply hne
  apply toRat_injective
  rw [h2, map_nsmul, two_smul, two_nsmul]

theorem sum_ne_two_smul {D : Set I} {δ δ' ε : I → ℤ} (hδ : δ ∈ roots hA D)
    (hδ' : δ' ∈ roots hA D) (hε : ε ∈ roots hA D) (hht : ht δ = ht δ') (hne : δ ≠ δ')
    (hδi : ∀ ζ ∈ roots hA D, δ ≠ 2 • ζ) (hδ'i : ∀ ζ ∈ roots hA D, δ' ≠ 2 • ζ) :
    δ + δ' ≠ 2 • ε := by
  obtain ⟨w₁, a, rfl⟩ := exists_eq_of_indiv hA hδ hδi
  obtain ⟨w₂, b, rfl⟩ := exists_eq_of_indiv hA hδ' hδ'i
  intro hsum
  have hhtsum := congrArg ht hsum
  rw [ht_add, ht_two_nsmul] at hhtsum
  rcases hε with ⟨w, k, rfl⟩ | ⟨w, k, -, rfl⟩
  ·
    have hne1 : weylAction hA w₁ (Pi.single a 1) ≠ weylAction hA w (Pi.single k 1) := by
      intro h
      apply hne
      rw [two_nsmul, ← h] at hsum
      exact (add_left_cancel hsum).symm
    have hne2 : weylAction hA w₂ (Pi.single b 1) ≠ weylAction hA w (Pi.single k 1) := by
      intro h
      apply hne
      rw [two_nsmul, ← h] at hsum
      exact add_right_cancel hsum
    have h1 := form_nonpos_of_ht_eq hA w₁ w a k (by omega) hne1
    have h2 := form_nonpos_of_ht_eq hA w₂ w b k (by omega) hne2
    have hεε := form_weylAction_single_self hA w k
    have hsum' := congrArg (fun v => form hA (toRat v) (toRat (weylAction hA w (Pi.single k 1))))
      hsum
    simp only [map_add, LinearMap.add_apply, two_nsmul] at hsum'
    have := symmetrizer_pos hA k
    linarith
  ·
    rw [ht_two_nsmul] at hhtsum
    have hζ : weylAction hA w (Pi.single k 1) ∈ roots hA D := Or.inl ⟨w, k, rfl⟩
    have h1 := pairing_le_three hA w w₁ k a (not_proportional_of_ht_eq_two_mul hA w w₁ k a
      (by omega) (hδi _ hζ))
    have h2 := pairing_le_three hA w w₂ k b (not_proportional_of_ht_eq_two_mul hA w w₂ k b
      (by omega) (hδ'i _ hζ))
    have h8 : coroot A k (weylAction hA w⁻¹ (weylAction hA w₁ (Pi.single a 1))) +
        coroot A k (weylAction hA w⁻¹ (weylAction hA w₂ (Pi.single b 1))) = 8 := by
      rw [← map_add, ← map_add, hsum]
      simp only [map_nsmul, weylAction_inv_apply_apply, coroot_single, hA.apply_self]
      norm_num
    omega

end OfCartan

open CFSG.LieType.RootSystem in
@[expose] noncomputable def RootSystem.ofCartan {I : Type} [Fintype I] [DecidableEq I]
    {A : Matrix I I ℤ} (hA : TauCeti.IsFiniteType A) (D : Set I) : RootSystem I where
  roots := CFSG.LieType.RootSystem.roots hA D
  finite_roots := CFSG.LieType.RootSystem.finite_roots hA D
  zero_notMem h := ne_zero_of_mem_roots hA D h rfl
  neg_mem _ h := OfCartan.neg_mem_roots hA h
  sign _ h := (nonneg_or_nonpos hA D h).imp (fun h j => h j) (fun h j => h j)
  single_mem i := Or.inl ⟨1, i, by simp⟩
  proportional _ hγ _ hδ h := OfCartan.proportional hA hγ hδ h
  refl i := (reflection A i).toAddMonoidHom
  refl_apply_of_ne i v _ hj := reflection_apply_of_ne A hj v
  refl_single i := reflection_single_self (hA.apply_self i)
  refl_refl i v := by
    have := LinearMap.congr_fun (reflection_mul_self (hA.apply_self i)) v
    simpa using this
  refl_mem i _ hγ := by
    have := weylAction_mem_roots hA ((coxeterMatrix hA).toCoxeterSystem.simple i) hγ
    rw [weylAction_simple] at this
    simpa using this
  exists_word _ hγ h := by
    obtain ⟨w, i, rfl⟩ := OfCartan.exists_eq_of_indiv hA hγ h
    obtain ⟨ω, rfl⟩ := (coxeterMatrix hA).toCoxeterSystem.wordProd_surjective w
    exact ⟨ω, i, OfCartan.weylAction_wordProd hA ω _⟩
  sum_ne_two_smul _ hδ _ hδ' _ hε _ hht hne hδi hδ'i :=
    OfCartan.sum_ne_two_smul hA hδ hδ' hε hht hne hδi hδ'i

section OfCartan

variable {I : Type} [Fintype I] [DecidableEq I] {A : Matrix I I ℤ} (hA : TauCeti.IsFiniteType A)
  (D : Set I)

@[simp] theorem RootSystem.ofCartan_roots :
    (RootSystem.ofCartan hA D).roots = CFSG.LieType.RootSystem.roots hA D := rfl

@[simp] theorem RootSystem.ofCartan_refl_apply (i : I) (v : I → ℤ) :
    (RootSystem.ofCartan hA D).refl i v = CFSG.LieType.RootSystem.reflection A i v := rfl

end OfCartan

end CFSG.LieType.Steinberg
