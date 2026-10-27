module

public import CFSG.LocalAnalysis.GLTheoremA.CatC.KD264LieRowY1KerA6UWittSel
public import CFSG.LocalAnalysis.GLTheoremA.CatC.KD264LieRowY1KerA6UAssem

public section

namespace CFSG.LocalAnalysis.GLTheoremA.KD264Lie

open Matrix CFSG.ClassicalGroups.UnitaryFlag CFSG.LocalAnalysis.ComponentInitial

variable {p f : ℕ} {K : Type} [Field K]

@[expose] noncomputable def monoM (e : Fin 6 ≃ Fin 6) (c : Fin 6 → K) : Matrix (Fin 6) (Fin 6) K :=
  Matrix.of fun k l => if k = e l then c l else 0

@[expose] noncomputable def monoN (e : Fin 6 ≃ Fin 6) (c : Fin 6 → K) : Matrix (Fin 6) (Fin 6) K :=
  Matrix.of fun k l => if k = e.symm l then (c (e.symm l))⁻¹ else 0

theorem monoM_mul_monoN (e : Fin 6 ≃ Fin 6) (c : Fin 6 → K) (hc : ∀ j, c j ≠ 0) :
    monoM e c * monoN e c = 1 := by
  ext a b
  rw [Matrix.mul_apply, Finset.sum_eq_single (e.symm b)]
  · by_cases hab : a = b
    · subst hab
      simp [monoM, monoN, hc]
    · simp [monoM, monoN, hab]
  · intro k _ hk
    simp [monoN, hk]
  · intro hn
    exact absurd (Finset.mem_univ _) hn

theorem monoN_mul_monoM (e : Fin 6 ≃ Fin 6) (c : Fin 6 → K) (hc : ∀ j, c j ≠ 0) :
    monoN e c * monoM e c = 1 := by
  ext a b
  rw [Matrix.mul_apply, Finset.sum_eq_single (e b)]
  · by_cases hab : a = b
    · subst hab
      simp [monoM, monoN, hc]
    · simp [monoM, monoN, hab]
  · intro k _ hk
    simp [monoM, hk]
  · intro hn
    exact absurd (Finset.mem_univ _) hn

@[expose] noncomputable def monoGL (e : Fin 6 ≃ Fin 6) (c : Fin 6 → K) (hc : ∀ j, c j ≠ 0) :
    GL (Fin 6) K :=
  ⟨monoM e c, monoN e c, monoM_mul_monoN e c hc, monoN_mul_monoM e c hc⟩

theorem monoGL_val (e : Fin 6 ≃ Fin 6) (c : Fin 6 → K) (hc : ∀ j, c j ≠ 0) :
    ((monoGL e c hc : GL (Fin 6) K) : Matrix (Fin 6) (Fin 6) K) = monoM e c := rfl

theorem monoGL_inv_val (e : Fin 6 ≃ Fin 6) (c : Fin 6 → K) (hc : ∀ j, c j ≠ 0) :
    (((monoGL e c hc)⁻¹ : GL (Fin 6) K) : Matrix (Fin 6) (Fin 6) K) = monoN e c := rfl

theorem hermT_monoM (h : UnitaryFieldData p f K) (e : Fin 6 ≃ Fin 6) (c : Fin 6 → K) (j i : Fin 6) :
    hermT h (monoM e c) j i = if i = e j then h.bar (c j) else 0 := by
  unfold hermT monoM
  by_cases hij : i = e j
  · simp [hij]
  · simp [hij]

theorem monoM_gram_entry (h : UnitaryFieldData p f K) (e : Fin 6 ≃ Fin 6) (c : Fin 6 → K)
    (G : Matrix (Fin 6) (Fin 6) K) (j l : Fin 6) :
    (hermT h (monoM e c) * G * monoM e c) j l = h.bar (c j) * G (e j) (e l) * c l := by
  rw [Matrix.mul_apply, Finset.sum_eq_single (e l)]
  · have h1 : (hermT h (monoM e c) * G) j (e l) = h.bar (c j) * G (e j) (e l) := by
      rw [Matrix.mul_apply, Finset.sum_eq_single (e j)]
      · simp [hermT_monoM]
      · intro i _ hi
        simp [hermT_monoM, hi]
      · intro hn
        exact absurd (Finset.mem_univ _) hn
    have hM : monoM e c (e l) l = c l := by simp [monoM]
    rw [h1, hM]
  · intro k _ hk
    simp [monoM, hk]
  · intro hn
    exact absurd (Finset.mem_univ _) hn

theorem monoN_diag_monoM (e : Fin 6 ≃ Fin 6) (c : Fin 6 → K) (hc : ∀ j, c j ≠ 0) (d : Fin 6 → K) :
    monoN e c * Matrix.diagonal d * monoM e c = Matrix.diagonal (fun j => d (e j)) := by
  ext a b
  rw [Matrix.mul_apply, Finset.sum_eq_single (e b)]
  · by_cases hab : a = b
    · subst hab
      simp [monoN, monoM, hc]
      rw [mul_comm ((c a)⁻¹ * d (e a)) (c a), ← mul_assoc, mul_inv_cancel₀ (hc a), one_mul]
    · simp [monoN, monoM, hab, Matrix.diagonal_apply]
  · intro k _ hk
    simp [monoM, hk]
  · intro hn
    exact absurd (Finset.mem_univ _) hn

theorem hermT_hermT (h : UnitaryFieldData p f K) (X : Matrix (Fin 6) (Fin 6) K) :
    hermT h (hermT h X) = X := by
  unfold hermT
  ext i j
  simp [bar_bar_of]

theorem gram_herm (h : UnitaryFieldData p f K) (T : GL (Fin 6) K) (i j : Fin 6) :
    gramT h T j i = h.bar (gramT h T i j) := by
  have hG : hermT h (gramT h T) = gramT h T := by
    unfold gramT
    rw [hermT_mul, hermT_hermT]
  have := congrFun (congrFun hG j) i
  unfold hermT at this
  simpa using this.symm

theorem trivC_of_invC_self (P : Subgroup (GL (Fin 6) K)) (T : GL (Fin 6) K)
    (hdiag : ∀ g ∈ P, ∀ i j, i ≠ j →
      ((T⁻¹ * g * T : GL (Fin 6) K) : Matrix (Fin 6) (Fin 6) K) i j = 0)
    (hpow : ∀ g ∈ P, g ^ 3 = 1) {i : Fin 6} (hI : InvC P T i i) : TrivC P T i := by
  intro g hg
  have h2 := hI g hg
  have h3 : chT T g i ^ 3 = 1 := by
    rw [← chT_pow P T hdiag hg i 3, hpow g hg, chT_one]
  have key : chT T g i ^ 3 = chT T g i := by
    rw [show chT T g i ^ 3 = (chT T g i * chT T g i) * chT T g i by ring, h2, one_mul]
  rw [h3] at key
  exact key.symm

theorem gram_table (h : UnitaryFieldData p f K) (hbar : ∀ x : K, x ^ 3 = 1 → h.bar x = x)
    (P : Subgroup (GL (Fin 6) K)) (T : GL (Fin 6) K)
    (hdiag : ∀ g ∈ P, ∀ i j, i ≠ j →
      ((T⁻¹ * g * T : GL (Fin 6) K) : Matrix (Fin 6) (Fin 6) K) i j = 0)
    (hpow : ∀ g ∈ P, g ^ 3 = 1)
    (hgram : ∀ g ∈ P, hermT h (g : Matrix (Fin 6) (Fin 6) K) * (g : Matrix (Fin 6) (Fin 6) K) = 1)
    (a b : Fin 3 → Fin 6)
    (H1 : ∀ k, ¬ TrivC P T (a k)) (H2 : ∀ k, InvC P T (b k) (a k))
    (H3 : ∀ k l, k ≠ l → ¬ SameC P T (a k) (a l) ∧ ¬ InvC P T (a k) (a l)) :
    (∀ k k', gramT h T (a k) (a k') = 0) ∧ (∀ k k', gramT h T (b k) (b k') = 0) ∧
      (∀ k k', k ≠ k' → gramT h T (a k) (b k') = 0) ∧
      (∀ k k', k ≠ k' → gramT h T (b k) (a k') = 0) ∧
      (∀ k, gramT h T (b k) (a k) = h.bar (gramT h T (a k) (b k))) := by
  have hA : ∀ k, ∀ g ∈ P, chT T g (b k) = (chT T g (a k))⁻¹ :=
    fun k g hg => eq_inv_of_mul_eq_one_left (H2 k g hg)
  have hInvSelf : ∀ k, ¬ InvC P T (a k) (a k) :=
    fun k hI => H1 k (trivC_of_invC_self P T hdiag hpow hI)
  have T1 : ∀ k k', gramT h T (a k) (a k') = 0 := by
    intro k k'
    by_contra hne
    by_cases hkk : k = k'
    · subst hkk
      exact hInvSelf k (invC_of_gram h hbar P T hdiag hgram hpow hne)
    · exact (H3 k k' hkk).2 (invC_of_gram h hbar P T hdiag hgram hpow hne)
  have T3 : ∀ k k', k ≠ k' → gramT h T (a k) (b k') = 0 := by
    intro k k' hkk
    by_contra hne
    apply (H3 k k' hkk).1
    intro g hg
    have hI := invC_of_gram h hbar P T hdiag hgram hpow hne g hg
    rw [hA k' g hg] at hI
    exact (mul_inv_eq_one₀ (chT_ne_zero P T hdiag hpow hg (a k'))).mp hI
  have key22 : ∀ k k', gramT h T (b k) (b k') ≠ 0 → InvC P T (a k) (a k') := by
    intro k k' hne g hg
    have e1 := invC_of_gram h hbar P T hdiag hgram hpow hne g hg
    rw [hA k g hg, hA k' g hg, ← mul_inv, inv_eq_one] at e1
    exact e1
  have T2 : ∀ k k', gramT h T (b k) (b k') = 0 := by
    intro k k'
    by_contra hne
    by_cases hkk : k = k'
    · subst hkk
      exact hInvSelf k (key22 k k hne)
    · exact (H3 k k' hkk).2 (key22 k k' hne)
  have T4 : ∀ k k', k ≠ k' → gramT h T (b k) (a k') = 0 := by
    intro k k' hkk
    rw [gram_herm h T (a k') (b k), T3 k' k (Ne.symm hkk), map_zero]
  exact ⟨T1, T2, T3, T4, fun k => gram_herm h T (a k) (b k)⟩

theorem perm_inj (h : UnitaryFieldData p f K) (P : Subgroup (GL (Fin 6) K)) (T : GL (Fin 6) K)
    (hdiag : ∀ g ∈ P, ∀ i j, i ≠ j →
      ((T⁻¹ * g * T : GL (Fin 6) K) : Matrix (Fin 6) (Fin 6) K) i j = 0)
    (hpow : ∀ g ∈ P, g ^ 3 = 1) (a b : Fin 3 → Fin 6)
    (H1 : ∀ k, ¬ TrivC P T (a k)) (H2 : ∀ k, InvC P T (b k) (a k))
    (H3 : ∀ k l, k ≠ l → ¬ SameC P T (a k) (a l) ∧ ¬ InvC P T (a k) (a l)) :
    Function.Injective (![a 0, a 1, a 2, b 0, b 1, b 2] : Fin 6 → Fin 6) := by
  have hA : ∀ k k', a k = a k' → k = k' := by
    intro k k' e
    by_contra hne
    exact (H3 k k' hne).1 (fun g _ => by rw [e])
  have hB : ∀ k k', b k = b k' → k = k' := by
    intro k k' e
    by_contra hne
    apply (H3 k k' hne).1
    intro g hg
    calc chT T g (a k) = (chT T g (b k))⁻¹ := eq_inv_of_mul_eq_one_right (H2 k g hg)
      _ = (chT T g (b k'))⁻¹ := by rw [e]
      _ = chT T g (a k') := (eq_inv_of_mul_eq_one_right (H2 k' g hg)).symm
  have hAB : ∀ k k', a k ≠ b k' := by
    intro k k' e
    by_cases hkk : k = k'
    · subst hkk
      apply H1 k
      apply trivC_of_invC_self P T hdiag hpow
      intro g hg
      have := H2 k g hg
      rw [← e] at this
      exact this
    · apply (H3 k k' hkk).2
      intro g hg
      have := H2 k' g hg
      rw [← e] at this
      exact this
  intro x y hxy
  fin_cases x <;> fin_cases y <;> simp at hxy ⊢ <;> first
    | rfl
    | exact absurd (hA _ _ hxy) (by decide)
    | exact absurd (hB _ _ hxy) (by decide)
    | exact absurd hxy (hAB _ _)
    | exact absurd hxy.symm (hAB _ _)

theorem Dhom_val (x : Fin 3 → mu3U K) (k : Fin 3) :
    ((Dhom K x k : Kˣ) : K) = ((x k : Kˣ) : K) := rfl

theorem witt_normal_form [Finite K] (h : UnitaryFieldData p f K)
    (hbar : ∀ x : K, x ^ 3 = 1 → h.bar x = x)
    (P : Subgroup (GL (Fin 6) K)) (T : GL (Fin 6) K)
    (hdiag : ∀ g ∈ P, ∀ i j, i ≠ j →
      ((T⁻¹ * g * T : GL (Fin 6) K) : Matrix (Fin 6) (Fin 6) K) i j = 0)
    (hcard : Nat.card P = 27) (hpow : ∀ g ∈ P, g ^ 3 = 1)
    (hgram : ∀ g ∈ P, hermT h (g : Matrix (Fin 6) (Fin 6) K) * (g : Matrix (Fin 6) (Fin 6) K) = 1) :
    ∃ R : GL (Fin 6) K,
      hermT h (R : Matrix (Fin 6) (Fin 6) K) * (R : Matrix (Fin 6) (Fin 6) K) = hypJ ∧
      ∀ g ∈ P, ∃ x : Fin 3 → mu3U K, diagGenHom (Dhom K x) = R⁻¹ * g * R := by
  obtain ⟨a, b, H1, H2, H3, H4⟩ := select3 h hbar P T hdiag hcard hpow hgram
  obtain ⟨T1, T2, T3, T4, T5⟩ := gram_table h hbar P T hdiag hpow hgram a b H1 H2 H3
  have hinj := perm_inj h P T hdiag hpow a b H1 H2 H3
  let pm : Fin 6 → Fin 6 := ![a 0, a 1, a 2, b 0, b 1, b 2]
  let e : Fin 6 ≃ Fin 6 := Equiv.ofBijective pm (Finite.injective_iff_bijective.mp hinj)
  let c : Fin 6 → K := ![1, 1, 1, (gramT h T (a 0) (b 0))⁻¹, (gramT h T (a 1) (b 1))⁻¹,
    (gramT h T (a 2) (b 2))⁻¹]
  have hc : ∀ j, c j ≠ 0 := by
    intro j
    fin_cases j <;> simp [c, H4]
  have hRval : ∀ g : GL (Fin 6) K,
      ((((T * monoGL e c hc)⁻¹ * g * (T * monoGL e c hc) : GL (Fin 6) K)) : Matrix (Fin 6) (Fin 6) K) =
        monoN e c * ((T⁻¹ * g * T : GL (Fin 6) K) : Matrix (Fin 6) (Fin 6) K) * monoM e c := by
    intro g
    simp only [Units.val_mul, _root_.mul_inv_rev, monoGL_inv_val, monoGL_val, Matrix.mul_assoc]
  refine ⟨T * monoGL e c hc, ?_, ?_⟩
  · have hval : ((T * monoGL e c hc : GL (Fin 6) K) : Matrix (Fin 6) (Fin 6) K) =
        (T : Matrix (Fin 6) (Fin 6) K) * monoM e c := by
      rw [Units.val_mul, monoGL_val]
    have hstep : hermT h ((T * monoGL e c hc : GL (Fin 6) K) : Matrix (Fin 6) (Fin 6) K) *
        ((T * monoGL e c hc : GL (Fin 6) K) : Matrix (Fin 6) (Fin 6) K) =
        hermT h (monoM e c) * gramT h T * monoM e c := by
      rw [hval, hermT_mul]
      unfold gramT
      simp only [Matrix.mul_assoc]
    rw [hstep]
    ext j l
    rw [monoM_gram_entry]
    fin_cases j <;> fin_cases l <;> simp [e, pm, c, T1, T2, T3, T4, T5, H4, hypJ] <;> rfl
  · intro g hg
    have hdg := conj_eq_diagonal P T hdiag hg
    have hcube : ∀ k, chT T g (a k) ^ 3 = 1 := fun k => by
      rw [← chT_pow P T hdiag hg (a k) 3, hpow g hg, chT_one]
    have hb0 : chT T g (b 0) = (chT T g (a 0))⁻¹ := eq_inv_of_mul_eq_one_left (H2 0 g hg)
    have hb1 : chT T g (b 1) = (chT T g (a 1))⁻¹ := eq_inv_of_mul_eq_one_left (H2 1 g hg)
    have hb2 : chT T g (b 2) = (chT T g (a 2))⁻¹ := eq_inv_of_mul_eq_one_left (H2 2 g hg)
    let x : Fin 3 → mu3U K := fun k =>
      ⟨Units.mk0 (chT T g (a k)) (chT_ne_zero P T hdiag hpow hg (a k)), by
        rw [mem_rootsOfUnity]
        apply Units.ext
        rw [Units.val_pow_eq_pow_val, Units.val_mk0, Units.val_one]
        exact hcube k⟩
    refine ⟨x, ?_⟩
    apply Units.ext
    have hL : ((diagGenHom (Dhom K x) : GL (Fin 6) K) : Matrix (Fin 6) (Fin 6) K) =
        Matrix.diagonal (fun j => chT T g (pm j)) := by
      rw [diagGenHom_apply, diagGen_val]
      congr 1
      funext j
      fin_cases j <;> simp [x, pm, Dhom_val, hb0, hb1, hb2]
    rw [hL, hRval, hdg, monoN_diag_monoM e c hc]
    rfl

theorem WittEigen6_holds (h : UnitaryFieldData p f K) : WittEigen6 h := by
  intro hbar hζ P hPsu hcomm hpow hcard
  haveI : Finite K := h.finite
  have hdet : ∀ g ∈ P, (g : Matrix (Fin 6) (Fin 6) K).det = 1 :=
    fun g hg => (mem_gramSU.mp (hPsu g hg)).2
  have hgram : ∀ g ∈ P,
      hermT h (g : Matrix (Fin 6) (Fin 6) K) * (g : Matrix (Fin 6) (Fin 6) K) = 1 := by
    intro g hg
    have h1 := (mem_gramSU.mp (hPsu g hg)).1
    rw [Matrix.mul_one] at h1
    exact h1
  obtain ⟨ζ, hζp⟩ := hζ
  obtain ⟨T, hdiag⟩ := exists_T_diag P hζp hdet hcomm hpow
  obtain ⟨R, hR, hconj⟩ := witt_normal_form h hbar P T hdiag hcard hpow hgram
  refine ⟨R, hR, fun g hg => ?_⟩
  obtain ⟨x, hx⟩ := hconj g hg
  exact MonoidHom.mem_range.mpr ⟨x, hx⟩

end CFSG.LocalAnalysis.GLTheoremA.KD264Lie

end

