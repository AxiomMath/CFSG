module

public import CFSG.ClassicalGroups.Orthogonal.RootInvolutionFrame

public section

namespace CFSG.ClassicalGroups.Orthogonal

open QuadraticMap Matrix

section Data

theorem rootPairGram_eight_transpose : (rootPairGram 8)ᵀ = rootPairGram 8 := by decide

theorem rootPairGram_eight_mul_self : rootPairGram 8 * rootPairGram 8 = 1 := by decide

theorem rootPairGram_six_transpose : (rootPairGram 6)ᵀ = rootPairGram 6 := by decide

theorem rootPairGram_six_mul_self : rootPairGram 6 * rootPairGram 6 = 1 := by decide

@[expose] def a4InvolutionMat : Matrix (Fin 8) (Fin 8) (ZMod 2) :=
  rootFrameEichMat (rootPairGram 8) ![1, 0, 0, 0, 0, 0, 0, 0] ![0, 0, 1, 0, 0, 0, 0, 0] 0 *
    rootFrameEichMat (rootPairGram 8) ![0, 0, 0, 0, 1, 0, 0, 0] ![0, 0, 0, 0, 0, 0, 1, 0] 0

@[expose] def a4ConjugatorMat : Matrix (Fin 8) (Fin 8) (ZMod 2) :=
  rootFrameEichMat (rootPairGram 8) ![0, 0, 0, 0, 0, 1, 0, 0] ![0, 0, 0, 0, 0, 0, 0, 1] 0 *
    rootFrameEichMat (rootPairGram 8) ![0, 1, 0, 0, 0, 0, 0, 0] ![0, 0, 0, 1, 0, 0, 1, 0] 0

@[expose] def a4ConjugatorInvMat : Matrix (Fin 8) (Fin 8) (ZMod 2) :=
  rootFrameEichMat (rootPairGram 8) ![0, 1, 0, 0, 0, 0, 0, 0] ![0, 0, 0, 1, 0, 0, 1, 0] 0 *
    rootFrameEichMat (rootPairGram 8) ![0, 0, 0, 0, 0, 1, 0, 0] ![0, 0, 0, 0, 0, 0, 0, 1] 0

theorem a4ConjugatorMat_mul_inv : a4ConjugatorMat * a4ConjugatorInvMat = 1 := by decide

theorem a4_word_eq :
    a4InvolutionMat * (a4ConjugatorMat * a4InvolutionMat * a4ConjugatorInvMat) =
      !![1, 0, 0, 1, 0, 0, 0, 0;
         0, 0, 1, 0, 1, 0, 0, 1;
         0, 1, 1, 0, 0, 0, 0, 0;
         1, 0, 0, 0, 0, 0, 0, 0;
         0, 0, 0, 0, 1, 0, 0, 1;
         1, 0, 0, 1, 0, 0, 1, 0;
         0, 0, 0, 0, 0, 1, 1, 0;
         0, 0, 0, 0, 1, 0, 0, 0] := by decide

theorem orderOf_a4_word :
    orderOf (a4InvolutionMat * (a4ConjugatorMat * a4InvolutionMat * a4ConjugatorInvMat)) = 6 := by
  rw [a4_word_eq, orderOf_eq_iff (by norm_num)]
  refine ⟨by decide, fun k hk hk0 => ?_⟩
  interval_cases k <;> decide

@[expose] def c4InvolutionMat : Matrix (Fin 8) (Fin 8) (ZMod 2) :=
  rootFrameEichMat (rootPairGram 8) ![1, 0, 0, 0, 0, 0, 0, 0] ![0, 0, 0, 0, 0, 0, 1, 0] 1 *
    rootFrameEichMat (rootPairGram 8) ![0, 0, 1, 0, 0, 0, 0, 0] ![0, 0, 0, 0, 1, 0, 0, 0] 0

@[expose] def c4ConjugatorMat : Matrix (Fin 8) (Fin 8) (ZMod 2) :=
  rootFrameEichMat (rootPairGram 8) ![0, 1, 0, 0, 0, 0, 0, 0] ![0, 0, 0, 0, 1, 1, 0, 0] 1

theorem c4ConjugatorMat_mul_self : c4ConjugatorMat * c4ConjugatorMat = 1 := by decide

theorem c4_word_eq :
    c4InvolutionMat * (c4ConjugatorMat * c4InvolutionMat * c4ConjugatorMat) =
      !![1, 1, 0, 1, 0, 0, 0, 1;
         1, 0, 0, 1, 1, 1, 0, 1;
         0, 1, 1, 0, 1, 1, 0, 1;
         0, 0, 0, 1, 0, 0, 0, 0;
         1, 1, 0, 0, 0, 1, 0, 1;
         1, 1, 0, 0, 1, 0, 0, 1;
         0, 1, 0, 1, 0, 0, 1, 1;
         0, 0, 0, 0, 0, 0, 0, 1] := by decide

theorem orderOf_c4_word :
    orderOf (c4InvolutionMat * (c4ConjugatorMat * c4InvolutionMat * c4ConjugatorMat)) = 6 := by
  rw [c4_word_eq, orderOf_eq_iff (by norm_num)]
  refine ⟨by decide, fun k hk hk0 => ?_⟩
  interval_cases k <;> decide

@[expose] def c2InvolutionMat : Matrix (Fin 6) (Fin 6) (ZMod 2) :=
  rootFrameEichMat (rootPairGram 6) ![1, 0, 0, 0, 0, 0] ![0, 0, 0, 0, 1, 0] 1

@[expose] def c2ConjugateMat : Matrix (Fin 6) (Fin 6) (ZMod 2) :=
  rootFrameEichMat (rootPairGram 6) ![1, 1, 0, 1, 1, 0] ![0, 0, 0, 1, 1, 0] 1

theorem c2_word_eq :
    c2InvolutionMat * c2ConjugateMat =
      !![1, 1, 0, 0, 0, 1;
         1, 0, 0, 0, 0, 0;
         0, 0, 1, 0, 0, 0;
         0, 0, 1, 1, 0, 1;
         1, 0, 1, 0, 1, 1;
         0, 0, 0, 0, 0, 1] := by decide

theorem orderOf_c2_word : orderOf (c2InvolutionMat * c2ConjugateMat) = 6 := by
  rw [c2_word_eq, orderOf_eq_iff (by norm_num)]
  refine ⟨by decide, fun k hk hk0 => ?_⟩
  interval_cases k <;> decide

end Data

variable {K V : Type*} [Field K] [CharP K 2] [AddCommGroup V] [Module K V]
  {Q : QuadraticForm K V}

@[expose] noncomputable def a4Involution (P : ℕ → HypPair Q) : V ≃ₗ[K] V :=
  eichler Q (P 0).e (P 1).e * eichler Q (P 2).e (P 3).e

@[expose] noncomputable def a4Conjugator (P : ℕ → HypPair Q) : V ≃ₗ[K] V :=
  eichler Q (P 2).f (P 3).f * eichler Q (P 0).f ((P 1).f + (P 3).e)

@[expose] noncomputable def c4Involution (P : ℕ → HypPair Q) (a₁ : V) : V ≃ₗ[K] V :=
  eichler Q (P 0).e a₁ * eichler Q (P 1).e (P 2).e

@[expose] noncomputable def c4Conjugator (P : ℕ → HypPair Q) : V ≃ₗ[K] V :=
  eichler Q (P 0).f ((P 2).e + (P 2).f)

@[expose] noncomputable def c2Conjugator (P : ℕ → HypPair Q) (a₁ a₂ : V) : V ≃ₗ[K] V :=
  eichler Q (P 1).f a₂ * eichler Q (P 0).f a₁

omit [CharP K 2] in
theorem a4Conjugator_mem_elementaryGroup (P : ℕ → HypPair Q) :
    a4Conjugator P ∈ elementaryGroup Q :=
  mul_mem (eichler_mem_elementaryGroup Q _ _) (eichler_mem_elementaryGroup Q _ _)

omit [CharP K 2] in
theorem c4Conjugator_mem_elementaryGroup (P : ℕ → HypPair Q) :
    c4Conjugator P ∈ elementaryGroup Q :=
  eichler_mem_elementaryGroup Q _ _

omit [CharP K 2] in
theorem c2Conjugator_mem_elementaryGroup (P : ℕ → HypPair Q) (a₁ a₂ : V) :
    c2Conjugator P a₁ a₂ ∈ elementaryGroup Q :=
  mul_mem (eichler_mem_elementaryGroup Q _ _) (eichler_mem_elementaryGroup Q _ _)

section Transport

variable {n : ℕ} {G₀ : Matrix (Fin n) (Fin n) (ZMod 2)} {b : Fin n → V}

private noncomputable def frameHom (hb : IsGramFrame Q G₀ b) (hG : G₀ᵀ = G₀)
    (hG2 : G₀ * G₀ = 1) : Matrix (Fin n) (Fin n) (ZMod 2) →* Module.End K V where
  toFun A := rootFrameEnd Q G₀ b (A.map (ZMod.castHom (dvd_refl 2) K))
  map_one' := by rw [Matrix.map_one _ (map_zero _) (map_one _), rootFrameEnd_one]
  map_mul' A C := by rw [Matrix.map_mul, rootFrameEnd_mul hb hG hG2]

private theorem orderOf_eq_of_frameHom (hb : IsGramFrame Q G₀ b) (hG : G₀ᵀ = G₀)
    (hG2 : G₀ * G₀ = 1) {s : V ≃ₗ[K] V} {A : Matrix (Fin n) (Fin n) (ZMod 2)}
    (hs : (s : Module.End K V) = frameHom hb hG hG2 A) : orderOf s = orderOf A := by
  have hΦ : Function.Injective (frameHom hb hG hG2) := fun A C h =>
    Matrix.map_injective (ZMod.castHom_injective K) (rootFrameEnd_injective hb hG hG2 h)
  rw [← orderOf_injective LinearEquiv.automorphismGroup.toLinearMapMonoidHom
      (fun _ _ h => LinearEquiv.toLinearMap_injective h) s,
    ← orderOf_injective (frameHom hb hG hG2) hΦ A]
  exact congrArg orderOf hs

private theorem coe_inv_eq_frameHom (hb : IsGramFrame Q G₀ b) (hG : G₀ᵀ = G₀)
    (hG2 : G₀ * G₀ = 1) {s : V ≃ₗ[K] V} {A C : Matrix (Fin n) (Fin n) (ZMod 2)}
    (hs : (s : Module.End K V) = frameHom hb hG hG2 A) (hAC : A * C = 1) :
    ((s⁻¹ : V ≃ₗ[K] V) : Module.End K V) = frameHom hb hG hG2 C := by
  have h1 : (s : Module.End K V) * frameHom hb hG hG2 C = 1 := by
    rw [hs, ← map_mul, hAC, map_one]
  calc ((s⁻¹ : V ≃ₗ[K] V) : Module.End K V)
      = ((s⁻¹ : V ≃ₗ[K] V) : Module.End K V) * ((s : Module.End K V) * frameHom hb hG hG2 C) := by
        rw [h1, mul_one]
    _ = frameHom hb hG hG2 C := by
        rw [← mul_assoc, ← LinearEquiv.coe_toLinearMap_mul, inv_mul_cancel]
        exact one_mul _

private theorem frame_hq_of_ne {q₀ x₀ : Fin n → ZMod 2} {l : Fin n}
    (hq : ∀ i, i ≠ l → Q (b i) = ZMod.castHom (dvd_refl 2) K (q₀ i)) (hx : x₀ l = 0) :
    ∀ i, x₀ i ≠ 0 → Q (b i) = ZMod.castHom (dvd_refl 2) K (q₀ i) :=
  fun i hi => hq i fun h => hi (h ▸ hx)

private theorem eichler_eq_frameHom (hb : IsGramFrame Q G₀ b) (hG : G₀ᵀ = G₀)
    (hG2 : G₀ * G₀ = 1) {q₀ u₀ w₀ : Fin n → ZMod 2} {c₀ : ZMod 2}
    (hqu : ∀ i, u₀ i ≠ 0 → Q (b i) = ZMod.castHom (dvd_refl 2) K (q₀ i))
    (hqw : ∀ i, w₀ i ≠ 0 → Q (b i) = ZMod.castHom (dvd_refl 2) K (q₀ i))
    (h₀ : rootFrameQ G₀ q₀ u₀ = 0 ∧ u₀ ⬝ᵥ (G₀ *ᵥ w₀) = 0 ∧ rootFrameQ G₀ q₀ w₀ = c₀) {u w : V}
    (hu : rootFrameEmb b (fun i => ZMod.castHom (dvd_refl 2) K (u₀ i)) = u)
    (hw : rootFrameEmb b (fun i => ZMod.castHom (dvd_refl 2) K (w₀ i)) = w) :
    ((eichler Q u w : V ≃ₗ[K] V) : Module.End K V) =
      frameHom hb hG hG2 (rootFrameEichMat G₀ u₀ w₀ c₀) := by
  subst hu hw
  exact eichler_rootFrameEmb_cast hG hG2 rfl rfl
    (by rw [map_rootFrameEmb_cast hb q₀ u₀ hqu, h₀.1, map_zero])
    (by rw [polar_rootFrameEmb_cast hb, h₀.2.1, map_zero])
    (by rw [map_rootFrameEmb_cast hb q₀ w₀ hqw, h₀.2.2])

end Transport

private theorem isGramFrame_rootPairFrame_of_lt {k : ℕ} {x y : Fin k → V}
    (hxy : ∀ i, polar Q (x i) (y i) = 1)
    (horth : ∀ i j, i < j → polar Q (x i) (x j) = 0 ∧ polar Q (x i) (y j) = 0 ∧
      polar Q (y i) (x j) = 0 ∧ polar Q (y i) (y j) = 0) :
    IsGramFrame Q (rootPairGram (2 * k)) (rootPairFrame x y) := by
  refine isGramFrame_rootPairFrame hxy fun i j hij => ?_
  rcases lt_or_gt_of_ne hij with h | h
  · exact horth i j h
  · obtain ⟨h1, h2, h3, h4⟩ := horth j i h
    exact ⟨by rw [polar_comm, h1], by rw [polar_comm, h3], by rw [polar_comm, h2],
      by rw [polar_comm, h4]⟩

omit [CharP K 2] in
private theorem commute_eichler_of_fixes {g : V ≃ₗ[K] V}
    (hg : g ∈ TauCeti.QuadraticMap.orthogonalGroup Q) {u w : V} (hu : g u = u) (hw : g w = w) :
    Commute g (eichler Q u w) := by
  have h := eichler_conj hg u w
  rw [hu, hw] at h
  exact mul_inv_eq_iff_eq_mul.mp h

private theorem mul_conj_mul_eq_of_commute {G : Type*} [Group G] {s g k : G} (hs : Commute g s)
    (hk : Commute g k) (hgg : g * g = 1) : s * g * (k * (s * g) * k⁻¹) = s * (k * s * k⁻¹) := by
  have hk' : Commute g k⁻¹ := hk.inv_right
  calc s * g * (k * (s * g) * k⁻¹) = s * (g * k * s * (g * k⁻¹)) := by simp only [mul_assoc]
    _ = s * (k * g * s * (k⁻¹ * g)) := by rw [hk.eq, hk'.eq]
    _ = s * (k * (g * s) * k⁻¹ * g) := by simp only [mul_assoc]
    _ = s * (k * (s * g) * k⁻¹ * g) := by rw [hs.eq]
    _ = s * (k * s * (g * k⁻¹) * g) := by simp only [mul_assoc]
    _ = s * (k * s * (k⁻¹ * g) * g) := by rw [hk'.eq]
    _ = s * (k * s * k⁻¹) * (g * g) := by simp only [mul_assoc]
    _ = s * (k * s * k⁻¹) := by rw [hgg, mul_one]

private def a4Frame (P : ℕ → HypPair Q) : Fin 8 → V :=
  ![(P 0).e, (P 0).f, (P 1).e, (P 1).f, (P 2).e, (P 2).f, (P 3).e, (P 3).f]

private theorem a4_frame {P : ℕ → HypPair Q}
    (hP : ∀ i j, i < 4 → j < 4 → i ≠ j → (P i).Orth (P j)) :
    IsGramFrame Q (rootPairGram 8) (a4Frame P) ∧
      ∀ i, Q (a4Frame P i) = ZMod.castHom (dvd_refl 2) K ((0 : Fin 8 → ZMod 2) i) := by
  refine ⟨?_, fun i => ?_⟩
  · have h := isGramFrame_rootPairFrame (Q := Q) (x := fun i : Fin 4 => (P i).e)
      (y := fun i : Fin 4 => (P i).f) (fun i => (P i).polar_ef) fun i j hij =>
        let O := hP i j i.2 j.2 (Fin.val_injective.ne hij)
        ⟨O.ee, O.ef, O.fe, O.ff⟩
    have he : (rootPairFrame (fun i : Fin 4 => (P i).e) (fun i : Fin 4 => (P i).f) :
        Fin 8 → V) = a4Frame P := by
      funext i
      fin_cases i <;> rfl
    rw [he] at h
    exact h
  · fin_cases i <;> simp [a4Frame, HypPair.Q_e, HypPair.Q_f]

private theorem a4_mats {P : ℕ → HypPair Q} (hb : IsGramFrame Q (rootPairGram 8) (a4Frame P))
    (hq : ∀ i, Q (a4Frame P i) = ZMod.castHom (dvd_refl 2) K ((0 : Fin 8 → ZMod 2) i)) :
    ((a4Involution P : V ≃ₗ[K] V) : Module.End K V) =
        frameHom hb rootPairGram_eight_transpose rootPairGram_eight_mul_self a4InvolutionMat ∧
      ((a4Conjugator P : V ≃ₗ[K] V) : Module.End K V) =
        frameHom hb rootPairGram_eight_transpose rootPairGram_eight_mul_self a4ConjugatorMat := by
  have e1 : ((eichler Q (P 0).e (P 1).e : V ≃ₗ[K] V) : Module.End K V) =
      frameHom hb rootPairGram_eight_transpose rootPairGram_eight_mul_self (rootFrameEichMat
        (rootPairGram 8) ![1, 0, 0, 0, 0, 0, 0, 0] ![0, 0, 1, 0, 0, 0, 0, 0] 0) :=
    eichler_eq_frameHom hb _ _ (fun i _ => hq i) (fun i _ => hq i) (by decide)
      (by simp [a4Frame, rootFrameEmb_apply, Fin.sum_univ_succ])
      (by simp [a4Frame, rootFrameEmb_apply, Fin.sum_univ_succ])
  have e2 : ((eichler Q (P 2).e (P 3).e : V ≃ₗ[K] V) : Module.End K V) =
      frameHom hb rootPairGram_eight_transpose rootPairGram_eight_mul_self (rootFrameEichMat
        (rootPairGram 8) ![0, 0, 0, 0, 1, 0, 0, 0] ![0, 0, 0, 0, 0, 0, 1, 0] 0) :=
    eichler_eq_frameHom hb _ _ (fun i _ => hq i) (fun i _ => hq i) (by decide)
      (by simp [a4Frame, rootFrameEmb_apply, Fin.sum_univ_succ])
      (by simp [a4Frame, rootFrameEmb_apply, Fin.sum_univ_succ])
  have e3 : ((eichler Q (P 2).f (P 3).f : V ≃ₗ[K] V) : Module.End K V) =
      frameHom hb rootPairGram_eight_transpose rootPairGram_eight_mul_self (rootFrameEichMat
        (rootPairGram 8) ![0, 0, 0, 0, 0, 1, 0, 0] ![0, 0, 0, 0, 0, 0, 0, 1] 0) :=
    eichler_eq_frameHom hb _ _ (fun i _ => hq i) (fun i _ => hq i) (by decide)
      (by simp [a4Frame, rootFrameEmb_apply, Fin.sum_univ_succ])
      (by simp [a4Frame, rootFrameEmb_apply, Fin.sum_univ_succ])
  have e4 : ((eichler Q (P 0).f ((P 1).f + (P 3).e) : V ≃ₗ[K] V) : Module.End K V) =
      frameHom hb rootPairGram_eight_transpose rootPairGram_eight_mul_self (rootFrameEichMat
        (rootPairGram 8) ![0, 1, 0, 0, 0, 0, 0, 0] ![0, 0, 0, 1, 0, 0, 1, 0] 0) :=
    eichler_eq_frameHom hb _ _ (fun i _ => hq i) (fun i _ => hq i) (by decide)
      (by simp [a4Frame, rootFrameEmb_apply, Fin.sum_univ_succ])
      (by simp [a4Frame, rootFrameEmb_apply, Fin.sum_univ_succ])
  refine ⟨?_, ?_⟩
  · rw [a4Involution, LinearEquiv.coe_toLinearMap_mul, e1, e2, ← map_mul]
    rfl
  · rw [a4Conjugator, LinearEquiv.coe_toLinearMap_mul, e3, e4, ← map_mul]
    rfl

theorem orderOf_a4_mul_conj {P : ℕ → HypPair Q}
    (hP : ∀ i j, i < 4 → j < 4 → i ≠ j → (P i).Orth (P j)) {g : V ≃ₗ[K] V}
    (hgO : g ∈ TauCeti.QuadraticMap.orthogonalGroup Q) (hgg : g * g = 1)
    (hfix : ∀ i < 4, g (P i).e = (P i).e ∧ g (P i).f = (P i).f) :
    orderOf (a4Involution P * g *
      (a4Conjugator P * (a4Involution P * g) * (a4Conjugator P)⁻¹)) = 6 := by
  have hcs : Commute g (a4Involution P) :=
    (commute_eichler_of_fixes hgO (hfix 0 (by norm_num)).1 (hfix 1 (by norm_num)).1).mul_right
      (commute_eichler_of_fixes hgO (hfix 2 (by norm_num)).1 (hfix 3 (by norm_num)).1)
  have hck : Commute g (a4Conjugator P) :=
    (commute_eichler_of_fixes hgO (hfix 2 (by norm_num)).2 (hfix 3 (by norm_num)).2).mul_right
      (commute_eichler_of_fixes hgO (hfix 0 (by norm_num)).2
        (by rw [map_add, (hfix 1 (by norm_num)).2, (hfix 3 (by norm_num)).1]))
  obtain ⟨hb, hq⟩ := a4_frame hP
  obtain ⟨hs, hk⟩ := a4_mats hb hq
  rw [mul_conj_mul_eq_of_commute hcs hck hgg, orderOf_eq_of_frameHom hb
    rootPairGram_eight_transpose rootPairGram_eight_mul_self
    (A := a4InvolutionMat * (a4ConjugatorMat * a4InvolutionMat * a4ConjugatorInvMat))]
  · exact orderOf_a4_word
  · simp only [LinearEquiv.coe_toLinearMap_mul]
    rw [hs, hk, coe_inv_eq_frameHom hb _ _ hk a4ConjugatorMat_mul_inv, map_mul, map_mul, map_mul]

private def c4Frame (P : ℕ → HypPair Q) (a₁ a₂ : V) : Fin 8 → V :=
  ![(P 0).e, (P 0).f, (P 1).e, (P 1).f, (P 2).e, (P 2).f, a₁, a₂]

private theorem c4_frame {P : ℕ → HypPair Q}
    (hP : ∀ i j, i < 3 → j < 3 → i ≠ j → (P i).Orth (P j)) {a₁ a₂ : V} (ha₁ : Q a₁ = 1)
    (ha₁₂ : polar Q a₁ a₂ = 1)
    (hperp : ∀ i < 3, polar Q (P i).e a₁ = 0 ∧ polar Q (P i).f a₁ = 0 ∧
      polar Q (P i).e a₂ = 0 ∧ polar Q (P i).f a₂ = 0) :
    IsGramFrame Q (rootPairGram 8) (c4Frame P a₁ a₂) ∧
      ∀ i, i ≠ 7 → Q (c4Frame P a₁ a₂ i) =
        ZMod.castHom (dvd_refl 2) K ((![0, 0, 0, 0, 0, 0, 1, 0] : Fin 8 → ZMod 2) i) := by
  obtain ⟨h0e1, h0f1, h0e2, h0f2⟩ := hperp 0 (by norm_num)
  obtain ⟨h1e1, h1f1, h1e2, h1f2⟩ := hperp 1 (by norm_num)
  obtain ⟨h2e1, h2f1, h2e2, h2f2⟩ := hperp 2 (by norm_num)
  have O01 := hP 0 1 (by norm_num) (by norm_num) (by norm_num)
  have O02 := hP 0 2 (by norm_num) (by norm_num) (by norm_num)
  have O12 := hP 1 2 (by norm_num) (by norm_num) (by norm_num)
  refine ⟨?_, fun i hi => ?_⟩
  · have h := isGramFrame_rootPairFrame_of_lt (Q := Q) (x := ![(P 0).e, (P 1).e, (P 2).e, a₁])
      (y := ![(P 0).f, (P 1).f, (P 2).f, a₂])
      (fun i => by
        fin_cases i
        exacts [(P 0).polar_ef, (P 1).polar_ef, (P 2).polar_ef, ha₁₂])
      (fun i j h => by
        fin_cases i <;> fin_cases j <;> first
          | exact absurd h (by decide)
          | exact ⟨O01.ee, O01.ef, O01.fe, O01.ff⟩
          | exact ⟨O02.ee, O02.ef, O02.fe, O02.ff⟩
          | exact ⟨O12.ee, O12.ef, O12.fe, O12.ff⟩
          | exact ⟨h0e1, h0e2, h0f1, h0f2⟩
          | exact ⟨h1e1, h1e2, h1f1, h1f2⟩
          | exact ⟨h2e1, h2e2, h2f1, h2f2⟩)
    have he : (rootPairFrame ![(P 0).e, (P 1).e, (P 2).e, a₁] ![(P 0).f, (P 1).f, (P 2).f, a₂] :
        Fin 8 → V) = c4Frame P a₁ a₂ := by
      funext i
      fin_cases i <;> rfl
    rw [he] at h
    exact h
  · fin_cases i <;> first
      | exact absurd rfl hi
      | simp [c4Frame, HypPair.Q_e, HypPair.Q_f, ha₁]

private theorem c4_mats {P : ℕ → HypPair Q} {a₁ a₂ : V}
    (hb : IsGramFrame Q (rootPairGram 8) (c4Frame P a₁ a₂))
    (hq : ∀ i, i ≠ 7 → Q (c4Frame P a₁ a₂ i) =
      ZMod.castHom (dvd_refl 2) K ((![0, 0, 0, 0, 0, 0, 1, 0] : Fin 8 → ZMod 2) i)) :
    ((c4Involution P a₁ : V ≃ₗ[K] V) : Module.End K V) =
        frameHom hb rootPairGram_eight_transpose rootPairGram_eight_mul_self c4InvolutionMat ∧
      ((c4Conjugator P : V ≃ₗ[K] V) : Module.End K V) =
        frameHom hb rootPairGram_eight_transpose rootPairGram_eight_mul_self c4ConjugatorMat := by
  have e1 : ((eichler Q (P 0).e a₁ : V ≃ₗ[K] V) : Module.End K V) =
      frameHom hb rootPairGram_eight_transpose rootPairGram_eight_mul_self (rootFrameEichMat
        (rootPairGram 8) ![1, 0, 0, 0, 0, 0, 0, 0] ![0, 0, 0, 0, 0, 0, 1, 0] 1) :=
    eichler_eq_frameHom hb _ _ (frame_hq_of_ne hq (by decide)) (frame_hq_of_ne hq (by decide))
      (by decide) (by simp [c4Frame, rootFrameEmb_apply, Fin.sum_univ_succ])
      (by simp [c4Frame, rootFrameEmb_apply, Fin.sum_univ_succ])
  have e2 : ((eichler Q (P 1).e (P 2).e : V ≃ₗ[K] V) : Module.End K V) =
      frameHom hb rootPairGram_eight_transpose rootPairGram_eight_mul_self (rootFrameEichMat
        (rootPairGram 8) ![0, 0, 1, 0, 0, 0, 0, 0] ![0, 0, 0, 0, 1, 0, 0, 0] 0) :=
    eichler_eq_frameHom hb _ _ (frame_hq_of_ne hq (by decide)) (frame_hq_of_ne hq (by decide))
      (by decide) (by simp [c4Frame, rootFrameEmb_apply, Fin.sum_univ_succ])
      (by simp [c4Frame, rootFrameEmb_apply, Fin.sum_univ_succ])
  refine ⟨?_, ?_⟩
  · rw [c4Involution, LinearEquiv.coe_toLinearMap_mul, e1, e2, ← map_mul]
    rfl
  · exact eichler_eq_frameHom hb _ _ (frame_hq_of_ne hq (by decide))
      (frame_hq_of_ne hq (by decide)) (by decide)
      (by simp [c4Frame, rootFrameEmb_apply, Fin.sum_univ_succ])
      (by simp [c4Frame, rootFrameEmb_apply, Fin.sum_univ_succ])

theorem orderOf_c4_mul_conj {P : ℕ → HypPair Q}
    (hP : ∀ i j, i < 3 → j < 3 → i ≠ j → (P i).Orth (P j)) {a₁ a₂ : V} (ha₁ : Q a₁ = 1)
    (ha₁₂ : polar Q a₁ a₂ = 1)
    (hperp : ∀ i < 3, polar Q (P i).e a₁ = 0 ∧ polar Q (P i).f a₁ = 0 ∧
      polar Q (P i).e a₂ = 0 ∧ polar Q (P i).f a₂ = 0)
    {g : V ≃ₗ[K] V} (hgO : g ∈ TauCeti.QuadraticMap.orthogonalGroup Q) (hgg : g * g = 1)
    (hfix : ∀ i < 3, g (P i).e = (P i).e ∧ g (P i).f = (P i).f) (hga : g a₁ = a₁ ∧ g a₂ = a₂) :
    orderOf (c4Involution P a₁ * g *
      (c4Conjugator P * (c4Involution P a₁ * g) * (c4Conjugator P)⁻¹)) = 6 := by
  have hcs : Commute g (c4Involution P a₁) :=
    (commute_eichler_of_fixes hgO (hfix 0 (by norm_num)).1 hga.1).mul_right
      (commute_eichler_of_fixes hgO (hfix 1 (by norm_num)).1 (hfix 2 (by norm_num)).1)
  have hck : Commute g (c4Conjugator P) :=
    commute_eichler_of_fixes hgO (hfix 0 (by norm_num)).2
      (by rw [map_add, (hfix 2 (by norm_num)).1, (hfix 2 (by norm_num)).2])
  obtain ⟨hb, hq⟩ := c4_frame hP ha₁ ha₁₂ hperp
  obtain ⟨hs, hk⟩ := c4_mats hb hq
  rw [mul_conj_mul_eq_of_commute hcs hck hgg, orderOf_eq_of_frameHom hb
    rootPairGram_eight_transpose rootPairGram_eight_mul_self
    (A := c4InvolutionMat * (c4ConjugatorMat * c4InvolutionMat * c4ConjugatorMat))]
  · exact orderOf_c4_word
  · simp only [LinearEquiv.coe_toLinearMap_mul]
    rw [hs, hk, coe_inv_eq_frameHom hb _ _ hk c4ConjugatorMat_mul_self, map_mul, map_mul, map_mul]

private theorem c2Conjugator_apply_e {P : ℕ → HypPair Q} (hP : (P 0).Orth (P 1)) {a₁ a₂ : V}
    (ha₁ : Q a₁ = 1) (ha₁₂ : polar Q a₁ a₂ = 1)
    (hperp : ∀ i < 2, polar Q (P i).e a₁ = 0 ∧ polar Q (P i).f a₁ = 0 ∧
      polar Q (P i).e a₂ = 0 ∧ polar Q (P i).f a₂ = 0) :
    c2Conjugator P a₁ a₂ (P 0).e = (P 0).e + (P 0).f + (P 1).f + a₁ := by
  obtain ⟨h0e1, h0f1, h0e2, h0f2⟩ := hperp 0 (by norm_num)
  obtain ⟨-, h1f1, -, h1f2⟩ := hperp 1 (by norm_num)
  have hk0 : eichler Q (P 0).f a₁ (P 0).e = (P 0).e + a₁ + (P 0).f := by
    rw [eichler_apply (P 0).Q_f h0f1, (P 0).polar_ef, h0e1, ha₁, sub_eq_add_neg, ← neg_smul,
      CharTwo.neg_eq]
    module
  have h1 : polar Q ((P 0).e + a₁ + (P 0).f) (P 1).f = 0 := by
    rw [polar_add_left, polar_add_left, hP.ef, polar_comm Q a₁, h1f1, hP.ff, add_zero, add_zero]
  have h2 : polar Q ((P 0).e + a₁ + (P 0).f) a₂ = 1 := by
    rw [polar_add_left, polar_add_left, h0e2, ha₁₂, h0f2, zero_add, add_zero]
  rw [c2Conjugator, LinearEquiv.mul_apply, hk0, eichler_apply (P 1).Q_f h1f2, h1, h2,
    sub_eq_add_neg, ← neg_smul, CharTwo.neg_eq]
  module

private theorem c2Conjugator_apply_a {P : ℕ → HypPair Q} {a₁ a₂ : V} (ha₁₂ : polar Q a₁ a₂ = 1)
    (hperp : ∀ i < 2, polar Q (P i).e a₁ = 0 ∧ polar Q (P i).f a₁ = 0 ∧
      polar Q (P i).e a₂ = 0 ∧ polar Q (P i).f a₂ = 0) :
    c2Conjugator P a₁ a₂ a₁ = a₁ + (P 1).f := by
  obtain ⟨-, h0f1, -, -⟩ := hperp 0 (by norm_num)
  obtain ⟨-, h1f1, -, h1f2⟩ := hperp 1 (by norm_num)
  have haa : polar Q a₁ a₁ = 0 := by
    rw [polar_self_eq_two_mul, CharTwo.two_eq_zero, zero_mul]
  have hk0 : eichler Q (P 0).f a₁ a₁ = a₁ :=
    eichler_apply_of_polar_eq_zero (by rw [polar_comm, h0f1]) haa
  rw [c2Conjugator, LinearEquiv.mul_apply, hk0, eichler_apply (P 1).Q_f h1f2,
    polar_comm Q a₁ (P 1).f, h1f1, ha₁₂, sub_eq_add_neg, ← neg_smul, CharTwo.neg_eq]
  module

theorem c2Conjugator_conj {P : ℕ → HypPair Q} (hP : (P 0).Orth (P 1)) {a₁ a₂ : V}
    (ha₁ : Q a₁ = 1) (ha₁₂ : polar Q a₁ a₂ = 1)
    (hperp : ∀ i < 2, polar Q (P i).e a₁ = 0 ∧ polar Q (P i).f a₁ = 0 ∧
      polar Q (P i).e a₂ = 0 ∧ polar Q (P i).f a₂ = 0) :
    c2Conjugator P a₁ a₂ * eichler Q (P 0).e a₁ * (c2Conjugator P a₁ a₂)⁻¹ =
      eichler Q ((P 0).e + (P 0).f + (P 1).f + a₁) (a₁ + (P 1).f) := by
  have hkO : c2Conjugator P a₁ a₂ ∈ TauCeti.QuadraticMap.orthogonalGroup Q :=
    mul_mem (eichler_mem_orthogonalGroup Q _ _) (eichler_mem_orthogonalGroup Q _ _)
  rw [eichler_conj hkO, c2Conjugator_apply_e hP ha₁ ha₁₂ hperp,
    c2Conjugator_apply_a ha₁₂ hperp]

private def c2Frame (P : ℕ → HypPair Q) (a₁ a₂ : V) : Fin 6 → V :=
  ![(P 0).e, (P 0).f, (P 1).e, (P 1).f, a₁, a₂]

private theorem c2_frame {P : ℕ → HypPair Q} (hP : (P 0).Orth (P 1)) {a₁ a₂ : V}
    (ha₁ : Q a₁ = 1) (ha₁₂ : polar Q a₁ a₂ = 1)
    (hperp : ∀ i < 2, polar Q (P i).e a₁ = 0 ∧ polar Q (P i).f a₁ = 0 ∧
      polar Q (P i).e a₂ = 0 ∧ polar Q (P i).f a₂ = 0) :
    IsGramFrame Q (rootPairGram 6) (c2Frame P a₁ a₂) ∧
      ∀ i, i ≠ 5 → Q (c2Frame P a₁ a₂ i) =
        ZMod.castHom (dvd_refl 2) K ((![0, 0, 0, 0, 1, 0] : Fin 6 → ZMod 2) i) := by
  obtain ⟨h0e1, h0f1, h0e2, h0f2⟩ := hperp 0 (by norm_num)
  obtain ⟨h1e1, h1f1, h1e2, h1f2⟩ := hperp 1 (by norm_num)
  refine ⟨?_, fun i hi => ?_⟩
  · have h := isGramFrame_rootPairFrame_of_lt (Q := Q) (x := ![(P 0).e, (P 1).e, a₁])
      (y := ![(P 0).f, (P 1).f, a₂])
      (fun i => by
        fin_cases i
        exacts [(P 0).polar_ef, (P 1).polar_ef, ha₁₂])
      (fun i j h => by
        fin_cases i <;> fin_cases j <;> first
          | exact absurd h (by decide)
          | exact ⟨hP.ee, hP.ef, hP.fe, hP.ff⟩
          | exact ⟨h0e1, h0e2, h0f1, h0f2⟩
          | exact ⟨h1e1, h1e2, h1f1, h1f2⟩)
    have he : (rootPairFrame ![(P 0).e, (P 1).e, a₁] ![(P 0).f, (P 1).f, a₂] : Fin 6 → V) =
        c2Frame P a₁ a₂ := by
      funext i
      fin_cases i <;> rfl
    rw [he] at h
    exact h
  · fin_cases i <;> first
      | exact absurd rfl hi
      | simp [c2Frame, HypPair.Q_e, HypPair.Q_f, ha₁]

theorem orderOf_c2_mul_conj {P : ℕ → HypPair Q} (hP : (P 0).Orth (P 1)) {a₁ a₂ : V}
    (ha₁ : Q a₁ = 1) (ha₁₂ : polar Q a₁ a₂ = 1)
    (hperp : ∀ i < 2, polar Q (P i).e a₁ = 0 ∧ polar Q (P i).f a₁ = 0 ∧
      polar Q (P i).e a₂ = 0 ∧ polar Q (P i).f a₂ = 0) :
    orderOf (eichler Q (P 0).e a₁ *
      (c2Conjugator P a₁ a₂ * eichler Q (P 0).e a₁ * (c2Conjugator P a₁ a₂)⁻¹)) = 6 := by
  rw [c2Conjugator_conj hP ha₁ ha₁₂ hperp]
  obtain ⟨hb, hq⟩ := c2_frame hP ha₁ ha₁₂ hperp
  have e1 : ((eichler Q (P 0).e a₁ : V ≃ₗ[K] V) : Module.End K V) =
      frameHom hb rootPairGram_six_transpose rootPairGram_six_mul_self c2InvolutionMat :=
    eichler_eq_frameHom hb _ _ (frame_hq_of_ne hq (by decide)) (frame_hq_of_ne hq (by decide))
      (by decide) (by simp [c2Frame, rootFrameEmb_apply, Fin.sum_univ_succ])
      (by simp [c2Frame, rootFrameEmb_apply, Fin.sum_univ_succ])
  have e2 : ((eichler Q ((P 0).e + (P 0).f + (P 1).f + a₁) (a₁ + (P 1).f) : V ≃ₗ[K] V) :
      Module.End K V) =
        frameHom hb rootPairGram_six_transpose rootPairGram_six_mul_self c2ConjugateMat :=
    eichler_eq_frameHom hb _ _ (frame_hq_of_ne hq (by decide)) (frame_hq_of_ne hq (by decide))
      (by decide) (by simp [c2Frame, rootFrameEmb_apply, Fin.sum_univ_succ]; abel)
      (by simp [c2Frame, rootFrameEmb_apply, Fin.sum_univ_succ]; abel)
  rw [orderOf_eq_of_frameHom hb rootPairGram_six_transpose rootPairGram_six_mul_self
    (A := c2InvolutionMat * c2ConjugateMat)
    (by rw [LinearEquiv.coe_toLinearMap_mul, e1, e2, map_mul])]
  exact orderOf_c2_word

end CFSG.ClassicalGroups.Orthogonal
