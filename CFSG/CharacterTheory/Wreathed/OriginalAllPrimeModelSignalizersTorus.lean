module

public import CFSG.CharacterTheory.Wreathed.CentralSL2.BaseElements
public import CFSG.CharacterTheory.Wreathed.CentralSL2.ProjectiveLine
public import CFSG.CharacterTheory.Wreathed.OddFieldFixedTorusDerivedCentralizerSupport

public section

namespace CFSG.Wreathed.OriginalAllPrime.ModelSignalizers

open Matrix CFSG.Wreathed.CyclicCentralSL2Extension CFSG.Wreathed.CentralSL2Abelianization
open CFSG.Wreathed.CentralSL2 CFSG.ComponentClassification.CatalogueSchreierLinearTwo

variable {F : Type} [Field F]

theorem eq_one_of_fieldSL_fixes_torus (h2 : (2 : F) ≠ 0) {σ : F ≃+* F}
    (hσ : ∀ t ∈ Subgroup.centralizer {weyl F}, fieldSL F σ t = t) : σ = 1 := by
  have key : ∀ s : F, 1 + s ^ 2 ≠ 0 → σ s = s := by
    intro s hs
    set v := (1 - s ^ 2) / (1 + s ^ 2) with hv_def
    set w := 2 * s / (1 + s ^ 2) with hw_def
    have hvw : v ^ 2 + w ^ 2 = 1 := by
      rw [hv_def, hw_def]
      field_simp
      ring
    have ht := hσ _ (CFSG.Wreathed.OddFieldTorus.rot_mem v w hvw)
    have hv : σ v = v := by
      have h00 := congrArg (fun X : SpecialLinearGroup (Fin 2) F => X 0 0) ht
      simpa [fieldSL_apply, CFSG.Wreathed.OddFieldTorus.rot_coe] using h00
    have hw : σ w = w := by
      have h10 := congrArg (fun X : SpecialLinearGroup (Fin 2) F => X 1 0) ht
      simpa [fieldSL_apply, CFSG.Wreathed.OddFieldTorus.rot_coe] using h10
    have h1v : 1 + v = 2 / (1 + s ^ 2) := by
      rw [hv_def]
      field_simp
      ring
    have hs' : s = w / (1 + v) := by
      rw [h1v, hw_def]
      field_simp
    rw [hs', map_div₀, map_add, map_one, hv, hw]
  apply RingEquiv.ext
  intro s
  change σ s = s
  by_cases hs : 1 + s ^ 2 = 0
  · by_cases hs1 : 1 + (s + 1) ^ 2 = 0
    · have hs2 : s = -1 / 2 := by
        field_simp
        linear_combination hs1 - hs
      rw [hs2, map_div₀, map_neg, map_one, map_ofNat]
    · have h := key (s + 1) hs1
      rw [map_add, map_one] at h
      exact add_right_cancel h
  · exact key s hs

theorem fieldAut_apply_eq_of_mul_self_eq_neg_one (h2 : (2 : F) ≠ 0) {σ : F ≃+* F}
    (hσ : Odd (orderOf σ)) {i : F} (hi : i * i = -1) : σ i = i := by
  have hσi : σ i * σ i = -1 := by rw [← map_mul, hi, map_neg, map_one]
  have hcases : (σ i - i) * (σ i + i) = 0 := by linear_combination hσi - hi
  rcases mul_eq_zero.mp hcases with h | h
  · exact sub_eq_zero.mp h
  · exfalso
    have hneg : σ i = -i := by linear_combination h
    have hpow : ∀ n : ℕ, (σ ^ n) i = (-1) ^ n * i := by
      intro n
      induction n with
      | zero => simp
      | succ n ih =>
        rw [pow_succ']
        change σ ((σ ^ n) i) = _
        rw [ih, map_mul, map_pow, map_neg, map_one, hneg]
        ring
    have h1 := hpow (orderOf σ)
    rw [pow_orderOf_eq_one, hσ.neg_one_pow] at h1
    have hi0 : i = 0 := by
      have h' : (2 : F) * i = 0 := by
        have h1' : i = -1 * i := h1
        linear_combination h1'
      exact (mul_eq_zero.mp h').resolve_left h2
    rw [hi0, mul_zero] at hi
    exact one_ne_zero (neg_eq_zero.mp hi.symm)

theorem neg_mul_neg_eq_neg_one {i : F} (hi : i * i = -1) : -i * -i = -1 := by
  rw [neg_mul_neg]
  exact hi

@[expose] def nilMat (i : F) : Matrix (Fin 2) (Fin 2) F := !![i, 1; 1, -i]

@[expose] def rootSL (i : F) (hi : i * i = -1) (l : F) : SpecialLinearGroup (Fin 2) F :=
  ⟨!![1 + l * i, l; l, 1 - l * i], by
    rw [det_fin_two_of]
    linear_combination (-l ^ 2) * hi⟩

theorem rootSL_coe (i : F) (hi : i * i = -1) (l : F) :
    (rootSL i hi l : Matrix (Fin 2) (Fin 2) F) = !![1 + l * i, l; l, 1 - l * i] := rfl

theorem rootSL_add (i : F) (hi : i * i = -1) (l l' : F) :
    rootSL i hi (l + l') = rootSL i hi l * rootSL i hi l' := by
  apply Subtype.ext
  change !![1 + (l + l') * i, l + l'; l + l', 1 - (l + l') * i] =
    !![1 + l * i, l; l, 1 - l * i] * !![1 + l' * i, l'; l', 1 - l' * i]
  rw [Matrix.mul_fin_two]
  ext p q
  fin_cases p <;> fin_cases q
  · simp only [Fin.zero_eta, Fin.isValue, of_apply, cons_val', cons_val_zero, empty_val',
      cons_val_fin_one]
    linear_combination (-(l * l')) * hi
  · simp only [Fin.zero_eta, Fin.isValue, Fin.mk_one, of_apply, cons_val', cons_val_one,
      cons_val_zero, empty_val', cons_val_fin_one]
    ring
  · simp only [Fin.mk_one, Fin.isValue, Fin.zero_eta, of_apply, cons_val', cons_val_zero,
      cons_val_one, empty_val', cons_val_fin_one]
    ring
  · simp only [Fin.mk_one, Fin.isValue, of_apply, cons_val', cons_val_one, empty_val',
      cons_val_fin_one]
    linear_combination (-(l * l')) * hi

theorem rootSL_zero (i : F) (hi : i * i = -1) : rootSL i hi 0 = 1 := by
  apply Subtype.ext
  change !![1 + 0 * i, 0; 0, 1 - 0 * i] = (1 : Matrix (Fin 2) (Fin 2) F)
  rw [Matrix.one_fin_two]
  simp

@[expose] def rootHom (i : F) (hi : i * i = -1) :
    Multiplicative F →* SpecialLinearGroup (Fin 2) F where
  toFun l := rootSL i hi l.toAdd
  map_one' := rootSL_zero i hi
  map_mul' l l' := rootSL_add i hi l.toAdd l'.toAdd

theorem rootHom_apply (i : F) (hi : i * i = -1) (l : Multiplicative F) :
    rootHom i hi l = rootSL i hi l.toAdd := rfl

theorem rootSL_injective (i : F) (hi : i * i = -1) : Function.Injective (rootSL i hi) := by
  intro l l' h
  have h01 := congrArg (fun X : SpecialLinearGroup (Fin 2) F => X 0 1) h
  simpa [rootSL_coe] using h01

theorem rootHom_injective (i : F) (hi : i * i = -1) : Function.Injective (rootHom i hi) :=
  fun _ _ h => Multiplicative.toAdd.injective (rootSL_injective i hi h)

theorem rootSL_nsmul (i : F) (hi : i * i = -1) (n : ℕ) (l : F) :
    rootSL i hi l ^ n = rootSL i hi (n * l) := by
  induction n with
  | zero => rw [pow_zero, Nat.cast_zero, zero_mul, rootSL_zero]
  | succ n ih => rw [pow_succ, ih, ← rootSL_add, Nat.cast_succ]; ring_nf

theorem rootSL_mem_torus_iff (h2 : (2 : F) ≠ 0) (i : F) (hi : i * i = -1) (l : F) :
    rootSL i hi l ∈ Subgroup.centralizer {weyl F} ↔ l = 0 := by
  constructor
  · intro h
    have h' := ((CFSG.Wreathed.OddFieldTorus.mem_torus_coord_iff _).mp h).2
    simp only [rootSL_coe, of_apply, cons_val', cons_val_one, cons_val_zero, empty_val',
      cons_val_fin_one, Fin.isValue] at h'
    have h2l : (2 : F) * l = 0 := by linear_combination h'
    exact (mul_eq_zero.mp h2l).resolve_left h2
  · rintro rfl
    rw [rootSL_zero]
    exact Subgroup.one_mem _

theorem toGL_weyl_coe :
    ((SpecialLinearGroup.toGL (weyl F) : GL (Fin 2) F) : Matrix (Fin 2) (Fin 2) F) =
      !![0, -1; 1, 0] := rfl

theorem entries_of_commute_weyl {G : GL (Fin 2) F}
    (hG : G * SpecialLinearGroup.toGL (weyl F) = SpecialLinearGroup.toGL (weyl F) * G) :
    G.val 1 1 = G.val 0 0 ∧ G.val 0 1 = -G.val 1 0 := by
  have h := congrArg (fun A : GL (Fin 2) F => (A : Matrix (Fin 2) (Fin 2) F)) hG
  simp only [Units.val_mul, toGL_weyl_coe] at h
  have h00 := congrFun (congrFun h 0) 0
  have h01 := congrFun (congrFun h 0) 1
  simp [Matrix.mul_apply, Fin.sum_univ_two] at h00 h01
  exact ⟨by linear_combination -h01, by linear_combination h00⟩

theorem entries_of_conj_weyl_eq_inv {G : GL (Fin 2) F}
    (hG : matrixConjugation F G (weyl F) = (weyl F)⁻¹) :
    G.val 1 1 = -G.val 0 0 ∧ G.val 0 1 = G.val 1 0 := by
  have h := congrArg (fun X : SpecialLinearGroup (Fin 2) F =>
    (SpecialLinearGroup.toGL X : GL (Fin 2) F)) hG
  simp only [matrixConjugation_toGL] at h
  have h' : G * SpecialLinearGroup.toGL (weyl F) =
      SpecialLinearGroup.toGL (weyl F)⁻¹ * G := by
    rw [← h]
    group
  have hm := congrArg (fun A : GL (Fin 2) F => (A : Matrix (Fin 2) (Fin 2) F)) h'
  simp only [Units.val_mul, toGL_weyl_coe] at hm
  have hinv : ((SpecialLinearGroup.toGL ((weyl F)⁻¹) : GL (Fin 2) F) :
      Matrix (Fin 2) (Fin 2) F) = !![0, 1; -1, 0] := by
    exact weyl_inv_val F
  rw [hinv] at hm
  have h00 := congrFun (congrFun hm 0) 0
  have h01 := congrFun (congrFun hm 0) 1
  simp [Matrix.mul_apply, Fin.sum_univ_two] at h00 h01
  exact ⟨by linear_combination -h01, by linear_combination h00⟩

theorem sum_sq_ne_zero_of_commute_weyl {G : GL (Fin 2) F}
    (hG : G * SpecialLinearGroup.toGL (weyl F) = SpecialLinearGroup.toGL (weyl F) * G) :
    G.val 0 0 * G.val 0 0 + G.val 1 0 * G.val 1 0 ≠ 0 := by
  obtain ⟨h11, h01⟩ := entries_of_commute_weyl hG
  have hdet := GeneralLinearGroup.det_ne_zero G
  rw [det_fin_two] at hdet
  intro h
  apply hdet
  change G.val 0 0 * G.val 1 1 - G.val 0 1 * G.val 1 0 = 0
  rw [h11, h01]
  linear_combination h

theorem sub_mul_ne_zero_of_commute_weyl {i : F} (hi : i * i = -1) {G : GL (Fin 2) F}
    (hG : G * SpecialLinearGroup.toGL (weyl F) = SpecialLinearGroup.toGL (weyl F) * G) :
    G.val 0 0 - G.val 1 0 * i ≠ 0 := by
  intro h
  apply sum_sq_ne_zero_of_commute_weyl hG
  linear_combination (G.val 0 0 + G.val 1 0 * i) * h + G.val 1 0 ^ 2 * hi

theorem matrixConjugation_rootSL_of_commute {i : F} (hi : i * i = -1) {G : GL (Fin 2) F}
    (hG : G * SpecialLinearGroup.toGL (weyl F) = SpecialLinearGroup.toGL (weyl F) * G) (l : F) :
    matrixConjugation F G (rootSL i hi l) =
      rootSL i hi (l * ((G.val 0 0 + G.val 1 0 * i) / (G.val 0 0 - G.val 1 0 * i))) := by
  obtain ⟨h11, h01⟩ := entries_of_commute_weyl hG
  have hD := sub_mul_ne_zero_of_commute_weyl hi hG
  set a := G.val 0 0 with ha
  set c := G.val 1 0 with hc
  set κ := (a + c * i) / (a - c * i) with hκdef
  have hκ : κ * (a - c * i) = a + c * i := by rw [hκdef]; field_simp
  have hGm : (G : Matrix (Fin 2) (Fin 2) F) = !![a, -c; c, a] := by
    rw [Matrix.eta_fin_two (G : Matrix (Fin 2) (Fin 2) F)]
    rw [h11, h01]
  apply SpecialLinearGroup.toGL_injective
  rw [matrixConjugation_toGL, mul_inv_eq_iff_eq_mul]
  apply Units.ext
  rw [Units.val_mul, Units.val_mul, hGm]
  change !![a, -c; c, a] * !![1 + l * i, l; l, 1 - l * i] =
    !![1 + l * κ * i, l * κ; l * κ, 1 - l * κ * i] * !![a, -c; c, a]
  rw [Matrix.mul_fin_two, Matrix.mul_fin_two]
  ext p q
  fin_cases p <;> fin_cases q
  · simp only [Fin.zero_eta, Fin.isValue, of_apply, cons_val', cons_val_zero, empty_val',
      cons_val_fin_one]
    linear_combination (-(i * l)) * hκ + (-(c * l + l * κ * c)) * hi
  · simp only [Fin.zero_eta, Fin.isValue, Fin.mk_one, of_apply, cons_val', cons_val_one,
      cons_val_zero, empty_val', cons_val_fin_one]
    linear_combination (-l) * hκ
  · simp only [Fin.mk_one, Fin.isValue, Fin.zero_eta, of_apply, cons_val', cons_val_zero,
      cons_val_one, empty_val', cons_val_fin_one]
    linear_combination (-l) * hκ
  · simp only [Fin.mk_one, Fin.isValue, of_apply, cons_val', cons_val_one, empty_val',
      cons_val_fin_one]
    linear_combination (i * l) * hκ + (c * l + l * κ * c) * hi

theorem matrixConjugation_rootSL_of_conj_eq_inv {i : F} (hi : i * i = -1) {G : GL (Fin 2) F}
    (hG : matrixConjugation F G (weyl F) = (weyl F)⁻¹) (l : F) :
    matrixConjugation F G (rootSL i hi l) =
      rootSL (-i) (neg_mul_neg_eq_neg_one hi)
        (l * (-(G.val 0 0 - G.val 1 0 * i) / (G.val 0 0 + G.val 1 0 * i))) := by
  obtain ⟨h11, h01⟩ := entries_of_conj_weyl_eq_inv hG
  set a := G.val 0 0 with ha
  set c := G.val 1 0 with hc
  have hdet := GeneralLinearGroup.det_ne_zero G
  rw [det_fin_two] at hdet
  have hD : a + c * i ≠ 0 := by
    intro h
    apply hdet
    change G.val 0 0 * G.val 1 1 - G.val 0 1 * G.val 1 0 = 0
    rw [h11, h01]
    linear_combination (-(a - c * i)) * h - c ^ 2 * hi
  set μ := -(a - c * i) / (a + c * i) with hμdef
  have hμ : μ * (a + c * i) = -(a - c * i) := by rw [hμdef]; field_simp
  have hGm : (G : Matrix (Fin 2) (Fin 2) F) = !![a, c; c, -a] := by
    rw [Matrix.eta_fin_two (G : Matrix (Fin 2) (Fin 2) F)]
    rw [h11, h01]
  apply SpecialLinearGroup.toGL_injective
  rw [matrixConjugation_toGL, mul_inv_eq_iff_eq_mul]
  apply Units.ext
  rw [Units.val_mul, Units.val_mul, hGm]
  change !![a, c; c, -a] * !![1 + l * i, l; l, 1 - l * i] =
    !![1 + l * μ * -i, l * μ; l * μ, 1 - l * μ * -i] * !![a, c; c, -a]
  rw [Matrix.mul_fin_two, Matrix.mul_fin_two]
  ext p q
  fin_cases p <;> fin_cases q
  · simp only [Fin.zero_eta, Fin.isValue, of_apply, cons_val', cons_val_zero, empty_val',
      cons_val_fin_one]
    linear_combination (i * l) * hμ + (c * l - l * μ * c) * hi
  · simp only [Fin.zero_eta, Fin.isValue, Fin.mk_one, of_apply, cons_val', cons_val_one,
      cons_val_zero, empty_val', cons_val_fin_one]
    linear_combination l * hμ
  · simp only [Fin.mk_one, Fin.isValue, Fin.zero_eta, of_apply, cons_val', cons_val_zero,
      cons_val_one, empty_val', cons_val_fin_one]
    linear_combination (-l) * hμ
  · simp only [Fin.mk_one, Fin.isValue, of_apply, cons_val', cons_val_one, empty_val',
      cons_val_fin_one]
    linear_combination (i * l) * hμ + (c * l - l * μ * c) * hi

theorem SL_inv_coe (A : SpecialLinearGroup (Fin 2) F) :
    ((A⁻¹ : SpecialLinearGroup (Fin 2) F) : Matrix (Fin 2) (Fin 2) F) =
      adjugate (A : Matrix (Fin 2) (Fin 2) F) := rfl

theorem SL_neg_coe (A : SpecialLinearGroup (Fin 2) F) :
    ((-A : SpecialLinearGroup (Fin 2) F) : Matrix (Fin 2) (Fin 2) F) =
      -(A : Matrix (Fin 2) (Fin 2) F) := rfl

theorem SL_ext_entries {A B : SpecialLinearGroup (Fin 2) F} (h00 : A 0 0 = B 0 0)
    (h01 : A 0 1 = B 0 1) (h10 : A 1 0 = B 1 0) (h11 : A 1 1 = B 1 1) : A = B := by
  apply Subtype.ext
  ext p q
  fin_cases p <;> fin_cases q
  · exact h00
  · exact h01
  · exact h10
  · exact h11

theorem symm_of_weyl_conj_eq_inv {Z : SpecialLinearGroup (Fin 2) F}
    (h : weyl F * Z * (weyl F)⁻¹ = Z⁻¹) : Z 0 1 = Z 1 0 := by
  have h' : weyl F * Z = Z⁻¹ * weyl F := by rw [← h]; group
  have hm := congrArg (fun A : SpecialLinearGroup (Fin 2) F => (A : Matrix (Fin 2) (Fin 2) F)) h'
  simp only [SL_mul_val, SL_inv_coe, weyl_val] at hm
  rw [Matrix.eta_fin_two (Z : Matrix (Fin 2) (Fin 2) F), adjugate_fin_two_of,
    Matrix.mul_fin_two, Matrix.mul_fin_two] at hm
  have h00 := congrFun (congrFun hm 0) 0
  simp only [of_apply, cons_val', cons_val_zero, empty_val', cons_val_fin_one,
    Fin.isValue] at h00
  linear_combination h00

theorem isotropic_of_commute_conj {Z t : SpecialLinearGroup (Fin 2) F}
    (hZ : Z 0 1 = Z 1 0) (ht : t ∈ Subgroup.centralizer {weyl F})
    (hcomm : Z * (t * Z * t⁻¹) = t * Z * t⁻¹ * Z) (htne : t 0 0 * t 1 0 ≠ 0) :
    (Z 0 0 - Z 1 1) ^ 2 + 4 * Z 0 1 ^ 2 = 0 := by
  obtain ⟨ht11, ht01⟩ := (CFSG.Wreathed.OddFieldTorus.mem_torus_coord_iff t).mp ht
  have hm := congrArg (fun A : SpecialLinearGroup (Fin 2) F => (A : Matrix (Fin 2) (Fin 2) F))
    hcomm
  simp only [SL_mul_val, SL_inv_coe] at hm
  have hZm : (Z : Matrix (Fin 2) (Fin 2) F) = !![Z 0 0, Z 0 1; Z 0 1, Z 1 1] := by
    ext p q
    fin_cases p <;> fin_cases q
    · rfl
    · rfl
    · exact hZ.symm
    · rfl
  have htm : (t : Matrix (Fin 2) (Fin 2) F) = !![t 0 0, -t 1 0; t 1 0, t 0 0] := by
    ext p q
    fin_cases p <;> fin_cases q
    · rfl
    · exact ht01
    · rfl
    · exact ht11
  rw [hZm, htm, adjugate_fin_two_of] at hm
  simp only [Matrix.mul_fin_two] at hm
  have h01 := congrFun (congrFun hm 0) 1
  simp only [of_apply, cons_val', cons_val_zero, cons_val_one, empty_val',
    cons_val_fin_one, Fin.isValue] at h01
  have key : t 0 0 * t 1 0 * ((Z 0 0 - Z 1 1) ^ 2 + 4 * Z 0 1 ^ 2) = 0 := by
    linear_combination h01
  exact (mul_eq_zero.mp key).resolve_left htne

theorem isSquare_neg_one_of_isotropic (h2 : (2 : F) ≠ 0) {Z : SpecialLinearGroup (Fin 2) F}
    (hZ : Z 0 1 = Z 1 0) (hiso : (Z 0 0 - Z 1 1) ^ 2 + 4 * Z 0 1 ^ 2 = 0)
    (h1 : Z ≠ 1) (hm1 : Z ≠ -1) : IsSquare (-1 : F) := by
  have hdet : Z 0 0 * Z 1 1 - Z 0 1 * Z 1 0 = 1 := by
    have h := Z.2
    rw [det_fin_two] at h
    exact h
  by_cases hβ : Z 0 1 = 0
  · exfalso
    have hαδ : Z 0 0 = Z 1 1 := by
      have h0 : (Z 0 0 - Z 1 1) ^ 2 = 0 := by rw [hβ] at hiso; linear_combination hiso
      exact sub_eq_zero.mp (pow_eq_zero_iff two_ne_zero |>.mp h0)
    have hβ' : Z 1 0 = 0 := by rw [← hZ, hβ]
    have hsq : (Z 0 0 - 1) * (Z 0 0 + 1) = 0 := by
      rw [hβ, ← hαδ] at hdet
      linear_combination hdet
    rcases mul_eq_zero.mp hsq with h | h
    · apply h1
      apply SL_ext_entries
      · show Z 0 0 = 1
        linear_combination h
      · show Z 0 1 = 0
        exact hβ
      · show Z 1 0 = 0
        exact hβ'
      · show Z 1 1 = 1
        linear_combination h - hαδ
    · apply hm1
      apply SL_ext_entries
      · show Z 0 0 = -1
        linear_combination h
      · show Z 0 1 = -0
        rw [hβ, neg_zero]
      · show Z 1 0 = -0
        rw [hβ', neg_zero]
      · show Z 1 1 = -1
        linear_combination h - hαδ
  · refine ⟨(Z 0 0 - Z 1 1) / (2 * Z 0 1), ?_⟩
    field_simp
    linear_combination -hiso

theorem eq_rootSL_of_isotropic (h2 : (2 : F) ≠ 0) {i : F} (hi : i * i = -1)
    {Z : SpecialLinearGroup (Fin 2) F} (hZ : Z 0 1 = Z 1 0)
    (hiso : (Z 0 0 - Z 1 1) ^ 2 + 4 * Z 0 1 ^ 2 = 0) :
    (∃ l, Z = rootSL i hi l ∨ Z = -rootSL i hi l) ∨
      (∃ l, Z = rootSL (-i) (neg_mul_neg_eq_neg_one hi) l ∨
        Z = -rootSL (-i) (neg_mul_neg_eq_neg_one hi) l) := by
  have hdet : Z 0 0 * Z 1 1 - Z 0 1 * Z 0 1 = 1 := by
    have h := Z.2
    rw [det_fin_two, ← hZ] at h
    exact h
  have hfac : (Z 0 0 - Z 1 1 - 2 * i * Z 0 1) * (Z 0 0 - Z 1 1 + 2 * i * Z 0 1) = 0 := by
    linear_combination hiso - 4 * Z 0 1 ^ 2 * hi
  have hsum : (Z 0 0 + Z 1 1 - 2) * (Z 0 0 + Z 1 1 + 2) = 0 := by
    linear_combination hiso + 4 * hdet
  have cancel2 : ∀ x y : F, 2 * x = 2 * y → x = y := fun x y h => mul_left_cancel₀ h2 h
  rcases mul_eq_zero.mp hfac with hA | hA <;> rcases mul_eq_zero.mp hsum with hS | hS
  · left
    refine ⟨Z 0 1, Or.inl (SL_ext_entries ?_ ?_ ?_ ?_)⟩
    · show Z 0 0 = 1 + Z 0 1 * i
      exact cancel2 _ _ (by linear_combination hA + hS)
    · show Z 0 1 = Z 0 1
      rfl
    · show Z 1 0 = Z 0 1
      exact hZ.symm
    · show Z 1 1 = 1 - Z 0 1 * i
      exact cancel2 _ _ (by linear_combination hS - hA)
  · left
    refine ⟨-Z 0 1, Or.inr (SL_ext_entries ?_ ?_ ?_ ?_)⟩
    · show Z 0 0 = -(1 + -Z 0 1 * i)
      exact cancel2 _ _ (by linear_combination hA + hS)
    · show Z 0 1 = -(-Z 0 1)
      rw [neg_neg]
    · show Z 1 0 = -(-Z 0 1)
      rw [neg_neg]
      exact hZ.symm
    · show Z 1 1 = -(1 - -Z 0 1 * i)
      exact cancel2 _ _ (by linear_combination hS - hA)
  · right
    refine ⟨Z 0 1, Or.inl (SL_ext_entries ?_ ?_ ?_ ?_)⟩
    · show Z 0 0 = 1 + Z 0 1 * -i
      exact cancel2 _ _ (by linear_combination hA + hS)
    · show Z 0 1 = Z 0 1
      rfl
    · show Z 1 0 = Z 0 1
      exact hZ.symm
    · show Z 1 1 = 1 - Z 0 1 * -i
      exact cancel2 _ _ (by linear_combination hS - hA)
  · right
    refine ⟨-Z 0 1, Or.inr (SL_ext_entries ?_ ?_ ?_ ?_)⟩
    · show Z 0 0 = -(1 + -Z 0 1 * -i)
      exact cancel2 _ _ (by linear_combination hA + hS)
    · show Z 0 1 = -(-Z 0 1)
      rw [neg_neg]
    · show Z 1 0 = -(-Z 0 1)
      rw [neg_neg]
      exact hZ.symm
    · show Z 1 1 = -(1 - -Z 0 1 * -i)
      exact cancel2 _ _ (by linear_combination hS - hA)

theorem exists_torus_mul_ne_zero [Finite F] (h2 : (2 : F) ≠ 0) (hq : 5 < Nat.card F) :
    ∃ t ∈ Subgroup.centralizer {weyl F}, t 0 0 * t 1 0 ≠ 0 := by
  classical
  by_contra hcon
  push Not at hcon
  have hw : weyl F ∈ Subgroup.centralizer {weyl F} :=
    Subgroup.mem_centralizer_singleton_iff.mpr rfl
  have h1 : (1 : SpecialLinearGroup (Fin 2) F) ∈ Subgroup.centralizer {weyl F} :=
    Subgroup.one_mem _
  have hm1 : (-1 : SpecialLinearGroup (Fin 2) F) ∈ Subgroup.centralizer {weyl F} :=
    Subgroup.mem_centralizer_singleton_iff.mpr (by rw [neg_one_mul, mul_neg_one])
  have hmw : -weyl F ∈ Subgroup.centralizer {weyl F} :=
    Subgroup.mem_centralizer_singleton_iff.mpr (by rw [neg_mul, mul_neg])
  have hsub : ((Subgroup.centralizer {weyl F} : Subgroup (SpecialLinearGroup (Fin 2) F)) :
      Set (SpecialLinearGroup (Fin 2) F)) ⊆
        (({1, -1, weyl F, -weyl F} : Finset (SpecialLinearGroup (Fin 2) F)) :
          Set (SpecialLinearGroup (Fin 2) F)) := by
    intro t ht
    have hsq := CFSG.Wreathed.OddFieldTorus.torus_sq_add_sq (L := F) ht
    simp only [Finset.coe_insert, Finset.coe_singleton, Set.mem_insert_iff,
      Set.mem_singleton_iff]
    rcases mul_eq_zero.mp (hcon t ht) with h0 | h0
    · have h10 : (t 1 0 - 1) * (t 1 0 + 1) = 0 := by rw [h0] at hsq; linear_combination hsq
      rcases mul_eq_zero.mp h10 with h | h
      · right; right; left
        apply CFSG.Wreathed.OddFieldTorus.torus_ext (L := F) ht hw
        · show t 0 0 = 0
          exact h0
        · show t 1 0 = 1
          linear_combination h
      · right; right; right
        apply CFSG.Wreathed.OddFieldTorus.torus_ext (L := F) ht hmw
        · show t 0 0 = -0
          rw [h0, neg_zero]
        · show t 1 0 = -1
          linear_combination h
    · have h00 : (t 0 0 - 1) * (t 0 0 + 1) = 0 := by rw [h0] at hsq; linear_combination hsq
      rcases mul_eq_zero.mp h00 with h | h
      · left
        apply CFSG.Wreathed.OddFieldTorus.torus_ext (L := F) ht h1
        · show t 0 0 = 1
          linear_combination h
        · show t 1 0 = 0
          exact h0
      · right; left
        apply CFSG.Wreathed.OddFieldTorus.torus_ext (L := F) ht hm1
        · show t 0 0 = -1
          linear_combination h
        · show t 1 0 = -0
          rw [h0, neg_zero]
  have hle : Nat.card (Subgroup.centralizer {weyl F} : Subgroup (SpecialLinearGroup (Fin 2) F))
      ≤ 4 := by
    have hc : Nat.card (Subgroup.centralizer {weyl F} : Subgroup (SpecialLinearGroup (Fin 2) F))
        = ((Subgroup.centralizer {weyl F} : Subgroup (SpecialLinearGroup (Fin 2) F)) :
          Set (SpecialLinearGroup (Fin 2) F)).ncard := Nat.card_coe_set_eq _
    rw [hc]
    calc _ ≤ ((({1, -1, weyl F, -weyl F} : Finset (SpecialLinearGroup (Fin 2) F)) :
          Set (SpecialLinearGroup (Fin 2) F))).ncard :=
          Set.ncard_le_ncard hsub (Finset.finite_toSet _)
      _ = ({1, -1, weyl F, -weyl F} : Finset (SpecialLinearGroup (Fin 2) F)).card :=
          Set.ncard_coe_finset _
      _ ≤ 4 := Finset.card_le_four
  have hT := CFSG.Wreathed.OddFieldTorus.torus_card h2 (L := F)
  have hT' : (Nat.card (Subgroup.centralizer {weyl F} :
      Subgroup (SpecialLinearGroup (Fin 2) F)) : ℤ) ≥ (Nat.card F : ℤ) - 1 := by
    change (Nat.card (CFSG.Wreathed.OddFieldTorus.torus F) : ℤ) ≥ _
    rw [hT]
    split_ifs <;> linarith
  have h5 : (5 : ℤ) < Nat.card F := by exact_mod_cast hq
  have h4 : (Nat.card (Subgroup.centralizer {weyl F} :
      Subgroup (SpecialLinearGroup (Fin 2) F)) : ℤ) ≤ 4 := by exact_mod_cast hle
  linarith

theorem toGL_rootSL_val (i : F) (hi : i * i = -1) (l : F) :
    (SpecialLinearGroup.toGL (rootSL i hi l)).val = !![1 + l * i, l; l, 1 - l * i] := rfl

theorem coordinateGLAction_rootSL_fix (i : F) (hi : i * i = -1) (l : F) :
    coordinateGLAction F (SpecialLinearGroup.toGL (rootSL i hi l)) (some i) = some i := by
  have hden : (SpecialLinearGroup.toGL (rootSL i hi l)).val 1 0 * i +
      (SpecialLinearGroup.toGL (rootSL i hi l)).val 1 1 = 1 := by
    rw [toGL_rootSL_val]
    simp
  rw [coordinateGLAction_finite F _ i (by rw [hden]; exact one_ne_zero), hden, div_one,
    toGL_rootSL_val]
  simp only [of_apply, cons_val', cons_val_zero, empty_val', cons_val_fin_one, cons_val_one,
    Fin.isValue, Option.some.injEq]
  linear_combination l * hi

theorem exists_coordinateGLAction_rootSL_eq (h2 : (2 : F) ≠ 0) (i : F) (hi : i * i = -1)
    {y : Omega F} (hy : y ≠ some i) :
    ∃ l, coordinateGLAction F (SpecialLinearGroup.toGL (rootSL i hi l)) (some (-i)) = y := by
  cases y with
  | none =>
    refine ⟨-i / 2, coordinateGLAction_finite_denominator_zero F _ _ ?_⟩
    rw [toGL_rootSL_val]
    simp only [of_apply, cons_val', cons_val_zero, empty_val', cons_val_fin_one, cons_val_one,
      Fin.isValue]
    field_simp
    linear_combination 2 * hi
  | some z =>
    have hz : z ≠ i := fun h => hy (by rw [h])
    have hD : 1 + i * z ≠ 0 := by
      intro h
      apply hz
      linear_combination (-i) * h + z * hi
    set l := (z + i) / (2 * (1 + i * z)) with hl_def
    have hl : l * (2 * (1 + i * z)) = z + i := by
      rw [hl_def]
      exact div_mul_cancel₀ _ (mul_ne_zero h2 hD)
    refine ⟨l, ?_⟩
    have hden : (SpecialLinearGroup.toGL (rootSL i hi l)).val 1 0 * -i +
        (SpecialLinearGroup.toGL (rootSL i hi l)).val 1 1 ≠ 0 := by
      rw [toGL_rootSL_val]
      simp only [of_apply, cons_val', cons_val_zero, empty_val', cons_val_fin_one, cons_val_one,
        Fin.isValue]
      intro h
      apply h2
      linear_combination (1 + i * z) * h + i * hl + hi
    rw [coordinateGLAction_finite F _ _ hden, Option.some.injEq, div_eq_iff hden,
      toGL_rootSL_val]
    simp only [of_apply, cons_val', cons_val_zero, empty_val', cons_val_fin_one, cons_val_one,
      Fin.isValue]
    linear_combination hl - l * hi

theorem coordinateGLAction_fix_of_commute {i : F} (hi : i * i = -1) {G : GL (Fin 2) F}
    (hG : G * SpecialLinearGroup.toGL (weyl F) = SpecialLinearGroup.toGL (weyl F) * G) :
    coordinateGLAction F G (some i) = some i := by
  obtain ⟨h11, h01⟩ := entries_of_commute_weyl hG
  have hne : G.val 0 0 + G.val 1 0 * i ≠ 0 := by
    have h := sub_mul_ne_zero_of_commute_weyl (neg_mul_neg_eq_neg_one hi) hG
    simpa using h
  have hden : G.val 1 0 * i + G.val 1 1 ≠ 0 := by
    rw [h11]
    intro h
    exact hne (by linear_combination h)
  rw [coordinateGLAction_finite F G i hden, Option.some.injEq, div_eq_iff hden, h11, h01]
  linear_combination (-G.val 1 0) * hi

theorem commute_weyl_of_coordinateGLAction_fix (h2 : (2 : F) ≠ 0) {i : F} (hi : i * i = -1)
    {G : GL (Fin 2) F} (hp : coordinateGLAction F G (some i) = some i)
    (hm : coordinateGLAction F G (some (-i)) = some (-i)) :
    G * SpecialLinearGroup.toGL (weyl F) = SpecialLinearGroup.toGL (weyl F) * G := by
  have hi0 : i ≠ 0 := by
    rintro rfl
    rw [mul_zero] at hi
    exact one_ne_zero (neg_eq_zero.mp hi.symm)
  rw [coordinateGLAction_some_eq_some_iff] at hp hm
  have h01 : G.val 0 1 = -G.val 1 0 := by
    have h : (2 : F) * (G.val 0 1 + G.val 1 0) = 0 := by
      linear_combination -hp - hm + 2 * G.val 1 0 * hi
    have := (mul_eq_zero.mp h).resolve_left h2
    linear_combination this
  have h11 : G.val 1 1 = G.val 0 0 := by
    have h : (2 * i) * (G.val 1 1 - G.val 0 0) = 0 := by linear_combination hp - hm
    have := (mul_eq_zero.mp h).resolve_left (mul_ne_zero h2 hi0)
    linear_combination this
  apply Units.ext
  rw [Units.val_mul, Units.val_mul, toGL_weyl_coe,
    Matrix.eta_fin_two (G : Matrix (Fin 2) (Fin 2) F)]
  rw [h01, h11, Matrix.mul_fin_two, Matrix.mul_fin_two]
  ext p q
  fin_cases p <;> fin_cases q <;> simp

@[expose] noncomputable def weylShift (y : F) (hy : y * y + 1 ≠ 0) : GL (Fin 2) F :=
  GeneralLinearGroup.mkOfDetNeZero !![y, -1; 1, y] (by
    rw [det_fin_two_of]
    intro h
    exact hy (by linear_combination h))

theorem weylShift_val (y : F) (hy : y * y + 1 ≠ 0) :
    (weylShift y hy).val = !![y, -1; 1, y] := rfl

theorem weylShift_commute (y : F) (hy : y * y + 1 ≠ 0) :
    weylShift y hy * SpecialLinearGroup.toGL (weyl F) =
      SpecialLinearGroup.toGL (weyl F) * weylShift y hy := by
  apply Units.ext
  rw [Units.val_mul, Units.val_mul, toGL_weyl_coe, weylShift_val, Matrix.mul_fin_two,
    Matrix.mul_fin_two]
  ext p q
  fin_cases p <;> fin_cases q <;> simp

theorem coordinateGLAction_weylShift_none (y : F) (hy : y * y + 1 ≠ 0) :
    coordinateGLAction F (weylShift y hy) none = some y := by
  rw [coordinateGLAction_infinity F _ (by rw [weylShift_val]; simp), weylShift_val]
  simp

theorem eq_weyl_or_eq_inv_of_commute (h2 : (2 : F) ≠ 0) {G : GL (Fin 2) F}
    (hG : G * SpecialLinearGroup.toGL (weyl F) = SpecialLinearGroup.toGL (weyl F) * G)
    (hc : G.val 1 0 ≠ 0) {J : SpecialLinearGroup (Fin 2) F} (hJ : J 0 0 + J 1 1 = 0)
    (hGJ : G * SpecialLinearGroup.toGL J = SpecialLinearGroup.toGL J * G) :
    J = weyl F ∨ J = (weyl F)⁻¹ := by
  obtain ⟨h11, h01⟩ := entries_of_commute_weyl hG
  have hm := congrArg (fun A : GL (Fin 2) F => (A : Matrix (Fin 2) (Fin 2) F)) hGJ
  simp only [Units.val_mul] at hm
  have e00 := congrFun (congrFun hm 0) 0
  have e01 := congrFun (congrFun hm 0) 1
  simp only [Matrix.mul_apply, Fin.sum_univ_two] at e00 e01
  change G.val 0 0 * J 0 0 + G.val 0 1 * J 1 0 = J 0 0 * G.val 0 0 + J 0 1 * G.val 1 0 at e00
  change G.val 0 0 * J 0 1 + G.val 0 1 * J 1 1 = J 0 0 * G.val 0 1 + J 0 1 * G.val 1 1 at e01
  rw [h01] at e00
  rw [h01, h11] at e01
  have hγ : J 1 0 = -J 0 1 := by
    have h : G.val 1 0 * (J 1 0 + J 0 1) = 0 := by linear_combination -e00
    have := (mul_eq_zero.mp h).resolve_left hc
    linear_combination this
  have hα : J 0 0 = 0 := by
    have h : (2 * G.val 1 0) * J 0 0 = 0 := by linear_combination e01 + G.val 1 0 * hJ
    exact (mul_eq_zero.mp h).resolve_left (mul_ne_zero h2 hc)
  have hδ : J 1 1 = 0 := by linear_combination hJ - hα
  have hdet : J 0 1 * J 0 1 = 1 := by
    have h := J.2
    rw [det_fin_two, hα, hδ, hγ] at h
    linear_combination h
  have hcases : (J 0 1 + 1) * (J 0 1 - 1) = 0 := by linear_combination hdet
  rcases mul_eq_zero.mp hcases with h | h
  · left
    apply SL_ext_entries <;> rw [weyl_val] <;> simp [hα, hδ, hγ] <;>
      first | linear_combination h | linear_combination -h
  · right
    apply SL_ext_entries <;> rw [weyl_inv_val] <;> simp [hα, hδ, hγ] <;>
      linear_combination h

theorem closure_upperSL_lowerSL :
    Subgroup.closure (Set.range (upperSL F) ∪ Set.range (lowerSL F)) = ⊤ := by
  rw [eq_top_iff, ← SpecialLinearGroup.closure_range_toSpecialLinearGroup_eq_top_of_field,
    Subgroup.closure_le]
  rintro _ ⟨⟨a, b, hab, c⟩, rfl⟩
  apply Subgroup.subset_closure
  rw [TransvectionStruct.toSpecialLinearGroup_mk]
  fin_cases a <;> fin_cases b
  · exact absurd rfl hab
  · left
    exact ⟨c, upperSL_eq_transvection F c⟩
  · right
    exact ⟨c, lowerSL_eq_transvection F c⟩
  · exact absurd rfl hab

@[expose] noncomputable def eigenMatrix (h2 : (2 : F) ≠ 0) {i : F} (hi : i * i = -1) :
    GL (Fin 2) F :=
  GeneralLinearGroup.mkOfDetNeZero !![1, 1; -i, i] (by
    rw [det_fin_two_of]
    intro h
    have hi0 : i ≠ 0 := by
      rintro rfl
      rw [mul_zero] at hi
      exact one_ne_zero (neg_eq_zero.mp hi.symm)
    exact mul_ne_zero h2 hi0 (by linear_combination h))

theorem matrixConjugation_eigenMatrix_upperSL (h2 : (2 : F) ≠ 0) {i : F} (hi : i * i = -1)
    (l : F) : matrixConjugation F (eigenMatrix h2 hi) (upperSL F (2 * i * l)) = rootSL i hi l := by
  apply SpecialLinearGroup.toGL_injective
  rw [matrixConjugation_toGL, mul_inv_eq_iff_eq_mul]
  apply Units.ext
  rw [Units.val_mul, Units.val_mul]
  change !![1, 1; -i, i] * !![1, 2 * i * l; 0, 1] =
    !![1 + l * i, l; l, 1 - l * i] * !![1, 1; -i, i]
  rw [Matrix.mul_fin_two, Matrix.mul_fin_two]
  ext p q
  fin_cases p <;> fin_cases q
  · simp only [Fin.zero_eta, Fin.isValue, of_apply, cons_val', cons_val_zero, empty_val',
      cons_val_fin_one]
    ring
  · simp only [Fin.zero_eta, Fin.isValue, Fin.mk_one, of_apply, cons_val', cons_val_one,
      cons_val_zero, empty_val', cons_val_fin_one]
    ring
  · simp only [Fin.mk_one, Fin.isValue, Fin.zero_eta, of_apply, cons_val', cons_val_zero,
      cons_val_one, empty_val', cons_val_fin_one]
    linear_combination (-l) * hi
  · simp only [Fin.mk_one, Fin.isValue, of_apply, cons_val', cons_val_one, empty_val',
      cons_val_fin_one]
    linear_combination (-l) * hi

theorem matrixConjugation_eigenMatrix_lowerSL (h2 : (2 : F) ≠ 0) {i : F} (hi : i * i = -1)
    (l : F) : matrixConjugation F (eigenMatrix h2 hi) (lowerSL F (-(2 * i * l))) =
      rootSL (-i) (neg_mul_neg_eq_neg_one hi) l := by
  apply SpecialLinearGroup.toGL_injective
  rw [matrixConjugation_toGL, mul_inv_eq_iff_eq_mul]
  apply Units.ext
  rw [Units.val_mul, Units.val_mul]
  change !![1, 1; -i, i] * !![1, 0; -(2 * i * l), 1] =
    !![1 + l * -i, l; l, 1 - l * -i] * !![1, 1; -i, i]
  rw [Matrix.mul_fin_two, Matrix.mul_fin_two]
  ext p q
  fin_cases p <;> fin_cases q
  · simp only [Fin.zero_eta, Fin.isValue, of_apply, cons_val', cons_val_zero, empty_val',
      cons_val_fin_one]
    ring
  · simp only [Fin.zero_eta, Fin.isValue, Fin.mk_one, of_apply, cons_val', cons_val_one,
      cons_val_zero, empty_val', cons_val_fin_one]
    ring
  · simp only [Fin.mk_one, Fin.isValue, Fin.zero_eta, of_apply, cons_val', cons_val_zero,
      cons_val_one, empty_val', cons_val_fin_one]
    linear_combination (-l) * hi
  · simp only [Fin.mk_one, Fin.isValue, of_apply, cons_val', cons_val_one, empty_val',
      cons_val_fin_one]
    linear_combination (-l) * hi

theorem closure_rootSL (h2 : (2 : F) ≠ 0) {i : F} (hi : i * i = -1) :
    Subgroup.closure (Set.range (rootSL i hi) ∪
      Set.range (rootSL (-i) (neg_mul_neg_eq_neg_one hi))) = ⊤ := by
  have hi0 : i ≠ 0 := by
    rintro rfl
    rw [mul_zero] at hi
    exact one_ne_zero (neg_eq_zero.mp hi.symm)
  set S := Subgroup.closure (Set.range (rootSL i hi) ∪
    Set.range (rootSL (-i) (neg_mul_neg_eq_neg_one hi)))
  let φ := (matrixConjugation F (eigenMatrix h2 hi)).toMonoidHom
  have hmap : (⊤ : Subgroup (SpecialLinearGroup (Fin 2) F)).map φ ≤ S := by
    rw [← closure_upperSL_lowerSL, MonoidHom.map_closure, Subgroup.closure_le]
    rintro _ ⟨X, hX, rfl⟩
    rcases hX with ⟨t, rfl⟩ | ⟨t, rfl⟩
    · apply Subgroup.subset_closure
      left
      refine ⟨t / (2 * i), ?_⟩
      change rootSL i hi (t / (2 * i)) = matrixConjugation F (eigenMatrix h2 hi) (upperSL F t)
      rw [← matrixConjugation_eigenMatrix_upperSL h2 hi]
      congr 2
      field_simp
    · apply Subgroup.subset_closure
      right
      refine ⟨-t / (2 * i), ?_⟩
      change rootSL (-i) _ (-t / (2 * i)) =
        matrixConjugation F (eigenMatrix h2 hi) (lowerSL F t)
      rw [← matrixConjugation_eigenMatrix_lowerSL h2 hi]
      congr 2
      field_simp
  rw [eq_top_iff]
  intro Z _
  apply hmap
  refine ⟨(matrixConjugation F (eigenMatrix h2 hi)).symm Z, Subgroup.mem_top _, ?_⟩
  change matrixConjugation F (eigenMatrix h2 hi)
    ((matrixConjugation F (eigenMatrix h2 hi)).symm Z) = Z
  exact MulEquiv.apply_symm_apply _ Z

end CFSG.Wreathed.OriginalAllPrime.ModelSignalizers
