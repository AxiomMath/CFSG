module

public import CFSG.HardMathSupport.Solomon.Coordinator.ChevQ.KS.E8FiveTwoHeis

public section

namespace CFSG.HardMathSupport.Solomon.Coordinator.ChevQ.KSE8Five

namespace Two

open Matrix CFSG.RankThree.Classical2 CFSG.RankThree.Classical CFSG.LocalAnalysis.ComponentInitial
  CFSG.LocalAnalysis.ComponentInitial.UnitaryHigher CFSG.RankThree.PartOne.KCUnitaryModel
  CFSG.LieType.SeitzGeneration CFSG.LieType.Universal.Unitary CFSG.LieType.BorelTits
open scoped MatrixGroups

section Scalar

variable {Ω : Type} [Field Ω] {n : ℕ}

theorem exists_scalar_of_commute_transvection {C : Matrix (Fin n) (Fin n) Ω}
    (h : ∀ (i j : Fin n) (hij : i ≠ j),
      Commute C ((SpecialLinearGroup.transvection hij (1 : Ω) : SL(n, Ω)) :
        Matrix (Fin n) (Fin n) Ω)) :
    ∃ c : Ω, C = c • 1 := by
  obtain ⟨c, hc⟩ := Matrix.mem_range_scalar_of_commute_single (M := C) (fun i j hij => by
    have h1 := (h i j hij).eq
    rw [SpecialLinearGroup.transvection_coe] at h1
    simp only [mul_add, add_mul, mul_one, one_mul] at h1
    exact (add_left_cancel h1).symm)
  exact ⟨c, by rw [← hc, Matrix.scalar_apply, Matrix.smul_one_eq_diagonal]⟩

end Scalar

section TauG

variable {Ω : Type} [Field Ω] {n : ℕ}

@[expose] noncomputable def tauG (σ : Ω →+* Ω) : GL (Fin n) Ω →* GL (Fin n) Ω :=
  invTransposeHom.comp (Matrix.GeneralLinearGroup.map σ)

theorem coe_tauG (σ : Ω →+* Ω) (X : GL (Fin n) Ω) :
    (tauG σ X : Matrix (Fin n) (Fin n) Ω) = (((X : Matrix (Fin n) (Fin n) Ω).map σ)⁻¹)ᵀ := by
  change (invTransposeHom (Matrix.GeneralLinearGroup.map σ X) : Matrix (Fin n) (Fin n) Ω) = _
  rw [coe_invTransposeHom, Matrix.coe_units_inv, coe_generalLinearGroup_map]

theorem tauG_tauG (σ : Ω →+* Ω) (X : GL (Fin n) Ω) :
    tauG σ (tauG σ X) =
      Matrix.GeneralLinearGroup.map σ (Matrix.GeneralLinearGroup.map σ X) := by
  change invTransposeHom (Matrix.GeneralLinearGroup.map σ
    (invTransposeHom (Matrix.GeneralLinearGroup.map σ X))) = _
  rw [map_invTransposeHom, invTransposeHom_invTransposeHom]

theorem det_tauG (σ : Ω →+* Ω) {X : GL (Fin n) Ω} (hX : (X : Matrix (Fin n) (Fin n) Ω).det = 1) :
    (tauG σ X : Matrix (Fin n) (Fin n) Ω).det = 1 := by
  have h1 : ((X : Matrix (Fin n) (Fin n) Ω).map σ).det = 1 := by
    have := RingHom.map_det σ (X : Matrix (Fin n) (Fin n) Ω)
    rw [hX, map_one] at this
    exact this.symm
  rw [coe_tauG, Matrix.det_transpose, Matrix.det_nonsing_inv, h1]
  simp

theorem exists_scalar_tauG [NeZero n] (σ : Ω →+* Ω) (M : GL (Fin n) Ω)
    (h : ∀ X : GL (Fin n) Ω, (X : Matrix (Fin n) (Fin n) Ω).det = 1 →
      tauG σ (M * X * M⁻¹) = M * tauG σ X * M⁻¹) :
    ∃ c : Ω, c ≠ 0 ∧
      (tauG σ M : Matrix (Fin n) (Fin n) Ω) = c • (M : Matrix (Fin n) (Fin n) Ω) := by
  set C : GL (Fin n) Ω := M⁻¹ * tauG σ M with hC
  have hcomm : ∀ (i j : Fin n) (hij : i ≠ j),
      Commute (C : Matrix (Fin n) (Fin n) Ω)
        ((SpecialLinearGroup.transvection hij (1 : Ω) : SL(n, Ω)) : Matrix (Fin n) (Fin n) Ω) := by
    intro i j hij
    set Y : GL (Fin n) Ω := Matrix.SpecialLinearGroup.toGL (SpecialLinearGroup.transvection hij 1)
      with hY
    have hYdet : (Y : Matrix (Fin n) (Fin n) Ω).det = 1 := (SpecialLinearGroup.transvection hij 1).2
    have hYfix : Matrix.GeneralLinearGroup.map σ (Matrix.GeneralLinearGroup.map σ Y) = Y := by
      refine Units.ext ?_
      rw [coe_generalLinearGroup_map, coe_generalLinearGroup_map]
      change ((1 + Matrix.single i j (1 : Ω)).map σ).map σ = 1 + Matrix.single i j (1 : Ω)
      simp [Matrix.map_add, Matrix.map_one, Matrix.map_single]
    have hX := h (tauG σ Y) (det_tauG σ hYdet)
    rw [map_mul, map_mul, map_inv] at hX
    simp only [tauG_tauG, hYfix] at hX
    have hX' : tauG σ M * Y = M * Y * M⁻¹ * tauG σ M := by
      rw [mul_inv_eq_iff_eq_mul] at hX
      exact hX
    have hCY : C * Y = Y * C := by
      calc C * Y = M⁻¹ * (tauG σ M * Y) := by rw [hC, mul_assoc]
        _ = M⁻¹ * (M * Y * M⁻¹ * tauG σ M) := by rw [hX']
        _ = Y * C := by rw [hC]; group
    have := congrArg (fun g : GL (Fin n) Ω => (g : Matrix (Fin n) (Fin n) Ω)) hCY
    exact this
  obtain ⟨c, hc⟩ := exists_scalar_of_commute_transvection hcomm
  have hc0 : c ≠ 0 := by
    rintro rfl
    have h1 := Units.mul_inv C
    rw [hc, zero_smul, Matrix.zero_mul] at h1
    have h2 := congrFun (congrFun h1 (0 : Fin n)) (0 : Fin n)
    simp at h2
  refine ⟨c, hc0, ?_⟩
  have hτM : tauG σ M = M * C := by rw [hC]; group
  rw [hτM, Units.val_mul, hc, Matrix.mul_smul, Matrix.mul_one]

end TauG

section FieldF

variable {ℓ : ℕ} {Ω : Type} [Field Ω] [IsAlgClosed Ω] [Fact ℓ.Prime] [CharP Ω ℓ]

variable (ℓ Ω) in
@[expose] noncomputable def subfieldSq (f : ℕ) : Subfield Ω :=
  (iterateFrobenius Ω ℓ (2 * f)).eqLocusField (RingHom.id Ω)

theorem mem_subfieldSq {f : ℕ} {c : Ω} :
    c ∈ subfieldSq ℓ Ω f ↔ c ^ (ℓ ^ f) ^ 2 = c := by
  change iterateFrobenius Ω ℓ (2 * f) c = c ↔ _
  rw [iterateFrobenius_def, ← pow_mul, mul_comm 2 f, pow_mul]

theorem card_subfieldSq {f : ℕ} (hf : 1 ≤ f) : Nat.card (subfieldSq ℓ Ω f) = ℓ ^ (2 * f) := by
  rw [← CFSG.RankThree.Classical2.natCard_setOf_pow_eq_self (Ω := Ω) (ℓ := ℓ)
    (by omega : 2 * f ≠ 0)]
  refine Nat.card_congr (Equiv.subtypeEquivRight fun c => ?_)
  change iterateFrobenius Ω ℓ (2 * f) c = c ↔ _
  rw [iterateFrobenius_def]
  exact Iff.rfl

theorem finite_subfieldSq {f : ℕ} (hf : 1 ≤ f) : Finite (subfieldSq ℓ Ω f) :=
  Nat.finite_of_card_ne_zero (by
    rw [card_subfieldSq hf]
    exact (pow_pos (Fact.out : ℓ.Prime).pos _).ne')

theorem unitaryFieldData_subfieldSq {f : ℕ} (hf : 1 ≤ f) :
    UnitaryFieldData ℓ f (subfieldSq ℓ Ω f) :=
  ⟨Fact.out, hf, card_subfieldSq hf⟩

theorem coe_bar_subfieldSq {f : ℕ} (hf : 1 ≤ f) (c : subfieldSq ℓ Ω f) :
    (((unitaryFieldData_subfieldSq (Ω := Ω) hf).bar c : subfieldSq ℓ Ω f) : Ω) =
      iterateFrobenius Ω ℓ f (c : Ω) := by
  rw [UnitaryFieldData.bar_apply, iterateFrobenius_def]
  rfl

end FieldF

section Descent

variable {Ω : Type} [Field Ω] {n : ℕ}

theorem exists_gl_of_entries (F : Subfield Ω) (g : GL (Fin n) Ω)
    (hg : ∀ i j, (g : Matrix (Fin n) (Fin n) Ω) i j ∈ F)
    (hgi : ∀ i j, ((g⁻¹ : GL (Fin n) Ω) : Matrix (Fin n) (Fin n) Ω) i j ∈ F) :
    ∃ g₀ : GL (Fin n) F, subfieldGL F n g₀ = g := by
  let M : Matrix (Fin n) (Fin n) F :=
    Matrix.of fun i j => ⟨(g : Matrix (Fin n) (Fin n) Ω) i j, hg i j⟩
  let N : Matrix (Fin n) (Fin n) F :=
    Matrix.of fun i j => ⟨((g⁻¹ : GL (Fin n) Ω) : Matrix (Fin n) (Fin n) Ω) i j, hgi i j⟩
  have hM : M.map F.subtype = g := Matrix.ext fun _ _ => rfl
  have hN : N.map F.subtype = ((g⁻¹ : GL (Fin n) Ω) : Matrix (Fin n) (Fin n) Ω) :=
    Matrix.ext fun _ _ => rfl
  have hinj := Matrix.map_injective (m := Fin n) (n := Fin n)
    (f := (F.subtype : F → Ω)) Subtype.val_injective
  have hMN : M * N = 1 := hinj (by
    change (M * N).map F.subtype = (1 : Matrix (Fin n) (Fin n) F).map F.subtype
    rw [Matrix.map_mul, hM, hN, Matrix.map_one _ (map_zero _) (map_one _), ← Units.val_mul,
      mul_inv_cancel, Units.val_one])
  have hNM : N * M = 1 := hinj (by
    change (N * M).map F.subtype = (1 : Matrix (Fin n) (Fin n) F).map F.subtype
    rw [Matrix.map_mul, hM, hN, Matrix.map_one _ (map_zero _) (map_one _), ← Units.val_mul,
      inv_mul_cancel, Units.val_one])
  exact ⟨⟨M, N, hMN, hNM⟩, Units.ext hM⟩

theorem map_map_eq_of_unitary (σ : Ω →+* Ω) {U : Matrix (Fin n) (Fin n) Ω}
    (h : (U.map σ)ᵀ * U = 1) : (U.map σ).map σ = U := by
  have hUV : U * (U.map σ)ᵀ = 1 := mul_eq_one_comm.1 h
  have h1 : (U.map σ) * Uᵀ = 1 := by
    have := congrArg Matrix.transpose hUV
    rwa [Matrix.transpose_mul, Matrix.transpose_transpose, Matrix.transpose_one] at this
  have h2 : ((U.map σ).map σ)ᵀ * (U.map σ) = 1 := by
    have := congrArg (fun A : Matrix (Fin n) (Fin n) Ω => A.map σ) h
    simp only [Matrix.map_mul, Matrix.map_one _ (map_zero σ) (map_one σ)] at this
    rwa [Matrix.transpose_map] at this
  have h3 : ((U.map σ).map σ)ᵀ = Uᵀ := by
    have e1 := Matrix.inv_eq_left_inv h2
    have e2 := Matrix.inv_eq_right_inv h1
    rw [← e1, e2]
  have := congrArg Matrix.transpose h3
  rwa [Matrix.transpose_transpose, Matrix.transpose_transpose] at this

end Descent

section Unitarize

variable {ℓ f : ℕ} {Ω : Type} [Field Ω] [IsAlgClosed Ω] [Fact ℓ.Prime] [CharP Ω ℓ]

theorem exists_unitary_gl (hf : 1 ≤ f) (Mt : GL (Fin 5) Ω) {c : Ω}
    (hMt : ((Mt : Matrix (Fin 5) (Fin 5) Ω).map (iterateFrobenius Ω ℓ f))ᵀ *
      (Mt : Matrix (Fin 5) (Fin 5) Ω) = c • 1) (hc : c ≠ 0) :
    ∃ (μ : Ω) (g : GL (Fin 5) (subfieldSq ℓ Ω f)), μ ≠ 0 ∧
      g ∈ primeFormUnitary (unitaryFieldData_subfieldSq (Ω := Ω) hf)
        (idGram (subfieldSq ℓ Ω f) 5) ∧
      ((subfieldGL (subfieldSq ℓ Ω f) 5 g : GL (Fin 5) Ω) : Matrix (Fin 5) (Fin 5) Ω) =
        μ • (Mt : Matrix (Fin 5) (Fin 5) Ω) := by
  classical
  set σ : Ω →+* Ω := iterateFrobenius Ω ℓ f with hσdef
  have hσ : ∀ x, σ x = x ^ ℓ ^ f := fun x => iterateFrobenius_def ℓ f x
  obtain ⟨μ, hμ⟩ := IsAlgClosed.exists_pow_nat_eq c⁻¹ (Nat.succ_pos (ℓ ^ f))
  have hμ0 : μ ≠ 0 := by
    rintro rfl
    rw [zero_pow (Nat.succ_ne_zero _)] at hμ
    exact inv_ne_zero hc hμ.symm
  set U : Matrix (Fin 5) (Fin 5) Ω := μ • (Mt : Matrix (Fin 5) (Fin 5) Ω) with hUdef
  have hU : (U.map σ)ᵀ * U = 1 := by
    have h1 : (U.map σ)ᵀ = σ μ • ((Mt : Matrix (Fin 5) (Fin 5) Ω).map σ)ᵀ := by
      ext i j
      simp [hUdef, Matrix.transpose_apply, Matrix.map_apply, map_mul]
    rw [h1, hUdef, Matrix.smul_mul, Matrix.mul_smul, smul_smul, hMt, smul_smul]
    have h2 : σ μ * μ * c = 1 := by
      rw [hσ, ← pow_succ, hμ, inv_mul_cancel₀ hc]
    rw [h2, one_smul]
  have hU' : U * (U.map σ)ᵀ = 1 := mul_eq_one_comm.1 hU
  let gU : GL (Fin 5) Ω := ⟨U, (U.map σ)ᵀ, hU', hU⟩
  have hgU : (gU : Matrix (Fin 5) (Fin 5) Ω) = U := rfl
  have hgUi : ((gU⁻¹ : GL (Fin 5) Ω) : Matrix (Fin 5) (Fin 5) Ω) = (U.map σ)ᵀ := rfl
  have hsq := map_map_eq_of_unitary σ hU
  have hmemF : ∀ x : Ω, σ (σ x) = x → x ∈ subfieldSq ℓ Ω f := fun x hx => by
    rw [mem_subfieldSq]
    calc x ^ (ℓ ^ f) ^ 2 = (x ^ ℓ ^ f) ^ ℓ ^ f := by rw [sq, pow_mul]
      _ = σ (σ x) := by rw [hσ, hσ]
      _ = x := hx
  have hUF : ∀ i j, (gU : Matrix (Fin 5) (Fin 5) Ω) i j ∈ subfieldSq ℓ Ω f := fun i j => by
    refine hmemF _ ?_
    have := congrFun (congrFun hsq i) j
    simpa [Matrix.map_apply] using this
  have hVF : ∀ i j, ((gU⁻¹ : GL (Fin 5) Ω) : Matrix (Fin 5) (Fin 5) Ω) i j ∈
      subfieldSq ℓ Ω f := fun i j => by
    rw [hgUi, Matrix.transpose_apply, Matrix.map_apply]
    refine hmemF _ ?_
    have hu : σ (σ ((U : Matrix (Fin 5) (Fin 5) Ω) j i)) = (U : Matrix (Fin 5) (Fin 5) Ω) j i := by
      have := congrFun (congrFun hsq j) i
      simpa [Matrix.map_apply] using this
    rw [hu]
  obtain ⟨g, hg⟩ := exists_gl_of_entries (subfieldSq ℓ Ω f) gU hUF hVF
  have hgmat : (g : Matrix (Fin 5) (Fin 5) (subfieldSq ℓ Ω f)).map (subfieldSq ℓ Ω f).subtype =
      U := by
    have := congrArg (fun x : GL (Fin 5) Ω => (x : Matrix (Fin 5) (Fin 5) Ω)) hg
    exact this
  refine ⟨μ, g, hμ0, ?_, by rw [hg]⟩
  rw [mem_primeFormUnitary]
  refine Matrix.map_injective (f := ((subfieldSq ℓ Ω f).subtype : subfieldSq ℓ Ω f → Ω))
    Subtype.val_injective ?_
  change (((g : Matrix (Fin 5) (Fin 5) (subfieldSq ℓ Ω f)).map
    (unitaryFieldData_subfieldSq (Ω := Ω) hf).bar)ᵀ * idGram (subfieldSq ℓ Ω f) 5 *
      (g : Matrix (Fin 5) (Fin 5) (subfieldSq ℓ Ω f))).map (subfieldSq ℓ Ω f).subtype =
    (idGram (subfieldSq ℓ Ω f) 5).map (subfieldSq ℓ Ω f).subtype
  have hbarmap : ((g : Matrix (Fin 5) (Fin 5) (subfieldSq ℓ Ω f)).map
      (unitaryFieldData_subfieldSq (Ω := Ω) hf).bar).map (subfieldSq ℓ Ω f).subtype =
        U.map σ := by
    rw [← hgmat]
    ext i j
    simp only [Matrix.map_apply]
    exact coe_bar_subfieldSq hf _
  rw [Matrix.map_mul, Matrix.map_mul, Matrix.transpose_map, hbarmap, hgmat]
  simp only [idGram, Units.val_one, Matrix.map_one _ (map_zero _) (map_one _), Matrix.mul_one]
  exact hU

end Unitarize

section Compat

variable {Ω : Type} [Field Ω] {n : ℕ}

theorem det_conj_eq_one (G X : GL (Fin n) Ω) (hX : (X : Matrix (Fin n) (Fin n) Ω).det = 1) :
    ((G * X * G⁻¹ : GL (Fin n) Ω) : Matrix (Fin n) (Fin n) Ω).det = 1 := by
  rw [Units.val_mul, Units.val_mul, Matrix.det_mul, Matrix.det_mul, hX, mul_one, ← Matrix.det_mul,
    Units.mul_inv, Matrix.det_one]

theorem tauG_compat_conj (σ : Ω →+* Ω) (A H M : GL (Fin n) Ω)
    (hdetH : (H : Matrix (Fin n) (Fin n) Ω).det = 1)
    (htw : ∀ X : GL (Fin n) Ω, (X : Matrix (Fin n) (Fin n) Ω).det = 1 →
      H⁻¹ * (A * tauG σ (H * X * H⁻¹) * A⁻¹) * H = tauG σ X)
    (hM : ∀ X : GL (Fin n) Ω, (X : Matrix (Fin n) (Fin n) Ω).det = 1 →
      A * tauG σ (M * X * M⁻¹) * A⁻¹ = M * (A * tauG σ X * A⁻¹) * M⁻¹)
    (X : GL (Fin n) Ω) (hX : (X : Matrix (Fin n) (Fin n) Ω).det = 1) :
    tauG σ ((H⁻¹ * M * H) * X * (H⁻¹ * M * H)⁻¹) =
      (H⁻¹ * M * H) * tauG σ X * (H⁻¹ * M * H)⁻¹ := by
  set Y : GL (Fin n) Ω := H * X * H⁻¹ with hY
  have hYdet : (Y : Matrix (Fin n) (Fin n) Ω).det = 1 := det_conj_eq_one H X hX
  have e1 : A * tauG σ Y * A⁻¹ = H * tauG σ X * H⁻¹ := by
    have := htw X hX
    calc A * tauG σ Y * A⁻¹ = H * (H⁻¹ * (A * tauG σ Y * A⁻¹) * H) * H⁻¹ := by group
      _ = H * tauG σ X * H⁻¹ := by rw [this]
  set X' : GL (Fin n) Ω := (H⁻¹ * M * H) * X * (H⁻¹ * M * H)⁻¹ with hX'
  have hX'det : (X' : Matrix (Fin n) (Fin n) Ω).det = 1 := det_conj_eq_one _ X hX
  have e2 : H * X' * H⁻¹ = M * Y * M⁻¹ := by rw [hX', hY]; group
  have e3 := htw X' hX'det
  rw [e2, hM Y hYdet, e1] at e3
  calc tauG σ X' = H⁻¹ * (M * (H * tauG σ X * H⁻¹) * M⁻¹) * H := e3.symm
    _ = (H⁻¹ * M * H) * tauG σ X * (H⁻¹ * M * H)⁻¹ := by group

theorem tauG_compat_of_phi (σ : Ω →+* Ω) (A M : GL (Fin n) Ω) (Φ : SL(n, Ω) →* SL(n, Ω))
    (hA' : ∀ X : SL(n, Ω), ((Φ X : SL(n, Ω)) : Matrix (Fin n) (Fin n) Ω) =
      (A : Matrix (Fin n) (Fin n) Ω) * (((X : Matrix (Fin n) (Fin n) Ω).map σ)⁻¹)ᵀ *
        (↑A⁻¹ : Matrix (Fin n) (Fin n) Ω))
    (hc : ∀ X : SL(n, Ω), Φ (conjSLn M X) = conjSLn M (Φ X))
    (X : GL (Fin n) Ω) (hX : (X : Matrix (Fin n) (Fin n) Ω).det = 1) :
    A * tauG σ (M * X * M⁻¹) * A⁻¹ = M * (A * tauG σ X * A⁻¹) * M⁻¹ := by
  set X' : SL(n, Ω) := ⟨(X : Matrix (Fin n) (Fin n) Ω), hX⟩ with hX'
  have hL := hA' (conjSLn M X')
  rw [coe_conjSLn] at hL
  have hR : ((conjSLn M (Φ X') : SL(n, Ω)) : Matrix (Fin n) (Fin n) Ω) =
      (M : Matrix (Fin n) (Fin n) Ω) * ((A : Matrix (Fin n) (Fin n) Ω) *
        (((X' : Matrix (Fin n) (Fin n) Ω).map σ)⁻¹)ᵀ * (↑A⁻¹ : Matrix (Fin n) (Fin n) Ω)) *
          (↑M⁻¹ : Matrix (Fin n) (Fin n) Ω) := by
    rw [coe_conjSLn, hA' X']
  have h1 := congrArg (fun Y : SL(n, Ω) => (Y : Matrix (Fin n) (Fin n) Ω)) (hc X')
  simp only [hL, hR] at h1
  refine Units.ext ?_
  simp only [Units.val_mul, coe_tauG]
  exact h1

end Compat

section PerMatrix

variable {ℓ f : ℕ} {Ω : Type} [Field Ω] [IsAlgClosed Ω] [Fact ℓ.Prime] [CharP Ω ℓ]

theorem exists_unitary_of_compat (hf : 1 ≤ f) (A H M : GL (Fin 5) Ω)
    (hdetH : (H : Matrix (Fin 5) (Fin 5) Ω).det = 1)
    (htw : ∀ X : GL (Fin 5) Ω, (X : Matrix (Fin 5) (Fin 5) Ω).det = 1 →
      H⁻¹ * (A * tauG (iterateFrobenius Ω ℓ f) (H * X * H⁻¹) * A⁻¹) * H =
        tauG (iterateFrobenius Ω ℓ f) X)
    (hM : ∀ X : GL (Fin 5) Ω, (X : Matrix (Fin 5) (Fin 5) Ω).det = 1 →
      A * tauG (iterateFrobenius Ω ℓ f) (M * X * M⁻¹) * A⁻¹ =
        M * (A * tauG (iterateFrobenius Ω ℓ f) X * A⁻¹) * M⁻¹) :
    ∃ (μ : Ω) (g : GL (Fin 5) (subfieldSq ℓ Ω f)), μ ≠ 0 ∧
      g ∈ primeFormUnitary (unitaryFieldData_subfieldSq (Ω := Ω) hf)
        (idGram (subfieldSq ℓ Ω f) 5) ∧
      ((subfieldGL (subfieldSq ℓ Ω f) 5 g : GL (Fin 5) Ω) : Matrix (Fin 5) (Fin 5) Ω) =
        μ • ((H⁻¹ * M * H : GL (Fin 5) Ω) : Matrix (Fin 5) (Fin 5) Ω) := by
  set σ : Ω →+* Ω := iterateFrobenius Ω ℓ f with hσdef
  set Mt : GL (Fin 5) Ω := H⁻¹ * M * H with hMt
  obtain ⟨c, hc0, hτ⟩ := exists_scalar_tauG σ Mt
    (fun X hX => tauG_compat_conj σ A H M hdetH htw hM X hX)
  set G : GL (Fin 5) Ω := Matrix.GeneralLinearGroup.map σ Mt with hG
  have hGmat : (G : Matrix (Fin 5) (Fin 5) Ω) = (Mt : Matrix (Fin 5) (Fin 5) Ω).map σ :=
    coe_generalLinearGroup_map σ Mt
  have h2 : (c • (Mt : Matrix (Fin 5) (Fin 5) Ω)) * ((Mt : Matrix (Fin 5) (Fin 5) Ω).map σ)ᵀ =
      1 := by
    rw [← hτ, ← hGmat]
    change (↑G⁻¹ : Matrix (Fin 5) (Fin 5) Ω)ᵀ * (G : Matrix (Fin 5) (Fin 5) Ω)ᵀ = 1
    rw [← Matrix.transpose_mul, Units.mul_inv, Matrix.transpose_one]
  have h3 : ((Mt : Matrix (Fin 5) (Fin 5) Ω).map σ)ᵀ * (c • (Mt : Matrix (Fin 5) (Fin 5) Ω)) =
      1 := mul_eq_one_comm.1 h2
  have h4 : ((Mt : Matrix (Fin 5) (Fin 5) Ω).map σ)ᵀ * (Mt : Matrix (Fin 5) (Fin 5) Ω) =
      c⁻¹ • 1 := by
    rw [Matrix.mul_smul] at h3
    calc ((Mt : Matrix (Fin 5) (Fin 5) Ω).map σ)ᵀ * (Mt : Matrix (Fin 5) (Fin 5) Ω)
        = c⁻¹ • (c • (((Mt : Matrix (Fin 5) (Fin 5) Ω).map σ)ᵀ *
            (Mt : Matrix (Fin 5) (Fin 5) Ω))) := by
          rw [smul_smul, inv_mul_cancel₀ hc0, one_smul]
      _ = c⁻¹ • 1 := by rw [h3]
  exact exists_unitary_gl hf Mt h4 (inv_ne_zero hc0)

end PerMatrix

section Helpers

variable {Ω : Type} [Field Ω]

theorem map_pow_mul_subtype (F : Subfield Ω) (g₀ g₁ : GL (Fin 5) F) (μ₀ μ₁ : Ω)
    (Mt₀ Mt₁ : GL (Fin 5) Ω)
    (h₀ : (g₀ : Matrix (Fin 5) (Fin 5) F).map F.subtype = μ₀ • (Mt₀ : Matrix (Fin 5) (Fin 5) Ω))
    (h₁ : (g₁ : Matrix (Fin 5) (Fin 5) F).map F.subtype = μ₁ • (Mt₁ : Matrix (Fin 5) (Fin 5) Ω))
    (a b : ℕ) :
    ((g₀ ^ a * g₁ ^ b : GL (Fin 5) F) : Matrix (Fin 5) (Fin 5) F).map F.subtype =
      (μ₀ ^ a * μ₁ ^ b) • ((Mt₀ ^ a * Mt₁ ^ b : GL (Fin 5) Ω) : Matrix (Fin 5) (Fin 5) Ω) := by
  have e : ∀ M : Matrix (Fin 5) (Fin 5) F, M.map F.subtype = F.subtype.mapMatrix M := fun M => rfl
  rw [Units.val_mul, Units.val_pow_eq_pow_val, Units.val_pow_eq_pow_val, e, map_mul, map_pow,
    map_pow, ← e, ← e, h₀, h₁, Units.val_mul, Units.val_pow_eq_pow_val, Units.val_pow_eq_pow_val,
    smul_pow, smul_pow, Matrix.smul_mul, Matrix.mul_smul, smul_smul]

theorem exists_scalar_of_map_scalar (F : Subfield Ω) (M : Matrix (Fin 5) (Fin 5) F) (s : Ω)
    (h : M.map F.subtype = s • 1) : ∃ c : F, M = c • 1 := by
  have hs : s ∈ F := by
    have := congrFun (congrFun h 0) 0
    simp only [Matrix.map_apply, Matrix.smul_apply, Matrix.one_apply_eq, smul_eq_mul, mul_one]
      at this
    exact this ▸ (M 0 0).2
  refine ⟨⟨s, hs⟩, ?_⟩
  have h2 : (((⟨s, hs⟩ : F) • (1 : Matrix (Fin 5) (Fin 5) F)).map F.subtype) = s • 1 := by
    ext i j
    by_cases hij : i = j <;> simp [Matrix.smul_apply, Matrix.one_apply, Matrix.map_apply, hij]
  exact Matrix.map_injective (f := (F.subtype : F → Ω)) Subtype.val_injective (h.trans h2.symm)

theorem conj_comm_smul (H M₀ M₁ : GL (Fin 5) Ω) {ζ : Ω}
    (h : (M₀ : Matrix (Fin 5) (Fin 5) Ω) * M₁ = ζ • ((M₁ : Matrix (Fin 5) (Fin 5) Ω) * M₀)) :
    ((H⁻¹ * M₀ * H : GL (Fin 5) Ω) : Matrix (Fin 5) (Fin 5) Ω) *
        ((H⁻¹ * M₁ * H : GL (Fin 5) Ω) : Matrix (Fin 5) (Fin 5) Ω) =
      ζ • (((H⁻¹ * M₁ * H : GL (Fin 5) Ω) : Matrix (Fin 5) (Fin 5) Ω) *
        ((H⁻¹ * M₀ * H : GL (Fin 5) Ω) : Matrix (Fin 5) (Fin 5) Ω)) := by
  have e : ∀ P Q : GL (Fin 5) Ω, (H⁻¹ * P * H) * (H⁻¹ * Q * H) = H⁻¹ * (P * Q) * H :=
    fun P Q => by group
  rw [← Units.val_mul, ← Units.val_mul, e, e]
  simp only [Units.val_mul]
  rw [h, Matrix.mul_smul, Matrix.smul_mul]

theorem conj_pow_five_scalar (H M : GL (Fin 5) Ω) {c : Ω}
    (h : ((M ^ 5 : GL (Fin 5) Ω) : Matrix (Fin 5) (Fin 5) Ω) = c • 1) :
    ((H⁻¹ * M * H : GL (Fin 5) Ω) : Matrix (Fin 5) (Fin 5) Ω) ^ 5 = c • 1 := by
  have e : (H⁻¹ * M * H) ^ 5 = H⁻¹ * M ^ 5 * H := by
    have := map_pow (MulAut.conj H⁻¹) M 5
    simp only [MulAut.conj_apply, inv_inv] at this
    exact this.symm
  rw [← Units.val_pow_eq_pow_val, e, Units.val_mul, Units.val_mul, h, Matrix.mul_smul,
    Matrix.mul_one, Matrix.smul_mul, ← Units.val_mul, inv_mul_cancel, Units.val_one]

end Helpers

section Bridge

theorem fixSubgroup_le_of_heis_lines
    {ℓ f : ℕ} {k Ω : Type} [Field k] [Field Ω] [Algebra k Ω] [IsAlgClosure k Ω]
    (hℓ : ℓ.Prime) (hf : 1 ≤ f) (hk : Nat.card k = ℓ ^ f) (hq5 : 5 ∣ ℓ ^ f + 1)
    (π : Equiv.Perm (Fin 5)) (Φ : SL(5, Ω) ≃* SL(5, Ω)) (b : Fin 5 → Fin 5 → Ωˣ)
    (hΦ : ∀ (i j : Fin 5) (hij : i ≠ j) (t : Ω),
      ((Φ (Matrix.SpecialLinearGroup.transvection hij t) : SL(5, Ω)) :
        Matrix (Fin 5) (Fin 5) Ω) = 1 + Matrix.single (π j) (π i) ((b i j : Ω) * t ^ ℓ ^ f))
    (M₀ M₁ : GL (Fin 5) Ω)
    (hc₀ : ∀ X : SL(5, Ω), Φ (conjSLn M₀ X) = conjSLn M₀ (Φ X))
    (hc₁ : ∀ X : SL(5, Ω), Φ (conjSLn M₁ X) = conjSLn M₁ (Φ X))
    {ζ : Ω} (hζ : IsPrimitiveRoot ζ 5)
    (hcomm : (M₀ : Matrix (Fin 5) (Fin 5) Ω) * M₁ = ζ • ((M₁ : Matrix (Fin 5) (Fin 5) Ω) * M₀))
    {c₀ c₁ : Ω} (h₀ : ((M₀ ^ 5 : GL (Fin 5) Ω) : Matrix (Fin 5) (Fin 5) Ω) = c₀ • 1)
    (h₁ : ((M₁ ^ 5 : GL (Fin 5) Ω) : Matrix (Fin 5) (Fin 5) Ω) = c₁ • 1)
    (H₀ : Subgroup SL(5, Ω))
    (hH : ∀ a b : ℕ, ¬ (5 ∣ a ∧ 5 ∣ b) → ∀ X ∈ fixSubgroup Φ,
      (X : Matrix (Fin 5) (Fin 5) Ω) *
        ((M₀ ^ a * M₁ ^ b : GL (Fin 5) Ω) : Matrix (Fin 5) (Fin 5) Ω) =
        ((M₀ ^ a * M₁ ^ b : GL (Fin 5) Ω) : Matrix (Fin 5) (Fin 5) Ω) * X → X ∈ H₀) :
    fixSubgroup Φ ≤ H₀ := by
  classical
  haveI : Fact ℓ.Prime := ⟨hℓ⟩
  haveI : Finite k := Nat.finite_of_card_ne_zero (by rw [hk]; exact (pow_pos hℓ.pos f).ne')
  haveI : Fintype k := Fintype.ofFinite k
  haveI : CharP k ℓ := charP_of_card_eq_prime_pow (by rw [← Nat.card_eq_fintype_card, hk])
  haveI : CharP Ω ℓ := charP_of_injective_algebraMap (algebraMap k Ω).injective ℓ
  haveI : IsAlgClosed Ω := IsAlgClosure.isAlgClosed k
  set σ : Ω →+* Ω := iterateFrobenius Ω ℓ f with hσdef
  have hσ' : ∀ c, σ c = c ^ ℓ ^ f := fun c => iterateFrobenius_def ℓ f c
  have hσfun : ⇑σ = fun c : Ω => c ^ ℓ ^ f := funext hσ'
  obtain ⟨A, hA⟩ := exists_conj_map_inv_transpose_of_root_permuting (by norm_num : 3 ≤ 5) σ π
    Φ.toMonoidHom b (fun i j hij t => by rw [MulEquiv.coe_toMonoidHom, hΦ, hσ'])
  obtain ⟨H, hHdet, htwist, hset⟩ :=
    matrix_graph_frobenius_unitary_descent hℓ hf hk (by norm_num : 1 ≤ 5) A
  have hA' : ∀ X : SL(5, Ω), ((Φ X : SL(5, Ω)) : Matrix (Fin 5) (Fin 5) Ω) =
      (A : Matrix (Fin 5) (Fin 5) Ω) * (((X : Matrix (Fin 5) (Fin 5) Ω).map σ)⁻¹)ᵀ *
        (↑A⁻¹ : Matrix (Fin 5) (Fin 5) Ω) := fun X => by
    have := hA X
    rwa [MulEquiv.coe_toMonoidHom, hσfun] at this
  have htw : ∀ X : GL (Fin 5) Ω, (X : Matrix (Fin 5) (Fin 5) Ω).det = 1 →
      H⁻¹ * (A * tauG σ (H * X * H⁻¹) * A⁻¹) * H = tauG σ X := by
    intro X hX
    refine Units.ext ?_
    have h1 := htwist X hX
    simp only [Units.val_mul, coe_tauG, hσfun]
    exact h1
  have hM₀ := tauG_compat_of_phi σ A M₀ Φ.toMonoidHom hA' hc₀
  have hM₁ := tauG_compat_of_phi σ A M₁ Φ.toMonoidHom hA' hc₁
  set F : Subfield Ω := subfieldSq ℓ Ω f with hFdef
  obtain ⟨μ₀, g₀, hμ₀, hg₀, hg₀m⟩ := exists_unitary_of_compat (ℓ := ℓ) hf A H M₀ hHdet htw hM₀
  obtain ⟨μ₁, g₁, hμ₁, hg₁, hg₁m⟩ := exists_unitary_of_compat (ℓ := ℓ) hf A H M₁ hHdet htw hM₁
  have hU : UnitaryFieldData ℓ f F := unitaryFieldData_subfieldSq (Ω := Ω) hf
  haveI : Finite F := finite_subfieldSq (Ω := Ω) (ℓ := ℓ) hf
  haveI : CharP F ℓ := hU.charP
  have hF : ∀ c : Ω, c ∈ F ↔ c ^ (ℓ ^ f) ^ 2 = c := fun c => mem_subfieldSq
  have hFcard : Nat.card F = (ℓ ^ f) ^ 2 := by
    rw [hFdef, card_subfieldSq hf, ← pow_mul, mul_comm]
  set Hs : SL(5, Ω) := ⟨(H : Matrix (Fin 5) (Fin 5) Ω), hHdet⟩ with hHsdef
  have hHs : Matrix.SpecialLinearGroup.toGL Hs = H := Units.ext rfl
  have hfix : ∀ X : SL(5, Ω), X ∈ fixSubgroup Φ ↔ ∃ Y ∈ unitarySet (ℓ ^ f) 5,
      Matrix.SpecialLinearGroup.toGL X =
        Matrix.SpecialLinearGroup.toGL Hs * Y * (Matrix.SpecialLinearGroup.toGL Hs)⁻¹ := by
    intro X
    have hX := Set.ext_iff.mp hset (Matrix.SpecialLinearGroup.toGL X)
    rw [mem_fixSubgroup, hHs]
    constructor
    · intro h
      obtain ⟨Y, hY, hXY⟩ := hX.mp ⟨X.2, by
        show (A : Matrix (Fin 5) (Fin 5) Ω) *
            (((X : Matrix (Fin 5) (Fin 5) Ω).map (· ^ ℓ ^ f))⁻¹)ᵀ *
              (↑A⁻¹ : Matrix (Fin 5) (Fin 5) Ω) = (X : Matrix (Fin 5) (Fin 5) Ω)
        rw [← hσfun, ← hA' X, h]⟩
      exact ⟨Y, hY, hXY.symm⟩
    · rintro ⟨Y, hY, hXY⟩
      have h := (hX.mpr ⟨Y, hY, hXY.symm⟩).2
      apply Subtype.ext
      rw [hA' X, hσfun]
      exact h
  have hSU : SUid (unitaryInvolution F ℓ f) 5 = CFSG.Open.StatedSU 5 (ℓ ^ f) F :=
    SUid_eq_statedSU hFcard 5
  let Ψ : CFSG.Open.StatedSU 5 (ℓ ^ f) F →* SL(5, Ω) := statedSUToSL F 5 (ℓ ^ f)
  let Θ : SUid (unitaryInvolution F ℓ f) 5 →* SL(5, Ω) :=
    (MulAut.conj Hs).toMonoidHom.comp (Ψ.comp (Subgroup.inclusion (le_of_eq hSU)))
  have hHsinv : ((Hs⁻¹ : SL(5, Ω)) : Matrix (Fin 5) (Fin 5) Ω) =
      (↑H⁻¹ : Matrix (Fin 5) (Fin 5) Ω) := by
    have := congrArg (fun g : GL (Fin 5) Ω => (g : Matrix (Fin 5) (Fin 5) Ω))
      (show Matrix.SpecialLinearGroup.toGL (Hs⁻¹) = H⁻¹ by rw [map_inv, hHs])
    exact this
  have hΘ : ∀ Y : SUid (unitaryInvolution F ℓ f) 5, (Θ Y : Matrix (Fin 5) (Fin 5) Ω) =
      (H : Matrix (Fin 5) (Fin 5) Ω) * ((Y : GL (Fin 5) F) : Matrix (Fin 5) (Fin 5) F).map
        F.subtype * (↑H⁻¹ : Matrix (Fin 5) (Fin 5) Ω) := by
    intro Y
    change ((Hs * Ψ (Subgroup.inclusion (le_of_eq hSU) Y) * Hs⁻¹ : SL(5, Ω)) :
      Matrix (Fin 5) (Fin 5) Ω) = _
    rw [Matrix.SpecialLinearGroup.coe_mul, Matrix.SpecialLinearGroup.coe_mul, hHsinv]
    rfl
  have hΘfix : ∀ Y, Θ Y ∈ fixSubgroup Φ := by
    intro Y
    rw [hfix]
    refine ⟨Matrix.SpecialLinearGroup.toGL (Ψ (Subgroup.inclusion (le_of_eq hSU) Y)),
      (CFSG.RankThree.Classical2.mem_range_statedSUToSL_iff hℓ F hF hFcard (by norm_num) _).mp
        ⟨_, rfl⟩, ?_⟩
    change Matrix.SpecialLinearGroup.toGL (Hs * Ψ (Subgroup.inclusion (le_of_eq hSU) Y) * Hs⁻¹) = _
    rw [map_mul, map_mul, map_inv]
  have hΘsurj : ∀ X ∈ fixSubgroup Φ, ∃ Y, Θ Y = X := by
    intro X hX
    obtain ⟨Y', hY', hXY⟩ := (hfix X).mp hX
    have hW : Matrix.SpecialLinearGroup.toGL (Hs⁻¹ * X * Hs) = Y' := by
      rw [map_mul, map_mul, map_inv, hXY]
      group
    obtain ⟨Y, hY⟩ := (CFSG.RankThree.Classical2.mem_range_statedSUToSL_iff hℓ F hF hFcard
      (by norm_num) _).mpr (hW ▸ hY')
    refine ⟨Subgroup.inclusion (le_of_eq hSU.symm) Y, ?_⟩
    change Hs * Ψ (Subgroup.inclusion (le_of_eq hSU) (Subgroup.inclusion (le_of_eq hSU.symm) Y)) *
      Hs⁻¹ = X
    have : Ψ (Subgroup.inclusion (le_of_eq hSU) (Subgroup.inclusion (le_of_eq hSU.symm) Y)) =
        Hs⁻¹ * X * Hs := by
      rw [← hY]
      rfl
    rw [this]
    group
  have hζF : ζ ∈ F := by
    rw [hF]
    have h5 : ζ ^ 5 = 1 := hζ.pow_eq_one
    have hq1 : 1 ≤ (ℓ ^ f) ^ 2 := Nat.one_le_pow _ _ (pow_pos hℓ.pos f)
    obtain ⟨m, hm⟩ : 5 ∣ (ℓ ^ f) ^ 2 - 1 := by
      have : (ℓ ^ f) ^ 2 - 1 = (ℓ ^ f + 1) * (ℓ ^ f - 1) := by
        have h1 : 1 ≤ ℓ ^ f := Nat.one_le_pow _ _ hℓ.pos
        zify [h1, hq1]
        ring
      rw [this]
      exact Dvd.dvd.mul_right hq5 _
    have : (ℓ ^ f) ^ 2 = 5 * m + 1 := by omega
    rw [this, pow_succ, pow_mul, h5, one_pow, one_mul]
  set ζF : F := ⟨ζ, hζF⟩ with hζFdef
  have hζF' : IsPrimitiveRoot ζF 5 :=
    IsPrimitiveRoot.of_map_of_injective (f := F.subtype) (by exact hζ) F.subtype.injective
  set Mt₀ : GL (Fin 5) Ω := H⁻¹ * M₀ * H with hMt₀
  set Mt₁ : GL (Fin 5) Ω := H⁻¹ * M₁ * H with hMt₁
  have hG₀ : (g₀ : Matrix (Fin 5) (Fin 5) F).map F.subtype =
      μ₀ • (Mt₀ : Matrix (Fin 5) (Fin 5) Ω) := hg₀m
  have hG₁ : (g₁ : Matrix (Fin 5) (Fin 5) F).map F.subtype =
      μ₁ • (Mt₁ : Matrix (Fin 5) (Fin 5) Ω) := hg₁m
  have hinj : Function.Injective fun M : Matrix (Fin 5) (Fin 5) F => M.map F.subtype :=
    Matrix.map_injective Subtype.val_injective
  have hNcomm := conj_comm_smul H M₀ M₁ hcomm
  have hGcomm : ((g₀ : Matrix (Fin 5) (Fin 5) F).map F.subtype) *
      ((g₁ : Matrix (Fin 5) (Fin 5) F).map F.subtype) =
      ζ • (((g₁ : Matrix (Fin 5) (Fin 5) F).map F.subtype) *
        ((g₀ : Matrix (Fin 5) (Fin 5) F).map F.subtype)) := by
    rw [hG₀, hG₁, Matrix.smul_mul, Matrix.mul_smul, Matrix.smul_mul, Matrix.mul_smul, smul_smul,
      smul_smul, hNcomm, smul_comm, smul_smul, smul_smul]
    congr 1
    ring
  have hcommF : (g₀ : Matrix (Fin 5) (Fin 5) F) * (g₁ : Matrix (Fin 5) (Fin 5) F) =
      ζF • ((g₁ : Matrix (Fin 5) (Fin 5) F) * (g₀ : Matrix (Fin 5) (Fin 5) F)) := by
    refine hinj ?_
    show ((g₀ : Matrix (Fin 5) (Fin 5) F) * g₁).map F.subtype =
      (ζF • ((g₁ : Matrix (Fin 5) (Fin 5) F) * g₀)).map F.subtype
    rw [Matrix.map_mul, Matrix.map_smul' F.subtype ζF _ (map_mul _), Matrix.map_mul]
    exact hGcomm
  have hpow5 : ∀ (g : GL (Fin 5) F) (μ : Ω) (Mt : GL (Fin 5) Ω) (c : Ω),
      (g : Matrix (Fin 5) (Fin 5) F).map F.subtype = μ • (Mt : Matrix (Fin 5) (Fin 5) Ω) →
      (Mt : Matrix (Fin 5) (Fin 5) Ω) ^ 5 = c • 1 →
      ∃ c' : F, ((g ^ 5 : GL (Fin 5) F) : Matrix (Fin 5) (Fin 5) F) = c' • 1 := by
    intro g μ Mt c hg hMt
    refine exists_scalar_of_map_scalar F _ (μ ^ 5 * c) ?_
    have e : ((g : Matrix (Fin 5) (Fin 5) F) ^ 5).map F.subtype =
        ((g : Matrix (Fin 5) (Fin 5) F).map F.subtype) ^ 5 :=
      map_pow F.subtype.mapMatrix (g : Matrix (Fin 5) (Fin 5) F) 5
    rw [Units.val_pow_eq_pow_val, e, hg, smul_pow, hMt, smul_smul]
  obtain ⟨c₀', h₀F⟩ := hpow5 g₀ μ₀ Mt₀ c₀ hG₀ (conj_pow_five_scalar H M₀ h₀)
  obtain ⟨c₁', h₁F⟩ := hpow5 g₁ μ₁ Mt₁ c₁ hG₁ (conj_pow_five_scalar H M₁ h₁)
  have hHH : (H : Matrix (Fin 5) (Fin 5) Ω) * (↑H⁻¹ : Matrix (Fin 5) (Fin 5) Ω) = 1 := H.mul_inv
  have hHH' : (↑H⁻¹ : Matrix (Fin 5) (Fin 5) Ω) * (H : Matrix (Fin 5) (Fin 5) Ω) = 1 := H.inv_mul
  have hHH2 : ∀ X : Matrix (Fin 5) (Fin 5) Ω,
      (H : Matrix (Fin 5) (Fin 5) Ω) * ((↑H⁻¹ : Matrix (Fin 5) (Fin 5) Ω) * X) = X := fun X => by
    rw [← Matrix.mul_assoc, hHH, Matrix.one_mul]
  let H_unit : Subgroup (SUid (unitaryInvolution F ℓ f) 5) := H₀.comap Θ
  have hCent : ∀ a b : ℕ, ¬ (5 ∣ a ∧ 5 ∣ b) →
      HeisTensor.Cent H_unit ((g₀ ^ a * g₁ ^ b : GL (Fin 5) F) : Matrix (Fin 5) (Fin 5) F) := by
    intro a b hab Y hYcomm
    show Θ Y ∈ H₀
    refine hH a b hab (Θ Y) (hΘfix Y) ?_
    have hmap := map_pow_mul_subtype F g₀ g₁ μ₀ μ₁ Mt₀ Mt₁ hG₀ hG₁ a b
    set Y' : Matrix (Fin 5) (Fin 5) Ω := ((Y : GL (Fin 5) F) : Matrix (Fin 5) (Fin 5) F).map
      F.subtype with hY'
    set P : Matrix (Fin 5) (Fin 5) Ω :=
      ((M₀ ^ a * M₁ ^ b : GL (Fin 5) Ω) : Matrix (Fin 5) (Fin 5) Ω) with hP
    have h1 : Y' * (((g₀ ^ a * g₁ ^ b : GL (Fin 5) F) : Matrix (Fin 5) (Fin 5) F).map F.subtype) =
        (((g₀ ^ a * g₁ ^ b : GL (Fin 5) F) : Matrix (Fin 5) (Fin 5) F).map F.subtype) * Y' := by
      rw [hY', ← Matrix.map_mul, ← Matrix.map_mul, hYcomm]
    have e : Mt₀ ^ a * Mt₁ ^ b = H⁻¹ * (M₀ ^ a * M₁ ^ b) * H := by
      have e0 : ∀ (M : GL (Fin 5) Ω) (n : ℕ), (H⁻¹ * M * H) ^ n = H⁻¹ * M ^ n * H := fun M n => by
        have := map_pow (MulAut.conj H⁻¹) M n
        simp only [MulAut.conj_apply, inv_inv] at this
        exact this.symm
      rw [hMt₀, hMt₁, e0, e0]
      group
    have hs : μ₀ ^ a * μ₁ ^ b ≠ 0 := mul_ne_zero (pow_ne_zero _ hμ₀) (pow_ne_zero _ hμ₁)
    rw [hmap, e, Units.val_mul, Units.val_mul] at h1
    have h2 : Y' * ((↑H⁻¹ : Matrix (Fin 5) (Fin 5) Ω) * P * (H : Matrix (Fin 5) (Fin 5) Ω)) =
        ((↑H⁻¹ : Matrix (Fin 5) (Fin 5) Ω) * P * (H : Matrix (Fin 5) (Fin 5) Ω)) * Y' := by
      rw [Matrix.mul_smul, Matrix.smul_mul] at h1
      exact smul_right_injective _ hs h1
    rw [hΘ Y]
    calc (H : Matrix (Fin 5) (Fin 5) Ω) * Y' * (↑H⁻¹ : Matrix (Fin 5) (Fin 5) Ω) * P
        = (H : Matrix (Fin 5) (Fin 5) Ω) * (Y' * ((↑H⁻¹ : Matrix (Fin 5) (Fin 5) Ω) * P *
            (H : Matrix (Fin 5) (Fin 5) Ω))) * (↑H⁻¹ : Matrix (Fin 5) (Fin 5) Ω) := by
          simp only [Matrix.mul_assoc, hHH, Matrix.mul_one]
      _ = (H : Matrix (Fin 5) (Fin 5) Ω) * (((↑H⁻¹ : Matrix (Fin 5) (Fin 5) Ω) * P *
            (H : Matrix (Fin 5) (Fin 5) Ω)) * Y') * (↑H⁻¹ : Matrix (Fin 5) (Fin 5) Ω) := by
          rw [h2]
      _ = P * ((H : Matrix (Fin 5) (Fin 5) Ω) * Y' * (↑H⁻¹ : Matrix (Fin 5) (Fin 5) Ω)) := by
          simp only [Matrix.mul_assoc, hHH2]
  have htop : H_unit = ⊤ :=
    eq_top_of_heis_lines hU hq5 hg₀ hg₁ hζF' hcommF h₀F h₁F hCent
  intro X hX
  obtain ⟨Y, rfl⟩ := hΘsurj X hX
  have : Y ∈ H_unit := by rw [htop]; exact Subgroup.mem_top Y
  exact this

end Bridge

end Two

end CFSG.HardMathSupport.Solomon.Coordinator.ChevQ.KSE8Five
