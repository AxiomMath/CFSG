module

public import CFSG.RankThree.PartTwo.Sec4.E27.D4StepALeavesAuxL1AlgU
public import CFSG.RankThree.PartOne.KE.SuzukiDescent
public import CFSG.RankThree.PartOne.KF.UnitaryDiag

public noncomputable section

namespace CFSG.HardMathSupport.Solomon.Coordinator.ChevQ.E6Three

open Matrix CFSG.ClassicalGroups.UnitaryFlag CFSG.LocalAnalysis.ComponentInitial
  CFSG.RankThree.PartOne.KFU CFSG.RankThree.PartTwo.KFacts CFSG.RankThree.PartTwo.Sec4.E27
  CFSG.RankThree.PartOne.KE
open CFSG.RankThree.Classical2 (unitarySet fixSubgroup)
open CFSG.RankThree.PartOne.KE (diagGL3 conjDiag3)
open CFSG.LocalAnalysis.ComponentInitial.UnitaryHigher (primeFormUnitary)
open CFSG.RankThree.PartOne.KCUnitaryModel (idGram)
open scoped MatrixGroups

section Unitary

variable {ℓ f : ℕ} {K : Type} [Field K] {Ω : Type} [Field Ω] [Algebra K Ω]

@[expose] def gl3Emb (K : Type) [Field K] (Ω : Type) [Field Ω] [Algebra K Ω] :
    GL (Fin 3) K →* GL (Fin 3) Ω :=
  Matrix.GeneralLinearGroup.map (algebraMap K Ω)

theorem coe_gl3Emb (B : GL (Fin 3) K) :
    ((gl3Emb K Ω B : GL (Fin 3) Ω) : Matrix (Fin 3) (Fin 3) Ω) =
      (B : Matrix (Fin 3) (Fin 3) K).map (algebraMap K Ω) :=
  rfl

theorem gl3Emb_injective : Function.Injective (gl3Emb K Ω) := by
  intro A B hAB
  have h1 := congrArg (fun X : GL (Fin 3) Ω => (X : Matrix (Fin 3) (Fin 3) Ω)) hAB
  simp only [coe_gl3Emb] at h1
  exact Units.ext (Matrix.map_injective (algebraMap K Ω).injective h1)

theorem map_pow_map (M : Matrix (Fin 3) (Fin 3) K) (n : ℕ) :
    (M.map (algebraMap K Ω)).map (· ^ n) = (M.map (· ^ n)).map (algebraMap K Ω) := by
  ext i j
  simp

theorem bar_map_eq (h : UnitaryFieldData ℓ f K) (M : Matrix (Fin 3) (Fin 3) K) :
    M.map h.bar = M.map (· ^ ℓ ^ f) := by
  have hfun : (⇑h.bar : K → K) = fun z => z ^ ℓ ^ f := funext h.bar_apply
  rw [hfun]

theorem pow_sq_eq_self (h : UnitaryFieldData ℓ f K) (c : K) : c ^ (ℓ ^ f) ^ 2 = c := by
  have := h.bar_bar c
  rw [h.bar_apply, h.bar_apply, ← pow_mul, ← sq] at this
  exact this

theorem gl3Emb_mem_unitarySet (h : UnitaryFieldData ℓ f K) {B : GL (Fin 3) K}
    (hB : B ∈ unitarySU ℓ f K 3) : gl3Emb K Ω B ∈ unitarySet (ℓ ^ f) 3 := by
  obtain ⟨hdet, horth⟩ := (mem_unitarySU_iff h).1 hB
  rw [bar_map_eq] at horth
  refine ⟨fun i j => ?_, ?_, ?_⟩
  · rw [coe_gl3Emb]
    simp only [Matrix.map_apply]
    rw [← map_pow, pow_sq_eq_self h]
  · rw [coe_gl3Emb, ← RingHom.mapMatrix_apply, ← RingHom.map_det, hdet, map_one]
  · rw [coe_gl3Emb, map_pow_map, ← Matrix.transpose_map, ← Matrix.map_mul, horth,
      Matrix.map_one _ (map_zero _) (map_one _)]

theorem exists_gl3Emb_of_mem_unitarySet (h : UnitaryFieldData ℓ f K) {Y : GL (Fin 3) Ω}
    (hY : Y ∈ unitarySet (ℓ ^ f) 3) :
    ∃ B : GL (Fin 3) K, B ∈ unitarySU ℓ f K 3 ∧ gl3Emb K Ω B = Y := by
  classical
  have hfin : Finite K := h.finite
  have hcard : Nat.card K = (ℓ ^ f) ^ 2 := by rw [h.card, ← pow_mul, mul_comm]
  obtain ⟨hent, hdet, horth⟩ := hY
  have hent' : ∀ i j, ∃ a : K, algebraMap K Ω a = (Y : Matrix (Fin 3) (Fin 3) Ω) i j :=
    fun i j => mem_range_algebraMap_of_pow_card_eq (by rw [hcard]; exact hent i j)
  choose a ha using hent'
  set M : Matrix (Fin 3) (Fin 3) K := Matrix.of a with hMdef
  have hM : M.map (algebraMap K Ω) = (Y : Matrix (Fin 3) (Fin 3) Ω) := by
    ext i j
    exact ha i j
  have hMdet : M.det = 1 := by
    apply (algebraMap K Ω).injective
    rw [RingHom.map_det, RingHom.mapMatrix_apply, hM, hdet, map_one]
  set B := Matrix.GeneralLinearGroup.mkOfDetNeZero M (by rw [hMdet]; exact one_ne_zero)
    with hBdef
  have hB : (B : Matrix (Fin 3) (Fin 3) K) = M := rfl
  refine ⟨B, (mem_unitarySU_iff h).2 ⟨by rw [hB, hMdet], ?_⟩, ?_⟩
  · rw [hB, bar_map_eq]
    refine Matrix.map_injective (algebraMap K Ω).injective ?_
    show ((M.map (· ^ ℓ ^ f))ᵀ * M).map (algebraMap K Ω) =
      (1 : Matrix (Fin 3) (Fin 3) K).map (algebraMap K Ω)
    rw [Matrix.map_mul, Matrix.transpose_map, ← map_pow_map, hM,
      Matrix.map_one _ (map_zero _) (map_one _)]
    exact horth
  · apply Units.ext
    rw [coe_gl3Emb, hB, hM]

theorem twExists_isom_of_normalizes [IsAlgClosed Ω] (h : UnitaryFieldData ℓ f K) [CharP Ω ℓ]
    (hℓ3 : ℓ ≠ 3) (hq1 : ℓ ^ f % 3 = 2) (N : GL (Fin 3) Ω)
    (hN : ∀ Y : GL (Fin 3) Ω, Y ∈ unitarySet (ℓ ^ f) 3 → N * Y * N⁻¹ ∈ unitarySet (ℓ ^ f) 3) :
    ∃ (c : Ω) (B : GL (Fin 3) K), c ≠ 0 ∧ B ∈ unitaryIsom3 h ∧
      (N : Matrix (Fin 3) (Fin 3) Ω) = c • (B : Matrix (Fin 3) (Fin 3) K).map (algebraMap K Ω) := by
  classical
  have : Fact ℓ.Prime := ⟨h.prime⟩
  have hfin : Finite K := h.finite
  have hcard : Nat.card K = (ℓ ^ f) ^ 2 := by rw [h.card, ← pow_mul, mul_comm]
  obtain ⟨c, A₁, hc0, hNA, hent, hA₁1⟩ := exists_unitary_scalar_mul hℓ3 hq1 N hN
  have hent' : ∀ i j, ∃ a : K, algebraMap K Ω a = A₁ i j :=
    fun i j => mem_range_algebraMap_of_pow_card_eq (by rw [hcard]; exact hent i j)
  choose a ha using hent'
  set Â : Matrix (Fin 3) (Fin 3) K := Matrix.of a with hÂdef
  have hÂmap : Â.map (algebraMap K Ω) = A₁ := by
    ext i j
    exact ha i j
  have hdetA₁ : A₁.det ≠ 0 := by
    intro h0
    have := congrArg Matrix.det hA₁1
    rw [Matrix.det_mul, h0, mul_zero, Matrix.det_one] at this
    exact zero_ne_one this
  have hdetÂ : Â.det ≠ 0 := by
    intro h0
    apply hdetA₁
    rw [← hÂmap, ← RingHom.mapMatrix_apply, ← RingHom.map_det, h0, map_zero]
  set B : GL (Fin 3) K := Matrix.GeneralLinearGroup.mkOfDetNeZero Â hdetÂ with hBdef
  have hBmat : (B : Matrix (Fin 3) (Fin 3) K) = Â := rfl
  refine ⟨c, B, hc0, ?_, ?_⟩
  · rw [mem_unitaryIsom3, hBmat, bar_map_eq]
    refine Matrix.map_injective (algebraMap K Ω).injective ?_
    have h2 : (A₁.map (· ^ ℓ ^ f))ᵀ * A₁ = 1 := by
      have hb : (A₁.map (· ^ ℓ ^ f))ᵀ = barM ℓ f Ω A₁ := by
        ext i j
        simp [barM_apply]
      rw [hb]
      exact hA₁1
    show ((Â.map (· ^ ℓ ^ f))ᵀ * Â).map (algebraMap K Ω) =
      (1 : Matrix (Fin 3) (Fin 3) K).map (algebraMap K Ω)
    rw [Matrix.map_mul, Matrix.transpose_map, ← map_pow_map, hÂmap,
      Matrix.map_one _ (map_zero _) (map_one _)]
    exact h2
  · rw [hNA, hBmat, hÂmap]

theorem twMem_primeFormUnitary_of_mem_unitaryIsom3 (h : UnitaryFieldData ℓ f K)
    {B : GL (Fin 3) K} (hB : B ∈ unitaryIsom3 h) :
    B ∈ primeFormUnitary h (idGram K 3) := by
  rw [UnitaryHigher.mem_primeFormUnitary]
  have hB' := mem_unitaryIsom3.1 hB
  simpa [idGram] using hB'

theorem conj_eq_gl3Emb {N : GL (Fin 3) Ω} {c : Ω} {γ : GL (Fin 3) K} (hc : c ≠ 0)
    (hN : (N : Matrix (Fin 3) (Fin 3) Ω) = c • (γ : Matrix (Fin 3) (Fin 3) K).map (algebraMap K Ω))
    (Z : GL (Fin 3) Ω) : N * Z * N⁻¹ = gl3Emb K Ω γ * Z * (gl3Emb K Ω γ)⁻¹ := by
  apply Units.ext
  rw [Units.val_mul, Units.val_mul, Units.val_mul, Units.val_mul]
  refine coe_conj_eq_of_eq_smul N _ _ c hc hN ?_ _
  rw [← map_inv]
  change ((γ : Matrix (Fin 3) (Fin 3) K).map (algebraMap K Ω)) *
    ((γ⁻¹ : GL (Fin 3) K) : Matrix (Fin 3) (Fin 3) K).map (algebraMap K Ω) = 1
  rw [← Matrix.map_mul, ← Units.val_mul, mul_inv_cancel, Units.val_one,
    Matrix.map_one _ (map_zero _) (map_one _)]

theorem commute_of_smul_eq {N N' : GL (Fin 3) Ω} {c c' : Ω} {γ γ' : GL (Fin 3) K} (hc : c ≠ 0)
    (hc' : c' ≠ 0)
    (hN : (N : Matrix (Fin 3) (Fin 3) Ω) = c • (γ : Matrix (Fin 3) (Fin 3) K).map (algebraMap K Ω))
    (hN' : (N' : Matrix (Fin 3) (Fin 3) Ω) =
      c' • (γ' : Matrix (Fin 3) (Fin 3) K).map (algebraMap K Ω))
    (hNN' : N * N' = N' * N) : γ * γ' = γ' * γ := by
  apply gl3Emb_injective (Ω := Ω)
  apply Units.ext
  have h1 := congrArg (fun X : GL (Fin 3) Ω => (X : Matrix (Fin 3) (Fin 3) Ω)) hNN'
  simp only [Units.val_mul, hN, hN', Matrix.smul_mul, Matrix.mul_smul, smul_smul] at h1
  rw [mul_comm c' c] at h1
  have h2 := smul_right_injective (Matrix (Fin 3) (Fin 3) Ω) (mul_ne_zero hc hc') h1
  rw [map_mul, map_mul, Units.val_mul, Units.val_mul]
  exact h2

@[expose] def embSL (h : UnitaryFieldData ℓ f K) (Ω : Type) [Field Ω] [Algebra K Ω] :
    unitarySU ℓ f K 3 →* SL(3, Ω) where
  toFun B := ⟨((B : GL (Fin 3) K) : Matrix (Fin 3) (Fin 3) K).map (algebraMap K Ω), by
    rw [← RingHom.mapMatrix_apply, ← RingHom.map_det, ((mem_unitarySU_iff h).1 B.2).1, map_one]⟩
  map_one' := Subtype.ext (by
    simp only [Subgroup.coe_one, Units.val_one]
    exact Matrix.map_one _ (map_zero _) (map_one _))
  map_mul' B B' := Subtype.ext (by
    simp only [Subgroup.coe_mul, Units.val_mul, Matrix.map_mul]
    rfl)

theorem toGL_embSL (h : UnitaryFieldData ℓ f K) (B : unitarySU ℓ f K 3) :
    Matrix.SpecialLinearGroup.toGL (embSL h Ω B) = gl3Emb K Ω (B : GL (Fin 3) K) :=
  Units.ext rfl

theorem embSL_injective (h : UnitaryFieldData ℓ f K) : Function.Injective (embSL h Ω) := by
  intro B B' hBB'
  have h1 := congrArg Matrix.SpecialLinearGroup.toGL hBB'
  rw [toGL_embSL, toGL_embSL] at h1
  exact Subtype.ext (gl3Emb_injective h1)

end Unitary

section Frames

variable {ℓ f : ℕ} {K : Type} [Field K] {Ω : Type} [Field Ω] [Algebra K Ω]

@[expose] def twUnitaryFrame (h : UnitaryFieldData ℓ f K) (Hc : SL(3, Ω)) :
    unitarySU ℓ f K 3 →* SL(3, Ω) :=
  (MulAut.conj Hc).toMonoidHom.comp (embSL h Ω)

theorem twUnitaryFrame_apply (h : UnitaryFieldData ℓ f K) (Hc : SL(3, Ω)) (x : unitarySU ℓ f K 3) :
    twUnitaryFrame h Hc x = Hc * embSL h Ω x * Hc⁻¹ := by
  simp [twUnitaryFrame, MulAut.conj_apply]

theorem twUnitaryFrame_injective (h : UnitaryFieldData ℓ f K) (Hc : SL(3, Ω)) :
    Function.Injective (twUnitaryFrame h Hc) :=
  (MulAut.conj Hc).injective.comp (embSL_injective h)

theorem toGL_twUnitaryFrame (h : UnitaryFieldData ℓ f K) (Hc : SL(3, Ω)) (x : unitarySU ℓ f K 3) :
    Matrix.SpecialLinearGroup.toGL (twUnitaryFrame h Hc x) =
      Matrix.SpecialLinearGroup.toGL Hc * gl3Emb K Ω (x : GL (Fin 3) K) *
        (Matrix.SpecialLinearGroup.toGL Hc)⁻¹ := by
  rw [twUnitaryFrame_apply, map_mul, map_mul, map_inv, toGL_embSL]

theorem mem_fixSubgroup_iff_exists_twUnitaryFrame (h : UnitaryFieldData ℓ f K)
    {Φ : SL(3, Ω) ≃* SL(3, Ω)} {Hc : SL(3, Ω)}
    (hfix : ∀ X : SL(3, Ω), X ∈ fixSubgroup Φ ↔ ∃ Y ∈ unitarySet (ℓ ^ f) 3,
      Matrix.SpecialLinearGroup.toGL X = Matrix.SpecialLinearGroup.toGL Hc * Y *
        (Matrix.SpecialLinearGroup.toGL Hc)⁻¹) (X : SL(3, Ω)) :
    X ∈ fixSubgroup Φ ↔ ∃ x : unitarySU ℓ f K 3, twUnitaryFrame h Hc x = X := by
  rw [hfix]
  constructor
  · rintro ⟨Y, hY, hXY⟩
    obtain ⟨B, hB, rfl⟩ := exists_gl3Emb_of_mem_unitarySet h hY
    refine ⟨⟨B, hB⟩, Matrix.SpecialLinearGroup.toGL_injective ?_⟩
    rw [toGL_twUnitaryFrame, hXY]
  · rintro ⟨x, rfl⟩
    exact ⟨gl3Emb K Ω (x : GL (Fin 3) K), gl3Emb_mem_unitarySet h x.2,
      toGL_twUnitaryFrame h Hc x⟩

@[expose] def twFrameDiag (Hc : SL(3, Ω)) (d : Fin 3 → Ωˣ) : GL (Fin 3) Ω :=
  (Matrix.SpecialLinearGroup.toGL Hc)⁻¹ * diagGL3 d * Matrix.SpecialLinearGroup.toGL Hc

theorem diagGL3_mul_comm (d d' : Fin 3 → Ωˣ) : diagGL3 d * diagGL3 d' = diagGL3 d' * diagGL3 d := by
  apply Units.ext
  simp only [Units.val_mul]
  change Matrix.diagonal (fun i => (d i : Ω)) * Matrix.diagonal (fun i => (d' i : Ω)) =
    Matrix.diagonal (fun i => (d' i : Ω)) * Matrix.diagonal (fun i => (d i : Ω))
  rw [Matrix.diagonal_mul_diagonal, Matrix.diagonal_mul_diagonal]
  congr 1
  funext i
  exact mul_comm _ _

theorem twFrameDiag_normalizes {Φ : SL(3, Ω) ≃* SL(3, Ω)} {Hc : SL(3, Ω)} {q : ℕ}
    (hfix : ∀ X : SL(3, Ω), X ∈ fixSubgroup Φ ↔ ∃ Y ∈ unitarySet q 3,
      Matrix.SpecialLinearGroup.toGL X = Matrix.SpecialLinearGroup.toGL Hc * Y *
        (Matrix.SpecialLinearGroup.toGL Hc)⁻¹) {d : Fin 3 → Ωˣ}
    (hd : ∀ X ∈ fixSubgroup Φ, conjDiag3 d X ∈ fixSubgroup Φ) {Y : GL (Fin 3) Ω}
    (hY : Y ∈ unitarySet q 3) :
    twFrameDiag Hc d * Y * (twFrameDiag Hc d)⁻¹ ∈ unitarySet q 3 := by
  set Y' : SL(3, Ω) := ⟨(Y : Matrix (Fin 3) (Fin 3) Ω), hY.2.1⟩ with hY'
  have hY'GL : Matrix.SpecialLinearGroup.toGL Y' = Y := Units.ext rfl
  have h1 : Hc * Y' * Hc⁻¹ ∈ fixSubgroup Φ :=
    (hfix _).2 ⟨Y, hY, by rw [map_mul, map_mul, map_inv, hY'GL]⟩
  obtain ⟨Y₂, hY₂, hE⟩ := (hfix _).1 (hd _ h1)
  rw [toGL_conjDiag3, map_mul, map_mul, map_inv, hY'GL] at hE
  have e : twFrameDiag Hc d * Y * (twFrameDiag Hc d)⁻¹ = Y₂ := by
    have : Y₂ = (Matrix.SpecialLinearGroup.toGL Hc)⁻¹ * (diagGL3 d *
        (Matrix.SpecialLinearGroup.toGL Hc * Y * (Matrix.SpecialLinearGroup.toGL Hc)⁻¹) *
          (diagGL3 d)⁻¹) * Matrix.SpecialLinearGroup.toGL Hc := by
      rw [hE]
      group
    rw [this, twFrameDiag]
    group
  rw [e]
  exact hY₂

@[expose] def TwDiagRealizes (Hc : SL(3, Ω)) (d : Fin 3 → Ωˣ) (B : GL (Fin 3) K) : Prop :=
  ∃ c : Ω, c ≠ 0 ∧ ((twFrameDiag Hc d : GL (Fin 3) Ω) : Matrix (Fin 3) (Fin 3) Ω) =
    c • (B : Matrix (Fin 3) (Fin 3) K).map (algebraMap K Ω)

theorem exists_twDiagRealizes [IsAlgClosed Ω] [CharP Ω ℓ] (h : UnitaryFieldData ℓ f K)
    (hℓ3 : ℓ ≠ 3) (hq1 : ℓ ^ f % 3 = 2) {Φ : SL(3, Ω) ≃* SL(3, Ω)} {Hc : SL(3, Ω)}
    (hfix : ∀ X : SL(3, Ω), X ∈ fixSubgroup Φ ↔ ∃ Y ∈ unitarySet (ℓ ^ f) 3,
      Matrix.SpecialLinearGroup.toGL X = Matrix.SpecialLinearGroup.toGL Hc * Y *
        (Matrix.SpecialLinearGroup.toGL Hc)⁻¹) {d : Fin 3 → Ωˣ}
    (hd : ∀ X ∈ fixSubgroup Φ, conjDiag3 d X ∈ fixSubgroup Φ) :
    ∃ B : GL (Fin 3) K, B ∈ unitaryIsom3 h ∧ TwDiagRealizes Hc d B := by
  obtain ⟨c, B, hc, hB, hN⟩ := twExists_isom_of_normalizes h hℓ3 hq1 (twFrameDiag Hc d)
    (fun Y hY => twFrameDiag_normalizes hfix hd hY)
  exact ⟨B, hB, c, hc, hN⟩

theorem TwDiagRealizes.commute {Hc : SL(3, Ω)} {d d' : Fin 3 → Ωˣ} {B B' : GL (Fin 3) K}
    (hB : TwDiagRealizes Hc d B) (hB' : TwDiagRealizes Hc d' B') : B * B' = B' * B := by
  obtain ⟨c, hc, hN⟩ := hB
  obtain ⟨c', hc', hN'⟩ := hB'
  refine commute_of_smul_eq hc hc' hN hN' ?_
  have e : diagGL3 d * diagGL3 d' = diagGL3 d' * diagGL3 d := diagGL3_mul_comm d d'
  calc twFrameDiag Hc d * twFrameDiag Hc d'
      = (Matrix.SpecialLinearGroup.toGL Hc)⁻¹ * (diagGL3 d * diagGL3 d') *
          Matrix.SpecialLinearGroup.toGL Hc := by
        unfold twFrameDiag
        group
    _ = (Matrix.SpecialLinearGroup.toGL Hc)⁻¹ * (diagGL3 d' * diagGL3 d) *
          Matrix.SpecialLinearGroup.toGL Hc := by rw [e]
    _ = twFrameDiag Hc d' * twFrameDiag Hc d := by
        unfold twFrameDiag
        group

theorem TwDiagRealizes.conjDiag3_twUnitaryFrame (h : UnitaryFieldData ℓ f K) {Hc : SL(3, Ω)}
    {d : Fin 3 → Ωˣ} {γ : primeFormUnitary h (idGram K 3)}
    (hγ : TwDiagRealizes Hc d (γ : GL (Fin 3) K)) (x : unitarySU ℓ f K 3) :
    conjDiag3 d (twUnitaryFrame h Hc x) = twUnitaryFrame h Hc (conjSU h γ x) := by
  obtain ⟨c, hc, hN⟩ := hγ
  apply Matrix.SpecialLinearGroup.toGL_injective
  rw [toGL_conjDiag3, toGL_twUnitaryFrame, toGL_twUnitaryFrame, coe_conjSU, map_mul, map_mul,
    map_inv]
  have h1 := conj_eq_gl3Emb hc hN (gl3Emb K Ω (x : GL (Fin 3) K))
  have e : diagGL3 d = Matrix.SpecialLinearGroup.toGL Hc * twFrameDiag Hc d *
      (Matrix.SpecialLinearGroup.toGL Hc)⁻¹ := by
    unfold twFrameDiag
    group
  calc diagGL3 d * (Matrix.SpecialLinearGroup.toGL Hc * gl3Emb K Ω (x : GL (Fin 3) K) *
        (Matrix.SpecialLinearGroup.toGL Hc)⁻¹) * (diagGL3 d)⁻¹
      = Matrix.SpecialLinearGroup.toGL Hc * (twFrameDiag Hc d * gl3Emb K Ω (x : GL (Fin 3) K) *
          (twFrameDiag Hc d)⁻¹) * (Matrix.SpecialLinearGroup.toGL Hc)⁻¹ := by
        rw [e]
        unfold twFrameDiag
        group
    _ = _ := by rw [h1]

end Frames

end CFSG.HardMathSupport.Solomon.Coordinator.ChevQ.E6Three

end
