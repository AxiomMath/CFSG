module

public import CFSG.LocalAnalysis.ComponentInitial.UnitaryHigherSemilinearAut
public import CFSG.LocalAnalysis.ShultStronglyClosedTI.UnitaryAutomorphismHyperbolic
public import CFSG.LieType.BorelTits.UnitaryForm
public import CFSG.LieType.Universal.Unitary.Basic
public import CFSG.Open.StatedDefs
public import CFSG.CharacterTheory.Semidihedral.DihedralQuaternion
public import CFSG.LieType.BorelTits.CompleteFlag
public import CFSG.ThirdParty.QiuzhenCFSG.GorensteinWalter.Defs

public section

namespace CFSG.LocalAnalysis.RankFourTheoremC

namespace AutSU

open Matrix CFSG.ClassicalGroups.UnitaryFlag CFSG.LocalAnalysis.ComponentInitial
  CFSG.LocalAnalysis.ComponentInitial.UnitaryHigher
open CFSG.Open (StatedSU StatedProj)

variable {p f : ℕ} {K : Type} [Field K] {m ε : ℕ}

theorem map_map_bar_comm (h : UnitaryFieldData p f K) (σ : K ≃+* K) {ι κ : Type}
    (M : Matrix ι κ K) : (M.map h.bar).map σ = (M.map σ).map h.bar := by
  ext i j
  simp only [Matrix.map_apply, map_bar_comm]

theorem isHypTransport_map {h : UnitaryFieldData p f K}
    {R : Matrix (Fin (2 * m + ε)) (HypIndex m ε) K} (hR : IsHypTransport h R) (σ : K ≃+* K) :
    IsHypTransport h (R.map σ) := by
  have hR' : (R.map h.bar)ᵀ * R = hypGram m ε K := hR
  have h1 := congrArg (fun M => M.map σ) hR'
  rw [Matrix.map_mul, transpose_map, map_map_bar_comm h σ, hypGram_map_ringEquiv] at h1
  exact h1

theorem map_transportInv {h : UnitaryFieldData p f K}
    (R : Matrix (Fin (2 * m + ε)) (HypIndex m ε) K) (σ : K ≃+* K) :
    (transportInv h R).map σ = transportInv h (R.map σ) := by
  rw [transportInv, transportInv, Matrix.map_mul, hypGram_map_ringEquiv, transpose_map,
    map_map_bar_comm h σ]

theorem transportInv_mul_cancel_left {h : UnitaryFieldData p f K}
    {R : Matrix (Fin (2 * m + ε)) (HypIndex m ε) K} (hR : IsHypTransport h R) {κ : Type}
    [Fintype κ] (Y : Matrix (HypIndex m ε) κ K) : transportInv h R * (R * Y) = Y := by
  rw [← Matrix.mul_assoc, transportInv_mul hR, Matrix.one_mul]

theorem mul_transportInv_cancel_left {h : UnitaryFieldData p f K}
    {R : Matrix (Fin (2 * m + ε)) (HypIndex m ε) K} (hR : IsHypTransport h R) {κ : Type}
    [Fintype κ] (Y : Matrix (Fin (2 * m + ε)) κ K) : R * (transportInv h R * Y) = Y := by
  rw [← Matrix.mul_assoc, mul_transportInv hR, Matrix.one_mul]

theorem transportInv_isometry {h : UnitaryFieldData p f K}
    {R : Matrix (Fin (2 * m + ε)) (HypIndex m ε) K} (hR : IsHypTransport h R) :
    ((transportInv h R).map h.bar)ᵀ * hypGram m ε K * transportInv h R = 1 := by
  refine gramForm_injective h fun u v => ?_
  rw [← gramForm_mulVec, ← stdHermForm_eq_gramForm]
  exact hypForm_transportInv hR u v

@[expose] noncomputable def twistTransportGL {h : UnitaryFieldData p f K}
    {R R' : Matrix (Fin (2 * m + ε)) (HypIndex m ε) K}
    (hR : IsHypTransport h R) (hR' : IsHypTransport h R') (A : GL (HypIndex m ε) K) :
    GL (Fin (2 * m + ε)) K where
  val := R * (A : Matrix (HypIndex m ε) (HypIndex m ε) K) * transportInv h R'
  inv := R' * ((A⁻¹ : GL (HypIndex m ε) K) : Matrix (HypIndex m ε) (HypIndex m ε) K) *
    transportInv h R
  val_inv := by
    calc _ = R * ((A : Matrix (HypIndex m ε) (HypIndex m ε) K) * (transportInv h R' * R') *
          ((A⁻¹ : GL (HypIndex m ε) K) : Matrix (HypIndex m ε) (HypIndex m ε) K)) *
            transportInv h R := by simp only [Matrix.mul_assoc]
      _ = 1 := by
        rw [transportInv_mul hR', Matrix.mul_one, ← Units.val_mul, mul_inv_cancel, Units.val_one,
          Matrix.mul_one, mul_transportInv hR]
  inv_val := by
    calc _ = R' * (((A⁻¹ : GL (HypIndex m ε) K) : Matrix (HypIndex m ε) (HypIndex m ε) K) *
          (transportInv h R * R) * (A : Matrix (HypIndex m ε) (HypIndex m ε) K)) *
            transportInv h R' := by simp only [Matrix.mul_assoc]
      _ = 1 := by
        rw [transportInv_mul hR, Matrix.mul_one, ← Units.val_mul, inv_mul_cancel, Units.val_one,
          Matrix.mul_one, mul_transportInv hR']

theorem coe_twistTransportGL {h : UnitaryFieldData p f K}
    {R R' : Matrix (Fin (2 * m + ε)) (HypIndex m ε) K}
    (hR : IsHypTransport h R) (hR' : IsHypTransport h R') (A : GL (HypIndex m ε) K) :
    ((twistTransportGL hR hR' A : GL (Fin (2 * m + ε)) K) :
      Matrix (Fin (2 * m + ε)) (Fin (2 * m + ε)) K) =
        R * (A : Matrix (HypIndex m ε) (HypIndex m ε) K) * transportInv h R' :=
  rfl

theorem twistTransportGL_conj {h : UnitaryFieldData p f K}
    {R R' : Matrix (Fin (2 * m + ε)) (HypIndex m ε) K}
    (hR : IsHypTransport h R) (hR' : IsHypTransport h R') (A g : GL (HypIndex m ε) K) :
    twistTransportGL hR hR' A * transportGL hR' g * (twistTransportGL hR hR' A)⁻¹ =
      transportGL hR (A * g * A⁻¹) := by
  refine Units.ext ?_
  rw [Units.val_mul, Units.val_mul]
  change R * (A : Matrix (HypIndex m ε) (HypIndex m ε) K) * transportInv h R' *
      (R' * (g : Matrix (HypIndex m ε) (HypIndex m ε) K) * transportInv h R') *
      (R' * ((A⁻¹ : GL (HypIndex m ε) K) : Matrix (HypIndex m ε) (HypIndex m ε) K) *
        transportInv h R) =
    R * ((A * g * A⁻¹ : GL (HypIndex m ε) K) : Matrix (HypIndex m ε) (HypIndex m ε) K) *
      transportInv h R
  rw [Units.val_mul, Units.val_mul]
  simp only [Matrix.mul_assoc, transportInv_mul_cancel_left hR', transportInv_mul hR',
    Matrix.mul_one]

theorem glAut_transportGL {h : UnitaryFieldData p f K}
    {R : Matrix (Fin (2 * m + ε)) (HypIndex m ε) K} (hR : IsHypTransport h R) (σ : K ≃+* K)
    (g : GL (HypIndex m ε) K) :
    glAut σ (transportGL hR g) = transportGL (isHypTransport_map hR σ) (glAut σ g) := by
  refine Units.ext ?_
  simp only [coe_glAut, coe_transportGL, Matrix.map_mul, map_transportInv]

theorem lineNormalizer_eq_semilinearPointGroup_of_two_le (h : UnitaryFieldData p f K)
    (hm : 2 ≤ m) (hε : ε ≤ 1) : lineNormalizer h m ε = semilinearPointGroup h m ε := by
  rcases (by omega : m = 2 ∨ 3 ≤ m) with rfl | hm3
  · exact (unitary_rank_two_permutation_normalizer h hε).1
  · exact (unitary_higher_permutation_normalizer h hm3 hε).1

theorem exists_semilinear_hypPSU_of_two_le (h : UnitaryFieldData p f K) (hm : 2 ≤ m)
    (hε : ε ≤ 1) (α : MulAut (hypPSU h m ε)) :
    ∃ x : semilinearSimilitudes h m ε, ∀ g : hypSU h m ε,
      α (hypProj h m ε g) = hypProj h m ε ⟨_, conj_mem_hypSU x.2 g⟩ := by
  have hr : 1 ≤ m := by omega
  have hmem : linePerm h hr hε α ∈ semilinearPointGroup h m ε := by
    rw [← lineNormalizer_eq_semilinearPointGroup_of_two_le h hm hε, ← range_linePerm h hr hε]
    exact ⟨α, rfl⟩
  obtain ⟨x, hx⟩ := hmem
  refine ⟨x, fun g => hypProjLineAction_injective h (by omega) ?_⟩
  rw [← linePerm_conj h hr hε, ← hx, semilinearPointAction_conj]

theorem exists_isometry_hypPSU_of_two_le (h : UnitaryFieldData p f K) (hm : 2 ≤ m)
    (hε : ε ≤ 1) (α : MulAut (hypPSU h m ε)) :
    ∃ (σ : K ≃+* K) (A : GL (HypIndex m ε) K),
      ((A : Matrix (HypIndex m ε) (HypIndex m ε) K).map h.bar)ᵀ * hypGram m ε K *
          (A : Matrix (HypIndex m ε) (HypIndex m ε) K) = hypGram m ε K ∧
        ∀ g : hypSU h m ε, ∃ hg : A * glAut σ (g : GL (HypIndex m ε) K) * A⁻¹ ∈ hypSU h m ε,
          α (hypProj h m ε g) = hypProj h m ε ⟨_, hg⟩ := by
  obtain ⟨x, hx⟩ := exists_semilinear_hypPSU_of_two_le h hm hε α
  obtain ⟨μ, hμ0, hμ, hB⟩ := mem_semilinearSimilitudes.mp x.2
  obtain ⟨c, hc⟩ := h.normHom_surjective ⟨μ⁻¹, by
    rw [UnitaryFieldData.mem_fixedField, map_inv₀, hμ]⟩
  have hc' : h.norm c = μ⁻¹ := congrArg Subtype.val hc
  have hc0 : c ≠ 0 := by
    rintro rfl
    rw [UnitaryFieldData.norm, zero_mul] at hc'
    exact inv_ne_zero hμ0 hc'.symm
  refine ⟨(x : SemiGL (HypIndex m ε) K).right,
    GeneralLinearGroup.scalar _ (Units.mk0 c hc0) * (x : SemiGL (HypIndex m ε) K).left,
    CFSG.ShultStronglyClosedTI.UnitaryAutomorphism.scalar_mul_isometry h hB
      (by rw [Units.val_mk0, hc', inv_mul_cancel₀ hμ0]), fun g => ?_⟩
  rw [CFSG.ShultStronglyClosedTI.UnitaryAutomorphism.scalar_mul_conj_eq]
  exact ⟨conj_mem_hypSU x.2 g, hx g⟩

theorem exists_isometry_of_mulAut_statedProj (h : UnitaryFieldData p f K) (hm : 2 ≤ m)
    (hε : ε ≤ 1) (γ : MulAut (StatedProj (StatedSU (2 * m + ε) (p ^ f) K))) :
    ∃ (σ : K ≃+* K) (B : GL (Fin (2 * m + ε)) K),
      ((B : Matrix (Fin (2 * m + ε)) (Fin (2 * m + ε)) K).map h.bar)ᵀ *
        (B : Matrix (Fin (2 * m + ε)) (Fin (2 * m + ε)) K) = 1 ∧
      ∀ g : StatedSU (2 * m + ε) (p ^ f) K,
        ∃ hg : B * glAut σ (g : GL (Fin (2 * m + ε)) K) * B⁻¹ ∈ StatedSU (2 * m + ε) (p ^ f) K,
          γ (QuotientGroup.mk g) = QuotientGroup.mk ⟨_, hg⟩ := by
  obtain ⟨R, hR⟩ := exists_isHypTransport (r := m) (ε := ε) h
  have hn : 1 ≤ 2 * m + ε := by omega
  obtain ⟨σ, A, hA, hAg⟩ := exists_isometry_hypPSU_of_two_le h hm hε
    (((hypPSUEquivStatedProj h hR hn).trans γ).trans (hypPSUEquivStatedProj h hR hn).symm)
  have hR' := isHypTransport_map hR σ
  refine ⟨σ, twistTransportGL hR hR' A, ?_, fun g => ?_⟩
  · rw [coe_twistTransportGL]
    have hexp : ((R * (A : Matrix (HypIndex m ε) (HypIndex m ε) K) *
          transportInv h (R.map σ)).map h.bar)ᵀ *
        (R * (A : Matrix (HypIndex m ε) (HypIndex m ε) K) * transportInv h (R.map σ)) =
        ((transportInv h (R.map σ)).map h.bar)ᵀ *
          (((A : Matrix (HypIndex m ε) (HypIndex m ε) K).map h.bar)ᵀ *
            ((R.map h.bar)ᵀ * R) * (A : Matrix (HypIndex m ε) (HypIndex m ε) K)) *
          transportInv h (R.map σ) := by
      rw [Matrix.map_mul, Matrix.map_mul, transpose_mul, transpose_mul]
      simp only [Matrix.mul_assoc]
    rw [hexp, show (R.map h.bar)ᵀ * R = hypGram m ε K from hR, hA, transportInv_isometry hR']
  · obtain ⟨hgA, hα⟩ := hAg ((hypTransport h hR).symm g)
    have hgcoe : (g : GL (Fin (2 * m + ε)) K) =
        transportGL hR (((hypTransport h hR).symm g : hypSU h m ε) : GL (HypIndex m ε) K) := by
      conv_lhs => rw [← MulEquiv.apply_symm_apply (hypTransport h hR) g]
      rfl
    have key : twistTransportGL hR hR' A * glAut σ (g : GL (Fin (2 * m + ε)) K) *
        (twistTransportGL hR hR' A)⁻¹ =
        transportGL hR (A * glAut σ (((hypTransport h hR).symm g : hypSU h m ε) :
          GL (HypIndex m ε) K) * A⁻¹) := by
      rw [hgcoe, glAut_transportGL hR σ, twistTransportGL_conj]
    have hmem : twistTransportGL hR hR' A * glAut σ (g : GL (Fin (2 * m + ε)) K) *
        (twistTransportGL hR hR' A)⁻¹ ∈ StatedSU (2 * m + ε) (p ^ f) K := by
      rw [key]
      exact (hypTransport h hR ⟨_, hgA⟩).2
    refine ⟨hmem, ?_⟩
    have h1 : (QuotientGroup.mk g : StatedProj (StatedSU (2 * m + ε) (p ^ f) K)) =
        hypPSUEquivStatedProj h hR hn (hypProj h m ε ((hypTransport h hR).symm g)) := by
      rw [hypPSUEquivStatedProj_hypProj, MulEquiv.apply_symm_apply]
    rw [h1]
    have h2 := congrArg (hypPSUEquivStatedProj h hR hn) hα
    rw [MulEquiv.trans_apply, MulEquiv.trans_apply, MulEquiv.apply_symm_apply] at h2
    rw [h2, hypPSUEquivStatedProj_hypProj]
    exact congrArg _ (Subtype.ext key.symm)

@[expose] noncomputable def twistTransportGLInv {h : UnitaryFieldData p f K}
    {R R' : Matrix (Fin (2 * m + ε)) (HypIndex m ε) K}
    (hR : IsHypTransport h R) (hR' : IsHypTransport h R') (B : GL (Fin (2 * m + ε)) K) :
    GL (HypIndex m ε) K where
  val := transportInv h R * (B : Matrix (Fin (2 * m + ε)) (Fin (2 * m + ε)) K) * R'
  inv := transportInv h R' *
    ((B⁻¹ : GL (Fin (2 * m + ε)) K) : Matrix (Fin (2 * m + ε)) (Fin (2 * m + ε)) K) * R
  val_inv := by
    calc _ = transportInv h R * ((B : Matrix (Fin (2 * m + ε)) (Fin (2 * m + ε)) K) *
          (R' * transportInv h R') *
          ((B⁻¹ : GL (Fin (2 * m + ε)) K) : Matrix (Fin (2 * m + ε)) (Fin (2 * m + ε)) K)) *
            R := by simp only [Matrix.mul_assoc]
      _ = 1 := by
        rw [mul_transportInv hR', Matrix.mul_one, ← Units.val_mul, mul_inv_cancel, Units.val_one,
          Matrix.mul_one, transportInv_mul hR]
  inv_val := by
    calc _ = transportInv h R' * (((B⁻¹ : GL (Fin (2 * m + ε)) K) :
          Matrix (Fin (2 * m + ε)) (Fin (2 * m + ε)) K) * (R * transportInv h R) *
          (B : Matrix (Fin (2 * m + ε)) (Fin (2 * m + ε)) K)) * R' := by
          simp only [Matrix.mul_assoc]
      _ = 1 := by
        rw [mul_transportInv hR, Matrix.mul_one, ← Units.val_mul, inv_mul_cancel, Units.val_one,
          Matrix.mul_one, transportInv_mul hR']

theorem coe_twistTransportGLInv {h : UnitaryFieldData p f K}
    {R R' : Matrix (Fin (2 * m + ε)) (HypIndex m ε) K}
    (hR : IsHypTransport h R) (hR' : IsHypTransport h R') (B : GL (Fin (2 * m + ε)) K) :
    ((twistTransportGLInv hR hR' B : GL (HypIndex m ε) K) :
      Matrix (HypIndex m ε) (HypIndex m ε) K) =
        transportInv h R * (B : Matrix (Fin (2 * m + ε)) (Fin (2 * m + ε)) K) * R' :=
  rfl

theorem transportGL_twistTransportGLInv_conj {h : UnitaryFieldData p f K}
    {R R' : Matrix (Fin (2 * m + ε)) (HypIndex m ε) K}
    (hR : IsHypTransport h R) (hR' : IsHypTransport h R') (B : GL (Fin (2 * m + ε)) K)
    (g : GL (HypIndex m ε) K) :
    transportGL hR (twistTransportGLInv hR hR' B * g * (twistTransportGLInv hR hR' B)⁻¹) =
      B * transportGL hR' g * B⁻¹ := by
  refine Units.ext ?_
  change R * (transportInv h R * (B : Matrix (Fin (2 * m + ε)) (Fin (2 * m + ε)) K) * R' *
      (g : Matrix (HypIndex m ε) (HypIndex m ε) K) *
      (transportInv h R' * ((B⁻¹ : GL (Fin (2 * m + ε)) K) :
        Matrix (Fin (2 * m + ε)) (Fin (2 * m + ε)) K) * R)) * transportInv h R =
    (B : Matrix (Fin (2 * m + ε)) (Fin (2 * m + ε)) K) *
      (R' * (g : Matrix (HypIndex m ε) (HypIndex m ε) K) * transportInv h R') *
      ((B⁻¹ : GL (Fin (2 * m + ε)) K) : Matrix (Fin (2 * m + ε)) (Fin (2 * m + ε)) K)
  simp only [Matrix.mul_assoc, mul_transportInv_cancel_left hR, mul_transportInv hR,
    Matrix.mul_one]

theorem glAut_scalar (σ : K ≃+* K) {ι : Type} [Fintype ι] [DecidableEq ι] (c : Kˣ) :
    ∃ c' : Kˣ, glAut σ (GeneralLinearGroup.scalar ι c) = GeneralLinearGroup.scalar ι c' := by
  refine ⟨Units.map (σ : K →* K) c, Units.ext ?_⟩
  rw [coe_glAut, GeneralLinearGroup.coe_scalar, GeneralLinearGroup.coe_scalar]
  ext i j
  by_cases hij : i = j
  · subst hij
    simp [Matrix.scalar_apply]
  · simp [Matrix.scalar_apply, hij]

theorem mul_twistTransportGLInv_mul {h : UnitaryFieldData p f K}
    {R R' : Matrix (Fin (2 * m + ε)) (HypIndex m ε) K}
    (hR : IsHypTransport h R) (hR' : IsHypTransport h R') (B : GL (Fin (2 * m + ε)) K) :
    R * ((twistTransportGLInv hR hR' B : GL (HypIndex m ε) K) :
      Matrix (HypIndex m ε) (HypIndex m ε) K) * transportInv h R' =
        (B : Matrix (Fin (2 * m + ε)) (Fin (2 * m + ε)) K) := by
  rw [coe_twistTransportGLInv]
  simp only [Matrix.mul_assoc, mul_transportInv_cancel_left hR, mul_transportInv hR',
    Matrix.mul_one]

theorem exists_similitude_of_represents (h : UnitaryFieldData p f K) (hm : 2 ≤ m)
    (hε : ε ≤ 1) (hr : 1 ≤ m) (hn : 1 ≤ 2 * m + ε)
    {R : Matrix (Fin (2 * m + ε)) (HypIndex m ε) K} (hR : IsHypTransport h R) (σ : K ≃+* K)
    (B : GL (Fin (2 * m + ε)) K)
    (hB : ((B : Matrix (Fin (2 * m + ε)) (Fin (2 * m + ε)) K).map h.bar)ᵀ *
      (B : Matrix (Fin (2 * m + ε)) (Fin (2 * m + ε)) K) = 1)
    (γ : MulAut (StatedProj (StatedSU (2 * m + ε) (p ^ f) K)))
    (hrep : ∀ g : StatedSU (2 * m + ε) (p ^ f) K,
      ∃ hg : B * glAut σ (g : GL (Fin (2 * m + ε)) K) * B⁻¹ ∈ StatedSU (2 * m + ε) (p ^ f) K,
        γ (QuotientGroup.mk g) = QuotientGroup.mk ⟨_, hg⟩) :
    ∃ x : semilinearSimilitudes h m ε,
      (x : SemiGL (HypIndex m ε) K).left =
        twistTransportGLInv hR (isHypTransport_map hR σ) B ∧
      (x : SemiGL (HypIndex m ε) K).right = σ ∧
      semilinearAutHom h hr hε x =
        ((hypPSUEquivStatedProj h hR hn).trans γ).trans (hypPSUEquivStatedProj h hR hn).symm := by
  have hR' := isHypTransport_map hR σ
  have hA : (((twistTransportGLInv hR hR' B : GL (HypIndex m ε) K) :
      Matrix (HypIndex m ε) (HypIndex m ε) K).map h.bar)ᵀ * hypGram m ε K *
      ((twistTransportGLInv hR hR' B : GL (HypIndex m ε) K) :
        Matrix (HypIndex m ε) (HypIndex m ε) K) = hypGram m ε K := by
    rw [coe_twistTransportGLInv]
    have hexp : ((transportInv h R *
          (B : Matrix (Fin (2 * m + ε)) (Fin (2 * m + ε)) K) * R.map σ).map h.bar)ᵀ *
          hypGram m ε K * (transportInv h R *
            (B : Matrix (Fin (2 * m + ε)) (Fin (2 * m + ε)) K) * R.map σ) =
        ((R.map σ).map h.bar)ᵀ * (((B : Matrix (Fin (2 * m + ε)) (Fin (2 * m + ε)) K).map
          h.bar)ᵀ * (((transportInv h R).map h.bar)ᵀ * hypGram m ε K * transportInv h R) *
            (B : Matrix (Fin (2 * m + ε)) (Fin (2 * m + ε)) K)) * R.map σ := by
      rw [Matrix.map_mul, Matrix.map_mul, transpose_mul, transpose_mul]
      simp only [Matrix.mul_assoc]
    rw [hexp, transportInv_isometry hR, Matrix.mul_one, hB, Matrix.mul_one]
    exact hR'
  have hx : (⟨twistTransportGLInv hR hR' B, σ⟩ : SemiGL (HypIndex m ε) K) ∈
      semilinearSimilitudes h m ε := ⟨1, one_ne_zero, map_one _, by rw [one_smul]; exact hA⟩
  refine ⟨⟨_, hx⟩, rfl, rfl, ?_⟩
  ext y
  obtain ⟨g, rfl⟩ := hypProj_surjective h m ε y
  rw [semilinearAutHom_apply]
  apply (hypPSUEquivStatedProj h hR hn).injective
  rw [MulEquiv.trans_apply, MulEquiv.trans_apply, MulEquiv.apply_symm_apply,
    hypPSUEquivStatedProj_hypProj, hypPSUEquivStatedProj_hypProj]
  obtain ⟨hg, hmk⟩ := hrep (hypTransport h hR g)
  rw [hmk]
  refine congrArg QuotientGroup.mk (Subtype.ext ?_)
  change transportGL hR (twistTransportGLInv hR hR' B * glAut σ (g : GL (HypIndex m ε) K) *
      (twistTransportGLInv hR hR' B)⁻¹) =
    B * glAut σ (transportGL hR (g : GL (HypIndex m ε) K)) * B⁻¹
  rw [glAut_transportGL hR σ]
  exact transportGL_twistTransportGLInv_conj hR hR' B _

theorem eq_and_scalar_of_represents (h : UnitaryFieldData p f K) (hm : 2 ≤ m) (hε : ε ≤ 1)
    (γ : MulAut (StatedProj (StatedSU (2 * m + ε) (p ^ f) K)))
    (σ₁ σ₂ : K ≃+* K) (B₁ B₂ : GL (Fin (2 * m + ε)) K)
    (hB₁ : ((B₁ : Matrix (Fin (2 * m + ε)) (Fin (2 * m + ε)) K).map h.bar)ᵀ *
      (B₁ : Matrix (Fin (2 * m + ε)) (Fin (2 * m + ε)) K) = 1)
    (hB₂ : ((B₂ : Matrix (Fin (2 * m + ε)) (Fin (2 * m + ε)) K).map h.bar)ᵀ *
      (B₂ : Matrix (Fin (2 * m + ε)) (Fin (2 * m + ε)) K) = 1)
    (hrep₁ : ∀ g : StatedSU (2 * m + ε) (p ^ f) K,
      ∃ hg : B₁ * glAut σ₁ (g : GL (Fin (2 * m + ε)) K) * B₁⁻¹ ∈
          StatedSU (2 * m + ε) (p ^ f) K,
        γ (QuotientGroup.mk g) = QuotientGroup.mk ⟨_, hg⟩)
    (hrep₂ : ∀ g : StatedSU (2 * m + ε) (p ^ f) K,
      ∃ hg : B₂ * glAut σ₂ (g : GL (Fin (2 * m + ε)) K) * B₂⁻¹ ∈
          StatedSU (2 * m + ε) (p ^ f) K,
        γ (QuotientGroup.mk g) = QuotientGroup.mk ⟨_, hg⟩) :
    σ₁ = σ₂ ∧ ∃ z : Kˣ, B₁ = B₂ * GeneralLinearGroup.scalar (Fin (2 * m + ε)) z := by
  obtain ⟨R, hR⟩ := exists_isHypTransport (r := m) (ε := ε) h
  have hr : 1 ≤ m := by omega
  have hn : 1 ≤ 2 * m + ε := by omega
  obtain ⟨x₁, hx₁l, hx₁r, h1⟩ := exists_similitude_of_represents h hm hε hr hn hR σ₁ B₁ hB₁ γ hrep₁
  obtain ⟨x₂, hx₂l, hx₂r, h2⟩ := exists_similitude_of_represents h hm hε hr hn hR σ₂ B₂ hB₂ γ hrep₂
  have hker : semilinearAutHom h hr hε (x₁⁻¹ * x₂) = 1 := by
    rw [map_mul, map_inv, h1, h2, inv_mul_cancel]
  obtain ⟨hσ, c, hc⟩ := (semilinearAutHom_eq_one_iff h hr hε (by omega) (x₁⁻¹ * x₂)).mp hker
  have hσeq : σ₁ = σ₂ := by
    have hright : ((x₁⁻¹ * x₂ : semilinearSimilitudes h m ε) : SemiGL (HypIndex m ε) K).right =
        σ₁⁻¹ * σ₂ := by
      change (x₁ : SemiGL (HypIndex m ε) K).right⁻¹ * (x₂ : SemiGL (HypIndex m ε) K).right = _
      rw [hx₁r, hx₂r]
    rw [hright] at hσ
    exact inv_mul_eq_one.mp hσ
  refine ⟨hσeq, ?_⟩
  subst hσeq
  have hleft : glAut σ₁⁻¹ (((x₁ : SemiGL (HypIndex m ε) K).left)⁻¹ *
      (x₂ : SemiGL (HypIndex m ε) K).left) = GeneralLinearGroup.scalar _ c := by
    rw [map_mul]
    have : ((x₁⁻¹ * x₂ : semilinearSimilitudes h m ε) : SemiGL (HypIndex m ε) K).left =
        glAut σ₁⁻¹ ((x₁ : SemiGL (HypIndex m ε) K).left⁻¹) *
          glAut σ₁⁻¹ (x₂ : SemiGL (HypIndex m ε) K).left := by
      change glAut (x₁ : SemiGL (HypIndex m ε) K).right⁻¹ (x₁ : SemiGL (HypIndex m ε) K).left⁻¹ *
        glAut (x₁ : SemiGL (HypIndex m ε) K).right⁻¹ (x₂ : SemiGL (HypIndex m ε) K).left = _
      rw [hx₁r]
    rw [← this]
    exact hc
  obtain ⟨c', hc'⟩ := glAut_scalar (ι := HypIndex m ε) σ₁ c
  have h3 : ((x₁ : SemiGL (HypIndex m ε) K).left)⁻¹ * (x₂ : SemiGL (HypIndex m ε) K).left =
      GeneralLinearGroup.scalar _ c' := by
    rw [← hc', ← hleft, ← MulAut.mul_apply, ← map_mul, mul_inv_cancel, map_one, MulAut.one_apply]
  have h4 : (x₂ : SemiGL (HypIndex m ε) K).left =
      (x₁ : SemiGL (HypIndex m ε) K).left * GeneralLinearGroup.scalar _ c' := by
    rw [← h3, mul_inv_cancel_left]
  have h5 : (B₂ : Matrix (Fin (2 * m + ε)) (Fin (2 * m + ε)) K) =
      (B₁ : Matrix (Fin (2 * m + ε)) (Fin (2 * m + ε)) K) *
        Matrix.scalar (Fin (2 * m + ε)) (c' : K) := by
    have e2 := mul_twistTransportGLInv_mul hR (isHypTransport_map hR σ₁) B₂
    have e1 := mul_twistTransportGLInv_mul hR (isHypTransport_map hR σ₁) B₁
    rw [← hx₂l, h4, Units.val_mul, GeneralLinearGroup.coe_scalar] at e2
    rw [← hx₁l] at e1
    rw [← e2, ← e1, ← transport_scalar (isHypTransport_map hR σ₁) (c' : K)]
    simp only [Matrix.mul_assoc, transportInv_mul_cancel_left (isHypTransport_map hR σ₁)]
  refine ⟨c'⁻¹, ?_⟩
  have h6 : B₂ = B₁ * GeneralLinearGroup.scalar (Fin (2 * m + ε)) c' :=
    Units.ext (by rw [h5, Units.val_mul, GeneralLinearGroup.coe_scalar])
  rw [h6, mul_assoc, ← map_mul, mul_inv_cancel, map_one, mul_one]

theorem semilinearAutHom_surjective_of_two_le (h : UnitaryFieldData p f K) (hm : 2 ≤ m)
    (hr : 1 ≤ m) (hε : ε ≤ 1) : Function.Surjective (semilinearAutHom h hr hε) := by
  intro α
  obtain ⟨x, hx⟩ := exists_semilinear_hypPSU_of_two_le h hm hε α
  refine ⟨x, ?_⟩
  ext y
  obtain ⟨g, rfl⟩ := hypProj_surjective h m ε y
  rw [semilinearAutHom_apply, hx]

@[expose] noncomputable def sigmaHom (h : UnitaryFieldData p f K) (hm : 2 ≤ m) (hr : 1 ≤ m)
    (hε : ε ≤ 1) : MulAut (hypPSU h m ε) →* (K ≃+* K) :=
  (semilinearAutHom h hr hε).liftOfSurjective (semilinearAutHom_surjective_of_two_le h hm hr hε)
    ⟨SemidirectProduct.rightHom.comp (semilinearSimilitudes h m ε).subtype, fun x hx =>
      MonoidHom.mem_ker.mpr
        ((semilinearAutHom_eq_one_iff h hr hε (by omega) x).mp (MonoidHom.mem_ker.mp hx)).1⟩

theorem sigmaHom_semilinearAutHom (h : UnitaryFieldData p f K) (hm : 2 ≤ m) (hr : 1 ≤ m)
    (hε : ε ≤ 1) (x : semilinearSimilitudes h m ε) :
    sigmaHom h hm hr hε (semilinearAutHom h hr hε x) = (x : SemiGL (HypIndex m ε) K).right :=
  MonoidHom.liftOfRightInverse_comp_apply _ _ _ _ x

theorem exists_sigmaHom (h : UnitaryFieldData p f K) (hm : 2 ≤ m) (hε : ε ≤ 1) :
    ∃ φ : MulAut (StatedProj (StatedSU (2 * m + ε) (p ^ f) K)) →* (K ≃+* K),
      ∀ (γ : MulAut (StatedProj (StatedSU (2 * m + ε) (p ^ f) K))) (σ : K ≃+* K)
        (B : GL (Fin (2 * m + ε)) K),
        ((B : Matrix (Fin (2 * m + ε)) (Fin (2 * m + ε)) K).map h.bar)ᵀ *
          (B : Matrix (Fin (2 * m + ε)) (Fin (2 * m + ε)) K) = 1 →
        (∀ g : StatedSU (2 * m + ε) (p ^ f) K,
          ∃ hg : B * glAut σ (g : GL (Fin (2 * m + ε)) K) * B⁻¹ ∈
              StatedSU (2 * m + ε) (p ^ f) K,
            γ (QuotientGroup.mk g) = QuotientGroup.mk ⟨_, hg⟩) → σ = φ γ := by
  obtain ⟨R, hR⟩ := exists_isHypTransport (r := m) (ε := ε) h
  have hr : 1 ≤ m := by omega
  have hn : 1 ≤ 2 * m + ε := by omega
  refine ⟨(sigmaHom h hm hr hε).comp
    (MulAut.congr (hypPSUEquivStatedProj h hR hn).symm).toMonoidHom, fun γ σ B hB hrep => ?_⟩
  obtain ⟨x, -, hxr, hΦ⟩ := exists_similitude_of_represents h hm hε hr hn hR σ B hB γ hrep
  rw [MonoidHom.comp_apply]
  change σ = sigmaHom h hm hr hε
    (((hypPSUEquivStatedProj h hR hn).trans γ).trans (hypPSUEquivStatedProj h hR hn).symm)
  rw [← hΦ, sigmaHom_semilinearAutHom, hxr]

theorem eq_refl_and_scalar_of_conj_trivial (h : UnitaryFieldData p f K) (hm : 2 ≤ m)
    (hε : ε ≤ 1) (σ : K ≃+* K) (B : GL (Fin (2 * m + ε)) K)
    (hB : ((B : Matrix (Fin (2 * m + ε)) (Fin (2 * m + ε)) K).map h.bar)ᵀ *
      (B : Matrix (Fin (2 * m + ε)) (Fin (2 * m + ε)) K) = 1)
    (hconj : ∀ g : StatedSU (2 * m + ε) (p ^ f) K,
      ∃ hg : B * glAut σ (g : GL (Fin (2 * m + ε)) K) * B⁻¹ ∈ StatedSU (2 * m + ε) (p ^ f) K,
        (QuotientGroup.mk ⟨_, hg⟩ : StatedProj (StatedSU (2 * m + ε) (p ^ f) K)) =
          QuotientGroup.mk g) :
    σ = RingEquiv.refl K ∧ ∃ z : Kˣ, B = GeneralLinearGroup.scalar (Fin (2 * m + ε)) z := by
  have hid : ∀ g : GL (Fin (2 * m + ε)) K,
      (1 : GL (Fin (2 * m + ε)) K) * glAut (1 : K ≃+* K) g * (1 : GL (Fin (2 * m + ε)) K)⁻¹ =
        g := fun g => by simp
  obtain ⟨hσ, z, hz⟩ := eq_and_scalar_of_represents h hm hε 1 σ 1 B 1 hB (by simp)
    (fun g => by
      obtain ⟨hg, hmk⟩ := hconj g
      exact ⟨hg, hmk.symm⟩)
    (fun g => ⟨by rw [hid]; exact g.2, congrArg QuotientGroup.mk (Subtype.ext (hid g).symm)⟩)
  exact ⟨hσ, z, by rw [hz, one_mul]⟩

theorem scalar_of_unitary_conj_trivial (h : UnitaryFieldData p f K) (hm : 2 ≤ m) (hε : ε ≤ 1)
    (B : GL (Fin (2 * m + ε)) K)
    (hB : ((B : Matrix (Fin (2 * m + ε)) (Fin (2 * m + ε)) K).map h.bar)ᵀ *
      (B : Matrix (Fin (2 * m + ε)) (Fin (2 * m + ε)) K) = 1)
    (hconj : ∀ g : StatedSU (2 * m + ε) (p ^ f) K,
      ∃ hg : B * (g : GL (Fin (2 * m + ε)) K) * B⁻¹ ∈ StatedSU (2 * m + ε) (p ^ f) K,
        (QuotientGroup.mk ⟨_, hg⟩ : StatedProj (StatedSU (2 * m + ε) (p ^ f) K)) =
          QuotientGroup.mk g) :
    ∃ z : Kˣ, B = GeneralLinearGroup.scalar (Fin (2 * m + ε)) z :=
  (eq_refl_and_scalar_of_conj_trivial h hm hε (RingEquiv.refl K) B hB hconj).2

section Involution

variable {r f : ℕ} [Fact r.Prime] {K : Type} [Field K] [Finite K] [CharP K r]

theorem unitaryFieldData_of_card (hK : Nat.card K = (r ^ f) ^ 2) : UnitaryFieldData r f K := by
  refine ⟨Fact.out, ?_, by rw [hK, ← pow_mul, mul_comm]⟩
  rcases Nat.eq_zero_or_pos f with h0 | h0
  · have h1 : 1 < Nat.card K := Finite.one_lt_card
    rw [hK, h0] at h1
    norm_num at h1
  · exact h0

theorem conjTr_unitaryInvolution (hU : UnitaryFieldData r f K) {n : ℕ}
    (B : Matrix (Fin n) (Fin n) K) :
    CFSG.LieType.Universal.Unitary.conjTr (CFSG.LieType.BorelTits.unitaryInvolution K r f) B =
      (B.map hU.bar)ᵀ := by
  have hσ : (⇑(CFSG.LieType.BorelTits.unitaryInvolution K r f) : K → K) = ⇑hU.bar :=
    funext fun c => by rw [CFSG.LieType.BorelTits.unitaryInvolution_apply, hU.bar_apply]
  simp only [CFSG.LieType.Universal.Unitary.conjTr, hσ]

end Involution

end AutSU

open CFSG.LocalAnalysis.ComponentInitial.UnitaryHigher (glAut)
open CFSG.LieType.BorelTits (unitaryInvolution)
open CFSG.LieType.Universal.Unitary (conjTr)

theorem l212in_aut_su {n r f : ℕ} [Fact r.Prime] (hn : 5 ≤ n) {K : Type} [Field K] [Finite K]
    [CharP K r] (hK : Nat.card K = (r ^ f) ^ 2)
    (γ : MulAut (CFSG.Open.StatedProj (CFSG.Open.StatedSU n (r ^ f) K))) :
    ∃ (σ : K ≃+* K) (B : GL (Fin n) K),
      conjTr (unitaryInvolution K r f) (B : Matrix (Fin n) (Fin n) K) *
          (B : Matrix (Fin n) (Fin n) K) = 1 ∧
      ∀ g : CFSG.Open.StatedSU n (r ^ f) K,
        ∃ hg : B * (glAut σ) (g : GL (Fin n) K) * B⁻¹ ∈ CFSG.Open.StatedSU n (r ^ f) K,
          γ (QuotientGroup.mk g) = QuotientGroup.mk ⟨_, hg⟩ := by
  have hU := AutSU.unitaryFieldData_of_card hK
  obtain ⟨m, ε, hε, rfl⟩ : ∃ m ε, ε ≤ 1 ∧ n = 2 * m + ε := ⟨n / 2, n % 2, by omega, by omega⟩
  obtain ⟨σ, B, hB, hγ⟩ := AutSU.exists_isometry_of_mulAut_statedProj hU (by omega) hε γ
  exact ⟨σ, B, by rw [AutSU.conjTr_unitaryInvolution hU]; exact hB, hγ⟩

theorem l212in_conj_scalar_su {n r f : ℕ} [Fact r.Prime] (hn : 5 ≤ n) {K : Type} [Field K]
    [Finite K] [CharP K r] (hK : Nat.card K = (r ^ f) ^ 2) (B : GL (Fin n) K)
    (hB : conjTr (unitaryInvolution K r f) (B : Matrix (Fin n) (Fin n) K) *
      (B : Matrix (Fin n) (Fin n) K) = 1)
    (h : ∀ g : CFSG.Open.StatedSU n (r ^ f) K,
      ∃ hg : B * (g : GL (Fin n) K) * B⁻¹ ∈ CFSG.Open.StatedSU n (r ^ f) K,
        (QuotientGroup.mk ⟨_, hg⟩ : CFSG.Open.StatedProj (CFSG.Open.StatedSU n (r ^ f) K)) =
          QuotientGroup.mk g) :
    ∃ z : Kˣ, B = Matrix.GeneralLinearGroup.scalar (Fin n) z := by
  have hU := AutSU.unitaryFieldData_of_card hK
  obtain ⟨m, ε, hε, rfl⟩ : ∃ m ε, ε ≤ 1 ∧ n = 2 * m + ε := ⟨n / 2, n % 2, by omega, by omega⟩
  rw [AutSU.conjTr_unitaryInvolution hU] at hB
  exact AutSU.scalar_of_unitary_conj_trivial hU (by omega) hε B hB h

theorem l212in_conj_trivial_su {n r f : ℕ} [Fact r.Prime] (hn : 5 ≤ n) {K : Type} [Field K]
    [Finite K] [CharP K r] (hK : Nat.card K = (r ^ f) ^ 2) (σ : K ≃+* K) (B : GL (Fin n) K)
    (hB : conjTr (unitaryInvolution K r f) (B : Matrix (Fin n) (Fin n) K) *
      (B : Matrix (Fin n) (Fin n) K) = 1)
    (h : ∀ g : CFSG.Open.StatedSU n (r ^ f) K,
      ∃ hg : B * (glAut σ) (g : GL (Fin n) K) * B⁻¹ ∈ CFSG.Open.StatedSU n (r ^ f) K,
        (QuotientGroup.mk ⟨_, hg⟩ : CFSG.Open.StatedProj (CFSG.Open.StatedSU n (r ^ f) K)) =
          QuotientGroup.mk g) :
    σ = RingEquiv.refl K ∧ ∃ z : Kˣ, B = Matrix.GeneralLinearGroup.scalar (Fin n) z := by
  have hU := AutSU.unitaryFieldData_of_card hK
  obtain ⟨m, ε, hε, rfl⟩ : ∃ m ε, ε ≤ 1 ∧ n = 2 * m + ε := ⟨n / 2, n % 2, by omega, by omega⟩
  rw [AutSU.conjTr_unitaryInvolution hU] at hB
  exact AutSU.eq_refl_and_scalar_of_conj_trivial hU (by omega) hε σ B hB h

theorem l212in_aut_su_unique {n r f : ℕ} [Fact r.Prime] (hn : 5 ≤ n) {K : Type} [Field K]
    [Finite K] [CharP K r] (hK : Nat.card K = (r ^ f) ^ 2)
    (γ : MulAut (CFSG.Open.StatedProj (CFSG.Open.StatedSU n (r ^ f) K)))
    (σ₁ σ₂ : K ≃+* K) (B₁ B₂ : GL (Fin n) K)
    (hB₁ : conjTr (unitaryInvolution K r f) (B₁ : Matrix (Fin n) (Fin n) K) *
      (B₁ : Matrix (Fin n) (Fin n) K) = 1)
    (hB₂ : conjTr (unitaryInvolution K r f) (B₂ : Matrix (Fin n) (Fin n) K) *
      (B₂ : Matrix (Fin n) (Fin n) K) = 1)
    (h₁ : ∀ g : CFSG.Open.StatedSU n (r ^ f) K,
      ∃ hg : B₁ * (glAut σ₁) (g : GL (Fin n) K) * B₁⁻¹ ∈ CFSG.Open.StatedSU n (r ^ f) K,
        γ (QuotientGroup.mk g) = QuotientGroup.mk ⟨_, hg⟩)
    (h₂ : ∀ g : CFSG.Open.StatedSU n (r ^ f) K,
      ∃ hg : B₂ * (glAut σ₂) (g : GL (Fin n) K) * B₂⁻¹ ∈ CFSG.Open.StatedSU n (r ^ f) K,
        γ (QuotientGroup.mk g) = QuotientGroup.mk ⟨_, hg⟩) :
    σ₁ = σ₂ ∧ ∃ z : Kˣ, B₁ = B₂ * Matrix.GeneralLinearGroup.scalar (Fin n) z := by
  have hU := AutSU.unitaryFieldData_of_card hK
  obtain ⟨m, ε, hε, rfl⟩ : ∃ m ε, ε ≤ 1 ∧ n = 2 * m + ε := ⟨n / 2, n % 2, by omega, by omega⟩
  rw [AutSU.conjTr_unitaryInvolution hU] at hB₁ hB₂
  exact AutSU.eq_and_scalar_of_represents hU (by omega) hε γ σ₁ σ₂ B₁ B₂ hB₁ hB₂ h₁ h₂

theorem l212in_aut_su_hom {n r f : ℕ} [Fact r.Prime] (hn : 5 ≤ n) {K : Type} [Field K] [Finite K]
    [CharP K r] (hK : Nat.card K = (r ^ f) ^ 2) :
    ∃ φ : MulAut (CFSG.Open.StatedProj (CFSG.Open.StatedSU n (r ^ f) K)) →* (K ≃+* K),
      ∀ γ : MulAut (CFSG.Open.StatedProj (CFSG.Open.StatedSU n (r ^ f) K)),
        (∃ B : GL (Fin n) K,
          conjTr (unitaryInvolution K r f) (B : Matrix (Fin n) (Fin n) K) *
            (B : Matrix (Fin n) (Fin n) K) = 1 ∧
          ∀ g : CFSG.Open.StatedSU n (r ^ f) K,
            ∃ hg : B * (glAut (φ γ)) (g : GL (Fin n) K) * B⁻¹ ∈
                CFSG.Open.StatedSU n (r ^ f) K,
              γ (QuotientGroup.mk g) = QuotientGroup.mk ⟨_, hg⟩) ∧
        ∀ (σ : K ≃+* K) (B : GL (Fin n) K),
          conjTr (unitaryInvolution K r f) (B : Matrix (Fin n) (Fin n) K) *
            (B : Matrix (Fin n) (Fin n) K) = 1 →
          (∀ g : CFSG.Open.StatedSU n (r ^ f) K,
            ∃ hg : B * (glAut σ) (g : GL (Fin n) K) * B⁻¹ ∈ CFSG.Open.StatedSU n (r ^ f) K,
              γ (QuotientGroup.mk g) = QuotientGroup.mk ⟨_, hg⟩) → σ = φ γ := by
  have hU := AutSU.unitaryFieldData_of_card hK
  obtain ⟨m, ε, hε, rfl⟩ : ∃ m ε, ε ≤ 1 ∧ n = 2 * m + ε := ⟨n / 2, n % 2, by omega, by omega⟩
  obtain ⟨φ, hφ⟩ := AutSU.exists_sigmaHom hU (by omega : 2 ≤ m) hε
  refine ⟨φ, fun γ => ⟨?_, fun σ B hB hrep => hφ γ σ B (by
    rw [AutSU.conjTr_unitaryInvolution hU] at hB
    exact hB) hrep⟩⟩
  obtain ⟨σ, B, hB, hγ⟩ := AutSU.exists_isometry_of_mulAut_statedProj hU (by omega) hε γ
  have hσ := hφ γ σ B hB hγ
  subst hσ
  exact ⟨B, by rw [AutSU.conjTr_unitaryInvolution hU]; exact hB, hγ⟩

end CFSG.LocalAnalysis.RankFourTheoremC
