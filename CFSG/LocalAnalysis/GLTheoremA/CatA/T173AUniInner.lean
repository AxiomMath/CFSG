module

public import CFSG.LocalAnalysis.GLTheoremA.CatA.T173AUniDefs
public import CFSG.LocalAnalysis.ComponentInitial.LinearUnitaryField

public section

namespace CFSG.LocalAnalysis.GLTheoremA.T173A

open CFSG.Open CFSG.Assembly CFSG.LocalAnalysis.GLTheoremA
open CFSG.LocalAnalysis.ComponentInitial
open Matrix
open scoped MatrixGroups

private theorem map_smul_ringHom {d : ℕ} {F : Type} [Field F] (τ : F →+* F) (c : F)
    (M : Matrix (Fin d) (Fin d) F) : (c • M).map τ = (τ c) • M.map τ := by
  ext i j
  simp only [Matrix.map_apply, Matrix.smul_apply, smul_eq_mul, map_mul]

private theorem val_scalar_gl' {d : ℕ} {F : Type} [Field F] (c : Fˣ) :
    ((Matrix.GeneralLinearGroup.scalar (Fin d) c : GL (Fin d) F) :
      Matrix (Fin d) (Fin d) F) = (c : F) • (1 : Matrix (Fin d) (Fin d) F) := by
  simp [Matrix.GeneralLinearGroup.scalar, Matrix.smul_one_eq_diagonal]

private theorem scalar_comm_gl {d : ℕ} {F : Type} [Field F] (c : Fˣ) (x : GL (Fin d) F) :
    Matrix.GeneralLinearGroup.scalar (Fin d) c * x =
      x * Matrix.GeneralLinearGroup.scalar (Fin d) c := by
  apply Units.ext
  rw [Units.val_mul, Units.val_mul, val_scalar_gl', Matrix.smul_mul, Matrix.mul_smul,
    Matrix.one_mul, Matrix.mul_one]

private def guSub (d : ℕ) (F : Type) [Field F] (τ : F →+* F)
    (hτ : ∀ x, τ (τ x) = x) : Subgroup (GL (Fin d) F) where
  carrier := {A | ((A : Matrix (Fin d) (Fin d) F).map τ)ᵀ * (A : Matrix (Fin d) (Fin d) F) = 1}
  mul_mem' := by
    intro A B hA hB
    have hmapmul : ∀ X Y : Matrix (Fin d) (Fin d) F, (X * Y).map τ = X.map τ * Y.map τ :=
      fun X Y => Matrix.map_mul (f := τ)
    show ((((A * B : GL (Fin d) F)) : Matrix (Fin d) (Fin d) F).map τ)ᵀ *
      ((A * B : GL (Fin d) F) : Matrix (Fin d) (Fin d) F) = 1
    rw [Units.val_mul, hmapmul, Matrix.transpose_mul, mul_assoc,
      ← mul_assoc (((A : Matrix (Fin d) (Fin d) F).map τ)ᵀ), hA, one_mul, hB]
  one_mem' := by
    show (((1 : GL (Fin d) F) : Matrix (Fin d) (Fin d) F).map τ)ᵀ *
      ((1 : GL (Fin d) F) : Matrix (Fin d) (Fin d) F) = 1
    rw [Units.val_one, Matrix.map_one _ (map_zero τ) (map_one τ), Matrix.transpose_one,
      Matrix.one_mul]
  inv_mem' := by
    intro A hA
    show ((((A⁻¹ : GL (Fin d) F)) : Matrix (Fin d) (Fin d) F).map τ)ᵀ *
      ((A⁻¹ : GL (Fin d) F) : Matrix (Fin d) (Fin d) F) = 1
    rw [Matrix.coe_units_inv]
    have hNinv := Matrix.inv_eq_left_inv hA
    have hNN : (A : Matrix (Fin d) (Fin d) F) * (A : Matrix (Fin d) (Fin d) F)⁻¹ = 1 := by
      rw [← Matrix.coe_units_inv]
      exact Units.mul_inv A
    have hmap : ((A : Matrix (Fin d) (Fin d) F)⁻¹).map τ =
        (A : Matrix (Fin d) (Fin d) F)ᵀ := by
      rw [hNinv, Matrix.transpose_map, Matrix.map_map]
      have hid : (⇑τ ∘ ⇑τ) = id := funext hτ
      rw [hid, Matrix.map_id]
    rw [hmap, Matrix.transpose_transpose]
    exact hNN

private theorem mem_guSub {d : ℕ} {F : Type} [Field F] {τ : F →+* F}
    {hτ : ∀ x, τ (τ x) = x} {A : GL (Fin d) F} :
    A ∈ guSub d F τ hτ ↔
      ((A : Matrix (Fin d) (Fin d) F).map τ)ᵀ * (A : Matrix (Fin d) (Fin d) F) = 1 :=
  Iff.rfl

private theorem scalar_mem_guSub {d n : ℕ} {F : Type} [Field F] (τ : F →+* F)
    (hτ : ∀ x, τ (τ x) = x) (hτq : ∀ x, τ x = x ^ 2 ^ n) {u : Fˣ}
    (hu : u ^ (2 ^ n + 1) = 1) :
    Matrix.GeneralLinearGroup.scalar (Fin d) u ∈ guSub d F τ hτ := by
  rw [mem_guSub, Matrix.GeneralLinearGroup.coe_scalar]
  have hmap : (Matrix.scalar (Fin d) (u : F)).map τ =
      Matrix.scalar (Fin d) (τ (u : F)) := by
    simp only [Matrix.scalar_apply, Matrix.diagonal_map (map_zero τ)]
  rw [hmap]
  have htrans : (Matrix.scalar (Fin d) (τ (u : F)))ᵀ =
      Matrix.scalar (Fin d) (τ (u : F)) := by
    simp only [Matrix.scalar_apply, Matrix.diagonal_transpose]
  rw [htrans, ← map_mul]
  have hval : τ (u : F) * (u : F) = 1 := by
    rw [hτq, ← pow_succ]
    have := congrArg (fun x : Fˣ => (x : F)) hu
    simpa using this
  rw [hval, map_one]

private theorem det_pow_card_mul_eq_one {d n : ℕ} {F : Type} [Field F]
    (τ : F →+* F) (hτq : ∀ x, τ x = x ^ 2 ^ n) {A : GL (Fin d) F}
    (hA : ((A : Matrix (Fin d) (Fin d) F).map τ)ᵀ * (A : Matrix (Fin d) (Fin d) F) = 1) :
    A.det ^ (2 ^ n + 1) = 1 := by
  apply Units.ext
  rw [Units.val_pow_eq_pow_val, Units.val_one,
    Matrix.GeneralLinearGroup.val_det_apply A, pow_succ]
  have h := congrArg Matrix.det hA
  rw [Matrix.det_mul, Matrix.det_transpose, Matrix.det_one] at h
  have hmap : Matrix.det ((A : Matrix (Fin d) (Fin d) F).map τ) =
      τ (A : Matrix (Fin d) (Fin d) F).det := by
    simpa [RingHom.mapMatrix_apply] using
      (RingHom.map_det τ (A : Matrix (Fin d) (Fin d) F)).symm
  rw [hmap, hτq] at h
  exact h

private theorem gu_conj_mem_SU {d n : ℕ} {F : Type} [Field F]
    (hU : UnitaryFieldData 2 n F) {B : GL (Fin d) F}
    (hB : B ∈ guSub d F hU.bar hU.bar_bar) {x : GL (Fin d) F}
    (hx : x ∈ UniSU n d F) : B * x * B⁻¹ ∈ UniSU n d F := by
  have hxgu : x ∈ guSub d F hU.bar hU.bar_bar := by
    have hSU_le : UniSU n d F ≤ guSub d F hU.bar hU.bar_bar := by
      apply (Subgroup.closure_le (guSub d F hU.bar hU.bar_bar)).mpr
      rintro A ⟨-, hrel⟩
      exact hrel
    exact hSU_le hx
  have hBxB : B * x * B⁻¹ ∈ guSub d F hU.bar hU.bar_bar :=
    mul_mem (mul_mem hB hxgu) (inv_mem hB)
  refine Subgroup.subset_closure ⟨?_, hBxB⟩
  have hunit : (B * x * B⁻¹ : GL (Fin d) F).det = 1 := by
    rw [map_mul, map_mul, map_inv]
    have hxdet' : x.det = 1 := by
      apply Units.ext
      rw [Units.val_one, Matrix.GeneralLinearGroup.val_det_apply]
      exact CFSG.Open.StatedAPI.det_of_mem_statedSU hx
    rw [hxdet', mul_one, mul_inv_cancel]
  rw [← Matrix.GeneralLinearGroup.val_det_apply]
  rw [hunit]
  rfl

private theorem graphAut_pow_gu {d n : ℕ} {F : Type} [Field F]
    (hU : UnitaryFieldData 2 n F) {R : Type} [Group R] (π : ↥(UniSU n d F) →* R)
    {B : GL (Fin d) F} (hB : B ∈ guSub d F hU.bar hU.bar_bar)
    {φ : MulAut R}
    (hφ : LargeEvenGraphAut π (fun h h' => (h' : GL (Fin d) F) = B * h * B⁻¹) φ) :
    ∀ k : ℕ, LargeEvenGraphAut π
      (fun h h' => (h' : GL (Fin d) F) = B ^ k * h * (B ^ k)⁻¹) (φ ^ k) := by
  intro k
  induction k with
  | zero =>
      intro h h' hh'
      rw [pow_zero, one_mul, inv_one, mul_one] at hh'
      rw [pow_zero, Subtype.ext hh', MulAut.one_apply]
  | succ k ih =>
      intro h h' hh'
      let h'' : ↥(UniSU n d F) :=
        ⟨B * (h : GL (Fin d) F) * B⁻¹, gu_conj_mem_SU hU hB h.2⟩
      have hstep : φ (π h) = π h'' := hφ h h'' rfl
      have hrel : (h' : GL (Fin d) F) = B ^ k * (h'' : GL (Fin d) F) * (B ^ k)⁻¹ := by
        rw [show (h'' : GL (Fin d) F) = B * (h : GL (Fin d) F) * B⁻¹ from rfl, hh',
          pow_succ, _root_.mul_inv_rev]
        group
      rw [pow_succ, MulAut.mul_apply, hstep]
      exact ih h'' h' hrel

private theorem exists_dth_root_of_gcd_dvd {F : Type} [Field F] [Finite F]
    {n d u : ℕ} (hcard : Nat.card F = (2 ^ n) ^ 2)
    (hgu : Nat.gcd d (2 ^ n + 1) ∣ u) {δ : Fˣ} (hδ : δ ^ (2 ^ n + 1) = 1) :
    ∃ ν : Fˣ, ν ^ d = (δ ^ u)⁻¹ ∧ ν ^ (2 ^ n + 1) = 1 := by
  set G : Subgroup Fˣ := (powMonoidHom (2 ^ n + 1) : Fˣ →* Fˣ).ker with hG
  haveI : IsCyclic G := isCyclic_of_injective (Subgroup.subtype G) (Subtype.coe_injective)
  have hcardG : Nat.card G = 2 ^ n + 1 := by
    rw [hG, IsCyclic.card_powMonoidHom_ker]
    rw [Nat.gcd_comm, Nat.gcd_eq_left_iff_dvd]
    rw [Nat.card_units, hcard]
    have hfac : (2 ^ n) ^ 2 - 1 = (2 ^ n + 1) * (2 ^ n - 1) := by
      have hsq := sq_tsub_sq (2 ^ n) 1
      rw [one_pow] at hsq
      exact hsq
    rw [hfac]
    exact dvd_mul_right _ _
  have hg_dvd_g : Nat.gcd d (2 ^ n + 1) ∣ 2 ^ n + 1 := Nat.gcd_dvd_right d (2 ^ n + 1)
  have hg_dvd_d : Nat.gcd d (2 ^ n + 1) ∣ d := Nat.gcd_dvd_left d (2 ^ n + 1)
  have hrange : (powMonoidHom (Nat.gcd d (2 ^ n + 1)) : G →* G).range =
      (powMonoidHom d : G →* G).range := by
    refine (Subgroup.eq_of_le_of_card_ge ?_ ?_).symm
    · rintro x ⟨y, rfl⟩
      refine ⟨y ^ (d / Nat.gcd d (2 ^ n + 1)), ?_⟩
      rw [powMonoidHom_apply, powMonoidHom_apply, ← pow_mul,
        Nat.div_mul_cancel hg_dvd_d]
    · rw [IsCyclic.card_powMonoidHom_range (G := G) (Nat.gcd d (2 ^ n + 1)),
        IsCyclic.card_powMonoidHom_range (G := G) d, hcardG]
      have hg1 : Nat.gcd (2 ^ n + 1) (Nat.gcd d (2 ^ n + 1)) =
          Nat.gcd d (2 ^ n + 1) := by
        rw [Nat.gcd_comm]
        exact Nat.gcd_eq_left_iff_dvd.mpr hg_dvd_g
      have hg2 : Nat.gcd (2 ^ n + 1) d = Nat.gcd d (2 ^ n + 1) := Nat.gcd_comm _ _
      rw [hg1, hg2]
  have hδG : δ ∈ G := by
    rw [hG, MonoidHom.mem_ker, powMonoidHom_apply]
    exact hδ
  have hmem : (⟨δ, hδG⟩ : G) ^ u ∈ (powMonoidHom d : G →* G).range := by
    have hu : (⟨δ, hδG⟩ : G) ^ u =
        ((⟨δ, hδG⟩ : G) ^ (u / Nat.gcd d (2 ^ n + 1))) ^ Nat.gcd d (2 ^ n + 1) := by
      rw [← pow_mul, Nat.div_mul_cancel hgu]
    rw [hu]
    have h1 : ((⟨δ, hδG⟩ : G) ^ (u / Nat.gcd d (2 ^ n + 1))) ^ Nat.gcd d (2 ^ n + 1) ∈
        (powMonoidHom (Nat.gcd d (2 ^ n + 1)) : G →* G).range :=
      ⟨_, by rw [powMonoidHom_apply]⟩
    rwa [hrange] at h1
  obtain ⟨νG, hνG⟩ := hmem
  refine ⟨(νG : Fˣ)⁻¹, ?_, ?_⟩
  · have hνd : (νG : Fˣ) ^ d = δ ^ u := by
      have := congrArg (fun x : G => (x : Fˣ)) hνG
      simpa [powMonoidHom_apply] using this
    rw [inv_pow, hνd]
  · have hνm : (νG : Fˣ) ^ (2 ^ n + 1) = 1 := by
      have hmem : (νG : Fˣ) ∈ (powMonoidHom (2 ^ n + 1) : Fˣ →* Fˣ).ker := by
        rw [← hG]
        exact νG.2
      rw [MonoidHom.mem_ker, powMonoidHom_apply] at hmem
      exact hmem
    rw [inv_pow, hνm, inv_one]

theorem uni_conjImage_pPower_inner {p n d : ℕ} {F : Type} [Field F] [Finite F]
    (h : UniArith p n d F) {φ : MulAut (UniPSU n d F)}
    (hφ : φ ∈ LargeEvenMatConjImage (UniMk n d F) (LargeEvenGUSet (Fin d) F (2 ^ n)))
    (hφp : φ ^ p = 1) : ∃ r : UniPSU n d F, ∀ y : UniPSU n d F, φ y = r * y * r⁻¹ := by
  obtain ⟨hp, hpm, hpd, hFcard, hn1, hd3, hd3n⟩ := h
  have hcard2 : Nat.card F = 2 ^ (2 * n) := by
    rw [hFcard, ← pow_mul, Nat.mul_comm n 2]
  have hU : UnitaryFieldData 2 n F := ⟨Nat.prime_two, hn1, hcard2⟩
  haveI : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  haveI : CharP F 2 := hU.charP
  obtain ⟨A, hA, hgraph⟩ := hφ
  obtain ⟨μ, hμ0, hμq, hAμ⟩ := hA
  have hfix : CFSG.LieType.BorelTits.unitaryInvolution F 2 n μ⁻¹ = μ⁻¹ := by
    rw [CFSG.LieType.BorelTits.unitaryInvolution_apply, inv_pow, hμq]
  obtain ⟨c, hc⟩ :=
    CFSG.ClassicalGroups.Unitary.exists_norm_eq_of_fixed (p := 2) (f := n) hFcard
      (d := μ⁻¹) hfix (inv_ne_zero hμ0)
  have hc' : c ^ (2 ^ n + 1) = μ⁻¹ := by
    rw [CFSG.LieType.BorelTits.unitaryInvolution_apply, ← pow_succ] at hc
    exact hc
  have hc0 : c ≠ 0 := by
    rintro rfl
    rw [zero_pow (by positivity : 2 ^ n + 1 ≠ 0)] at hc'
    exact (inv_ne_zero hμ0) hc'.symm
  let cunit : Fˣ := Units.mk0 c hc0
  set A' : GL (Fin d) F := Matrix.GeneralLinearGroup.scalar (Fin d) cunit * A with hA'def
  have hA'val : ((A' : GL (Fin d) F) : Matrix (Fin d) (Fin d) F) =
      c • (A : Matrix (Fin d) (Fin d) F) := by
    rw [hA'def, Units.val_mul, val_scalar_gl', Matrix.smul_mul, Matrix.one_mul]
    rfl
  have hAμ' : ((A : Matrix (Fin d) (Fin d) F).map hU.bar)ᵀ *
      (A : Matrix (Fin d) (Fin d) F) = μ • 1 := hAμ
  have hscal : hU.bar c * c * μ = 1 := by
    rw [hU.bar_apply, ← pow_succ, hc', inv_mul_cancel₀ hμ0]
  have hA'rel : (((A' : GL (Fin d) F) : Matrix (Fin d) (Fin d) F).map hU.bar)ᵀ *
      ((A' : GL (Fin d) F) : Matrix (Fin d) (Fin d) F) = 1 := by
    rw [hA'val, map_smul_ringHom, Matrix.transpose_smul, Matrix.smul_mul, Matrix.mul_smul,
      hAμ']
    simp only [smul_smul]
    rw [← mul_assoc, hscal, one_smul]
  have hA'gu : A' ∈ guSub d F hU.bar hU.bar_bar := mem_guSub.mpr hA'rel
  have hA'φ : LargeEvenGraphAut (UniMk n d F)
      (fun h h' => (h' : GL (Fin d) F) = A' * h * A'⁻¹) φ := by
    intro h h' hh'
    refine hgraph h h' ?_
    change (h' : GL (Fin d) F) = A * (h : GL (Fin d) F) * A⁻¹
    rw [hh', hA'def, _root_.mul_inv_rev,
      show (Matrix.GeneralLinearGroup.scalar (Fin d) cunit * A) * h *
          (A⁻¹ * (Matrix.GeneralLinearGroup.scalar (Fin d) cunit)⁻¹) =
        Matrix.GeneralLinearGroup.scalar (Fin d) cunit * (A * h * A⁻¹) *
          (Matrix.GeneralLinearGroup.scalar (Fin d) cunit)⁻¹ by group]
    rw [scalar_comm_gl, mul_inv_cancel_right]
  have hp_g : ¬ p ∣ Nat.gcd d (2 ^ n + 1) := by
    intro hpg
    exact hpd (hpg.trans (Nat.gcd_dvd_left d (2 ^ n + 1)))
  have hcop : Nat.Coprime (Nat.gcd d (2 ^ n + 1)) p := by
    rw [Nat.coprime_comm]
    exact hp.coprime_iff_not_dvd.mpr hp_g
  obtain ⟨u, hu0, hu1⟩ := Nat.chineseRemainder hcop 0 1
  have hgu : Nat.gcd d (2 ^ n + 1) ∣ u := Nat.modEq_zero_iff_dvd.mp hu0
  have hmod1 : u % p = 1 := by
    have := hu1
    change u % p = 1 % p at this
    rwa [Nat.mod_eq_of_lt hp.one_lt] at this
  have hu_pos : 1 ≤ u := by
    rw [Nat.one_le_iff_ne_zero]
    intro hu0'
    rw [hu0', Nat.zero_mod] at hmod1
    exact Nat.zero_ne_one hmod1
  have hu_eq : u = p * (u / p) + 1 := by
    have hdiv := Nat.div_add_mod u p
    rw [hmod1] at hdiv
    exact hdiv.symm
  have hφu : φ ^ u = φ := by
    rw [hu_eq, pow_add, pow_mul, hφp, one_pow, one_mul, pow_one]
  have hδ : (A'.det) ^ (2 ^ n + 1) = 1 := det_pow_card_mul_eq_one hU.bar hU.bar_apply hA'rel
  obtain ⟨νu, hνd, hνm⟩ := exists_dth_root_of_gcd_dvd hFcard hgu hδ
  set B : GL (Fin d) F := A' ^ u with hBdef
  set X : GL (Fin d) F := Matrix.GeneralLinearGroup.scalar (Fin d) νu * B with hXdef
  have hXdetmat : (((X : GL (Fin d) F)) : Matrix (Fin d) (Fin d) F).det = 1 := by
    rw [← Matrix.GeneralLinearGroup.val_det_apply]
    have hunit : X.det = 1 := by
      rw [hXdef, map_mul, GeneralLinearGroup.det_scalar, Fintype.card_fin, hνd, hBdef,
        map_pow, inv_mul_cancel]
    rw [hunit, Units.val_one]
  have hscalar_gu : Matrix.GeneralLinearGroup.scalar (Fin d) νu ∈
      guSub d F hU.bar hU.bar_bar := scalar_mem_guSub hU.bar hU.bar_bar hU.bar_apply hνm
  have hB_gu : B ∈ guSub d F hU.bar hU.bar_bar := by
    rw [hBdef]
    exact pow_mem hA'gu u
  have hXgu : X ∈ guSub d F hU.bar hU.bar_bar := by
    rw [hXdef]
    exact mul_mem hscalar_gu hB_gu
  have hXSU : X ∈ UniSU n d F := Subgroup.subset_closure ⟨hXdetmat, hXgu⟩
  have hpowφ : LargeEvenGraphAut (UniMk n d F)
      (fun h h' => (h' : GL (Fin d) F) = B * h * B⁻¹) (φ ^ u) :=
    graphAut_pow_gu hU (UniMk n d F) hA'gu hA'φ u
  have hφB : LargeEvenGraphAut (UniMk n d F)
      (fun h h' => (h' : GL (Fin d) F) = B * h * B⁻¹) φ := by
    rw [← hφu]
    exact hpowφ
  refine ⟨UniMk n d F ⟨X, hXSU⟩, ?_⟩
  intro y
  obtain ⟨h, rfl⟩ := QuotientGroup.mk'_surjective
    ((LargeEvenScalars (Fin d) F).subgroupOf (UniSU n d F)) y
  let h' : ↥(UniSU n d F) :=
    ⟨X * (h : GL (Fin d) F) * X⁻¹, mul_mem (mul_mem hXSU h.2) (inv_mem hXSU)⟩
  have hconj : X * (h : GL (Fin d) F) * X⁻¹ = B * (h : GL (Fin d) F) * B⁻¹ := by
    rw [hXdef, _root_.mul_inv_rev,
      show Matrix.GeneralLinearGroup.scalar (Fin d) νu * B * (h : GL (Fin d) F) *
          (B⁻¹ * (Matrix.GeneralLinearGroup.scalar (Fin d) νu)⁻¹) =
        Matrix.GeneralLinearGroup.scalar (Fin d) νu * (B * (h : GL (Fin d) F) * B⁻¹) *
          (Matrix.GeneralLinearGroup.scalar (Fin d) νu)⁻¹ by group]
    rw [scalar_comm_gl, mul_inv_cancel_right]
  have hgraphX : φ (UniMk n d F h) = UniMk n d F h' := hφB h h' hconj
  rw [hgraphX, ← map_inv, ← map_mul, ← map_mul]
  exact congrArg (UniMk n d F) (Subtype.ext rfl)

end CFSG.LocalAnalysis.GLTheoremA.T173A

end
