module

public import CFSG.GH74.KGroups.L3EpsUniAut
public import CFSG.LocalAnalysis.ComponentInitial.UnitaryHigherAntiunitaryTransport
public import CFSG.GH74.KGroups.L3EpsInvLin

public section

namespace CFSG.GH74.KGroups.L3Eps.Uni

open Matrix Subgroup CFSG CFSG.ClassicalGroups.UnitaryFlag CFSG.LocalAnalysis.ComponentInitial
  CFSG.LocalAnalysis.ComponentInitial.UnitaryHigher CFSG.RankThree.SubgroupLists
open CFSG.GH74.Generic.S45.Uni (exists_real_frame gram_transpose gram_map_bar transpose_eq_smul' isUnit_det_map_bar)
open scoped MatrixGroups commutatorElement

variable {p f : ℕ} {F : Type} [Field F]

section RealForm

theorem exists_real_form (h : UnitaryFieldData p f F) (h2 : (2 : F) ≠ 0) {A : Matrix (Fin 3) (Fin 3) F}
    (hAu : (A.map h.bar)ᵀ * A = 1) (hAA : A * A.map h.bar = 1) :
    ∃ (Pu : GL (Fin 3) F) (G : GL (Fin 3) h.fixedField),
      A * (Pu : Matrix (Fin 3) (Fin 3) F).map h.bar = (Pu : Matrix (Fin 3) (Fin 3) F) ∧
      (G : Matrix (Fin 3) (Fin 3) h.fixedField).map h.fixedField.subtype =
        ((Pu : Matrix (Fin 3) (Fin 3) F).map h.bar)ᵀ * (Pu : Matrix (Fin 3) (Fin 3) F) ∧
      (G : Matrix (Fin 3) (Fin 3) h.fixedField)ᵀ = G := by
  have hAA' : A * A.map h.bar = (1 : F) • 1 := by rw [one_smul]; exact hAA
  obtain ⟨P, hPu, hP⟩ := exists_real_frame h h2 (A := A) (ε := 1) (b := 1) hAA' (by simp) (by simp)
  rw [one_smul] at hP
  have hAt := transpose_eq_smul' h hAu hAA' (by simp)
  have hGt := gram_transpose h hAt (b := 1) (by rw [one_smul]; exact hP)
  have hGb := gram_map_bar h P
  set Gm : Matrix (Fin 3) (Fin 3) F := (P.map h.bar)ᵀ * P with hGm
  rw [one_smul] at hGt
  have hreal : ∀ i j, h.bar (Gm i j) = Gm i j := by
    intro i j
    have := congrFun (congrFun hGb i) j
    simp only [Matrix.map_apply, transpose_apply] at this
    rw [this]
    have := congrFun (congrFun hGt i) j
    simpa using this
  let G'm : Matrix (Fin 3) (Fin 3) h.fixedField :=
    Matrix.of fun i j => ⟨Gm i j, (h.mem_fixedField).2 (hreal i j)⟩
  have hG'map : G'm.map h.fixedField.subtype = Gm := by
    ext i j
    rfl
  have hdetG : IsUnit Gm.det := by
    rw [hGm, det_mul, det_transpose]
    exact (isUnit_det_map_bar h hPu).mul hPu
  have hdet' : G'm.det ≠ 0 := by
    intro h0
    have h1 : h.fixedField.subtype G'm.det = Gm.det := by
      rw [RingHom.map_det, RingHom.mapMatrix_apply, hG'map]
    rw [h0, map_zero] at h1
    exact hdetG.ne_zero h1.symm
  have hsymm : G'mᵀ = G'm := by
    ext i j
    have := congrFun (congrFun hGt i) j
    simpa [G'm] using this
  exact ⟨GeneralLinearGroup.mkOfDetNeZero P hPu.ne_zero, GeneralLinearGroup.mkOfDetNeZero G'm hdet', hP,
    hG'map, hsymm⟩

end RealForm

section Orth

open CFSG.ComponentClassification CFSG.ComponentClassification.Burgoyne.PSL
  CFSG.LocalAnalysis.ComponentInitial.LinearFlag in
theorem isQuasisimple_commutator_isometryGroup {k : Type} [Field k] [Finite k] (hk : ringChar k ≠ 2)
    (h3 : Nat.card k ≠ 3) (R : GL (Fin 3) k) (hR : (R : Matrix (Fin 3) (Fin 3) k)ᵀ = R) :
    CFSG.IsQuasisimple ↥⁅CatalogueBGraphForm.isometryGroup 3 k R,
      CatalogueBGraphForm.isometryGroup 3 k R⁆ := by
  have hodd := CatalogueBLinearHigherB.odd_card_of_ringChar_ne_two k hk
  have hQnd := CatalogueBLinearHigherB.polarBilin_matrixQuadraticForm_nondegenerate hk R hR
  have hdim : Module.finrank k (Fin 3 → k) = 3 := Module.finrank_fin_fun k
  obtain ⟨d, ψ, e, -, -, -, hq0, -⟩ := orthogonal_three_derived hodd h3
    (CatalogueBLinearHigherB.matrixQuadraticForm R) hQnd hdim
  have := isQuasisimple_trans (isoOrthGL hk R hR) hq0
  rwa [trans_commutator] at this

end Orth

section Descent

@[expose] noncomputable def inclK (h : UnitaryFieldData p f F) :
    GL (Fin 3) h.fixedField →* GL (Fin 3) F :=
  Matrix.GeneralLinearGroup.map h.fixedField.subtype

theorem coe_inclK (h : UnitaryFieldData p f F) (X : GL (Fin 3) h.fixedField) :
    ((inclK h X : GL (Fin 3) F) : Matrix (Fin 3) (Fin 3) F) =
      (X : Matrix (Fin 3) (Fin 3) h.fixedField).map h.fixedField.subtype := rfl

theorem glAut_inclK (h : UnitaryFieldData p f F) {φ : F ≃+* F} (hφ : ∀ c, φ c = h.bar c)
    (X : GL (Fin 3) h.fixedField) : glAut φ (inclK h X) = inclK h X := by
  apply Units.ext
  rw [coe_glAut, coe_inclK]
  ext i j
  simp only [Matrix.map_apply]
  rw [hφ]
  exact (h.mem_fixedField).1 (X i j).2

theorem exists_inclK_of_real (h : UnitaryFieldData p f F) {Y : GL (Fin 3) F}
    (hY : (Y : Matrix (Fin 3) (Fin 3) F).map h.bar = Y) :
    ∃ X : GL (Fin 3) h.fixedField, inclK h X = Y := by
  let Xm : Matrix (Fin 3) (Fin 3) h.fixedField :=
    Matrix.of fun i j => ⟨(Y : Matrix (Fin 3) (Fin 3) F) i j,
      (h.mem_fixedField).2 (congrFun (congrFun hY i) j)⟩
  have hXm : Xm.map h.fixedField.subtype = (Y : Matrix (Fin 3) (Fin 3) F) := by
    ext i j
    rfl
  have hdet : Xm.det ≠ 0 := by
    intro h0
    have h1 : h.fixedField.subtype Xm.det = (Y : Matrix (Fin 3) (Fin 3) F).det := by
      rw [RingHom.map_det, RingHom.mapMatrix_apply, hXm]
    rw [h0, map_zero] at h1
    exact ((Matrix.isUnit_iff_isUnit_det _).1 (Units.isUnit Y)).ne_zero h1.symm
  exact ⟨GeneralLinearGroup.mkOfDetNeZero Xm hdet, Units.ext hXm⟩

structure RealData (h : UnitaryFieldData p f F) (A : GL (Fin 3) F) where
  Pu : GL (Fin 3) F
  G : GL (Fin 3) h.fixedField
  hP : (A : Matrix (Fin 3) (Fin 3) F) * (Pu : Matrix (Fin 3) (Fin 3) F).map h.bar =
    (Pu : Matrix (Fin 3) (Fin 3) F)
  hG : (G : Matrix (Fin 3) (Fin 3) h.fixedField).map h.fixedField.subtype =
    ((Pu : Matrix (Fin 3) (Fin 3) F).map h.bar)ᵀ * (Pu : Matrix (Fin 3) (Fin 3) F)
  hGs : (G : Matrix (Fin 3) (Fin 3) h.fixedField)ᵀ = G

theorem exists_realData (h : UnitaryFieldData p f F) (h2 : (2 : F) ≠ 0) {A : GL (Fin 3) F}
    (hAu : ((A : Matrix (Fin 3) (Fin 3) F).map h.bar)ᵀ * (A : Matrix (Fin 3) (Fin 3) F) = 1)
    (hAA : (A : Matrix (Fin 3) (Fin 3) F) * (A : Matrix (Fin 3) (Fin 3) F).map h.bar = 1) :
    Nonempty (RealData h A) := by
  obtain ⟨Pu, G, hP, hG, hGs⟩ := exists_real_form h h2 hAu hAA
  exact ⟨⟨Pu, G, hP, hG, hGs⟩⟩

namespace RealData

variable {h : UnitaryFieldData p f F} {A : GL (Fin 3) F} (D : RealData h A)

@[expose] noncomputable def Iso : Subgroup (GL (Fin 3) h.fixedField) :=
  CFSG.ComponentClassification.CatalogueBGraphForm.isometryGroup 3 h.fixedField D.G

@[expose] noncomputable def Iso1 : Subgroup (GL (Fin 3) h.fixedField) :=
  D.Iso ⊓ (Matrix.GeneralLinearGroup.det : GL (Fin 3) h.fixedField →* h.fixedFieldˣ).ker

theorem hH : ((D.Pu : Matrix (Fin 3) (Fin 3) F).map h.bar)ᵀ * (1 : Matrix (Fin 3) (Fin 3) F) * D.Pu =
    (D.G : Matrix (Fin 3) (Fin 3) h.fixedField).map h.fixedField.subtype := by
  rw [Matrix.mul_one]
  exact D.hG.symm

theorem map_bar_inclK (X : GL (Fin 3) h.fixedField) :
    ((inclK h X : GL (Fin 3) F) : Matrix (Fin 3) (Fin 3) F).map h.bar = (inclK h X : GL (Fin 3) F) := by
  rw [coe_inclK]
  ext i j
  simp only [Matrix.map_apply]
  exact (h.mem_fixedField).1 (X i j).2

theorem inclK_mem_gramSU {X : GL (Fin 3) h.fixedField} (hX : X ∈ D.Iso1) :
    inclK h X ∈ gramSU h ((D.G : Matrix (Fin 3) (Fin 3) h.fixedField).map h.fixedField.subtype) := by
  obtain ⟨hI, hdet⟩ := hX
  have hI' := (CFSG.ComponentClassification.CatalogueBGraphForm.mem_isometryGroup 3 h.fixedField D.G X).1 hI
  refine mem_gramSU.2 ⟨?_, ?_⟩
  · rw [map_bar_inclK, coe_inclK]
    have := congrArg (fun M : Matrix (Fin 3) (Fin 3) h.fixedField => M.map h.fixedField.subtype) hI'
    simp only [Matrix.map_mul, Matrix.transpose_map] at this
    exact this
  · have h1 : (X : Matrix (Fin 3) (Fin 3) h.fixedField).det = 1 := by
      have := congrArg (fun u : h.fixedFieldˣ => (u : h.fixedField)) (MonoidHom.mem_ker.1 hdet)
      simpa using this
    rw [coe_inclK, ← RingHom.mapMatrix_apply, ← RingHom.map_det, h1, map_one]

@[expose] noncomputable def kappa : GL (Fin 3) h.fixedField →* GL (Fin 3) F :=
  (MulAut.conj D.Pu).toMonoidHom.comp (inclK h)

theorem kappa_mem_su {X : GL (Fin 3) h.fixedField} (hX : X ∈ D.Iso1) :
    D.kappa X ∈ unitarySU p f F 3 := by
  rw [unitarySU_eq_gramSU h 3]
  exact conj_mem_gramSU_of_gram h D.hH (D.inclK_mem_gramSU hX)

@[expose] noncomputable def Phi : ↥D.Iso1 →* ↥(unitarySU p f F 3) :=
  (D.kappa.comp D.Iso1.subtype).codRestrict (unitarySU p f F 3) (fun X => D.kappa_mem_su X.2)

theorem coe_Phi (X : ↥D.Iso1) :
    ((D.Phi X : ↥(unitarySU p f F 3)) : GL (Fin 3) F) = D.Pu * inclK h (X : GL (Fin 3) h.fixedField) * D.Pu⁻¹ :=
  rfl

theorem glAut_Pu {φ : F ≃+* F} (hφ : ∀ c, φ c = h.bar c) : A * glAut φ D.Pu = D.Pu := by
  apply Units.ext
  rw [Units.val_mul, coe_glAut]
  have hmap : (D.Pu : Matrix (Fin 3) (Fin 3) F).map φ = (D.Pu : Matrix (Fin 3) (Fin 3) F).map h.bar := by
    ext i j
    exact hφ _
  rw [hmap]
  exact D.hP

theorem Phi_fixed {φ : F ≃+* F} (hφ : ∀ c, φ c = h.bar c) (X : ↥D.Iso1) :
    A * glAut φ ((D.Phi X : ↥(unitarySU p f F 3)) : GL (Fin 3) F) * A⁻¹ = D.Phi X := by
  rw [D.coe_Phi, map_mul, map_mul, map_inv, glAut_inclK h hφ]
  have e := D.glAut_Pu hφ
  calc A * (glAut φ D.Pu * inclK h (X : GL (Fin 3) h.fixedField) * (glAut φ D.Pu)⁻¹) * A⁻¹
      = (A * glAut φ D.Pu) * inclK h (X : GL (Fin 3) h.fixedField) * (A * glAut φ D.Pu)⁻¹ := by group
    _ = D.Pu * inclK h (X : GL (Fin 3) h.fixedField) * D.Pu⁻¹ := by rw [e]

theorem exists_Phi_of_fixed {φ : F ≃+* F} (hφ : ∀ c, φ c = h.bar c) {g : ↥(unitarySU p f F 3)}
    (hg : A * glAut φ (g : GL (Fin 3) F) * A⁻¹ = g) : ∃ X : ↥D.Iso1, D.Phi X = g := by
  have e1 : A * glAut φ D.Pu = D.Pu := D.glAut_Pu hφ
  have e2 : glAut φ D.Pu = A⁻¹ * D.Pu := by
    rw [eq_inv_mul_iff_mul_eq]
    exact e1
  have hg' : A * glAut φ (g : GL (Fin 3) F) = g * A := mul_inv_eq_iff_eq_mul.1 hg
  have e3 : glAut φ (g : GL (Fin 3) F) = A⁻¹ * g * A := by
    rw [mul_assoc, eq_inv_mul_iff_mul_eq]
    exact hg'
  have hY : glAut φ (D.Pu⁻¹ * (g : GL (Fin 3) F) * D.Pu) = D.Pu⁻¹ * (g : GL (Fin 3) F) * D.Pu := by
    rw [map_mul, map_mul, map_inv, e2, e3]
    group
  have hYreal : ((D.Pu⁻¹ * (g : GL (Fin 3) F) * D.Pu : GL (Fin 3) F) : Matrix (Fin 3) (Fin 3) F).map h.bar =
      (D.Pu⁻¹ * (g : GL (Fin 3) F) * D.Pu : GL (Fin 3) F) := by
    have := congrArg (fun x : GL (Fin 3) F => (x : Matrix (Fin 3) (Fin 3) F)) hY
    simp only [coe_glAut] at this
    ext i j
    have h1 := congrFun (congrFun this i) j
    simp only [Matrix.map_apply] at h1 ⊢
    rw [← hφ]
    exact h1
  obtain ⟨X, hX⟩ := exists_inclK_of_real h hYreal
  have hgsu : (g : GL (Fin 3) F) ∈ gramSU h (1 : Matrix (Fin 3) (Fin 3) F) := by
    rw [← unitarySU_eq_gramSU h 3]
    exact g.2
  have hinv : (((D.Pu⁻¹ : GL (Fin 3) F) : Matrix (Fin 3) (Fin 3) F).map h.bar)ᵀ *
      (D.G : Matrix (Fin 3) (Fin 3) h.fixedField).map h.fixedField.subtype *
        ((D.Pu⁻¹ : GL (Fin 3) F) : Matrix (Fin 3) (Fin 3) F) = 1 :=
    inv_gram_eq h D.hH
  have hYsu := conj_mem_gramSU_of_gram h hinv hgsu
  rw [inv_inv] at hYsu
  obtain ⟨hY1, hY2⟩ := mem_gramSU.1 hYsu
  rw [hYreal] at hY1
  rw [← hX] at hY1 hY2
  have hXiso : X ∈ D.Iso := by
    unfold Iso
    rw [CFSG.ComponentClassification.CatalogueBGraphForm.mem_isometryGroup]
    apply Matrix.map_injective h.fixedField.subtype_injective
    simp only [Matrix.map_mul, Matrix.transpose_map]
    exact hY1
  have hXdet : X ∈ (Matrix.GeneralLinearGroup.det : GL (Fin 3) h.fixedField →* h.fixedFieldˣ).ker := by
    rw [MonoidHom.mem_ker]
    apply Units.ext
    have h1 : (X : Matrix (Fin 3) (Fin 3) h.fixedField).det = 1 := by
      apply h.fixedField.subtype_injective
      rw [map_one, RingHom.map_det, RingHom.mapMatrix_apply]
      exact hY2
    simpa using h1
  refine ⟨⟨X, hXiso, hXdet⟩, Subtype.ext ?_⟩
  show D.Pu * inclK h X * D.Pu⁻¹ = g
  rw [hX]
  group

theorem injective_theta_Phi {K : Type} [Group K] {θ : ↥(unitarySU p f F 3) →* K}
    (hθ : IsCover h θ) : Function.Injective (θ.comp D.Phi) := by
  rw [injective_iff_map_eq_one]
  intro X hX
  have hker : D.Phi X ∈ θ.ker := hX
  rw [hθ.ker, mem_unitaryScalars] at hker
  obtain ⟨c, hcN, hc3, hc⟩ := hker
  rw [D.coe_Phi] at hc
  have hinc : inclK h (X : GL (Fin 3) h.fixedField) = GeneralLinearGroup.scalar (Fin 3) c := by
    have e : inclK h (X : GL (Fin 3) h.fixedField) =
        D.Pu⁻¹ * (D.Pu * inclK h (X : GL (Fin 3) h.fixedField) * D.Pu⁻¹) * D.Pu := by group
    rw [e, hc, (commute_scalar c _).eq, inv_mul_cancel_right]
  have hmat := congrArg (fun Z : GL (Fin 3) F => (Z : Matrix (Fin 3) (Fin 3) F)) hinc
  simp only [coe_inclK, GeneralLinearGroup.coe_scalar] at hmat
  have hent : ∀ i j, (((X : GL (Fin 3) h.fixedField) : Matrix (Fin 3) (Fin 3) h.fixedField) i j : F) =
      if i = j then (c : F) else 0 := by
    intro i j
    have := congrFun (congrFun hmat i) j
    simpa [Matrix.scalar_apply, diagonal_apply] using this
  set c' : h.fixedField := ((X : GL (Fin 3) h.fixedField) : Matrix (Fin 3) (Fin 3) h.fixedField) 0 0 with hc'
  have hc'c : (c' : F) = c := by simpa using hent 0 0
  have hXc : ((X : GL (Fin 3) h.fixedField) : Matrix (Fin 3) (Fin 3) h.fixedField) = c' • 1 := by
    ext i j
    rw [hent i j]
    by_cases hij : i = j
    · simp [hij, hc'c]
    · simp [hij, Matrix.one_apply_ne hij]
  have hiso := (CFSG.ComponentClassification.CatalogueBGraphForm.mem_isometryGroup 3 h.fixedField D.G X).1 X.2.1
  rw [hXc, transpose_smul, transpose_one, Matrix.smul_mul, Matrix.one_mul, Matrix.mul_smul, Matrix.mul_one,
    smul_smul] at hiso
  have hG0 := gl_ne_zero D.G
  have hcc : c' * c' = 1 := by
    have h1 : (c' * c' - 1) • (D.G : Matrix (Fin 3) (Fin 3) h.fixedField) = 0 := by
      rw [sub_smul, one_smul, hiso, sub_self]
    have := (smul_eq_zero.1 h1).resolve_right hG0
    linear_combination this
  have hc3' : c' ^ 3 = 1 := by
    apply h.fixedField.subtype_injective
    have : (c : F) ^ 3 = 1 := by simpa using congrArg (fun u : Fˣ => (u : F)) hc3
    rw [map_pow, map_one]
    show (c' : F) ^ 3 = 1
    rw [hc'c]
    exact this
  have hc1 : c' = 1 := by linear_combination hc3' - c' * hcc
  apply Subtype.ext
  apply Units.ext
  rw [hXc, hc1, one_smul]
  rfl

end RealData

end Descent

section Fixed

theorem exists_fixed_rep (h : UnitaryFieldData p f F) {K : Type} [Group K]
    {θ : ↥(unitarySU p f F 3) →* K} (hθ : IsCover h θ) {σ : MulAut K} {φ : F ≃+* F}
    {A : GL (Fin 3) F} (hφ : ∀ c, φ c = h.bar c)
    (hrel : ∀ g : ↥(unitarySU p f F 3), ∃ g' : ↥(unitarySU p f F 3),
      (g' : GL (Fin 3) F) = A * glAut φ (g : GL (Fin 3) F) * A⁻¹ ∧ θ g' = σ (θ g))
    {x : K} (hx : σ x = x) :
    ∃ g : ↥(unitarySU p f F 3), θ g = x ∧ A * glAut φ (g : GL (Fin 3) F) * A⁻¹ = g := by
  obtain ⟨g, rfl⟩ := hθ.surj x
  obtain ⟨g', hg'GL, hg'θ⟩ := hrel g
  rw [hx] at hg'θ
  obtain ⟨c, hcN, hc3, hc⟩ := (theta_eq_iff h θ hθ.ker).1 hg'θ.symm
  have hz : (g' : GL (Fin 3) F) = (g : GL (Fin 3) F) * GeneralLinearGroup.scalar (Fin 3) c := by
    apply Units.ext
    rw [Units.val_mul, GeneralLinearGroup.coe_scalar]
    exact hc
  have hc0 : (c : F) ≠ 0 := c.ne_zero
  have hbarc : h.bar (c : F) = (c : F)⁻¹ := by
    have : (c : F) * h.bar (c : F) = 1 := hcN
    exact eq_inv_of_mul_eq_one_right this
  have hcN' : h.norm (((c⁻¹ : Fˣ)) : F) = 1 := by
    show ((c⁻¹ : Fˣ) : F) * h.bar ((c⁻¹ : Fˣ) : F) = 1
    rw [Units.val_inv_eq_inv_val, map_inv₀, hbarc, inv_inv]
    exact inv_mul_cancel₀ hc0
  have hc3' : (c⁻¹) ^ 3 = 1 := by rw [inv_pow, hc3, inv_one]
  have hwmem : GeneralLinearGroup.scalar (Fin 3) c⁻¹ ∈ unitarySU p f F 3 :=
    scalar_mem_unitarySU h (by norm_num) hcN' hc3'
  let w : ↥(unitarySU p f F 3) := ⟨GeneralLinearGroup.scalar (Fin 3) c⁻¹, hwmem⟩
  have hwθ : θ w = 1 := by
    have : w ∈ θ.ker := by
      rw [hθ.ker, mem_unitaryScalars]
      exact ⟨c⁻¹, hcN', hc3', rfl⟩
    exact this
  have hφw : glAut φ (GeneralLinearGroup.scalar (Fin 3) c⁻¹) = GeneralLinearGroup.scalar (Fin 3) c := by
    apply Units.ext
    rw [coe_glAut, GeneralLinearGroup.coe_scalar, GeneralLinearGroup.coe_scalar]
    ext i j
    by_cases hij : i = j
    · simp [Matrix.scalar_apply, hij, hφ, hbarc]
    · simp [Matrix.scalar_apply, hij]
  have hcc : (c * c : Fˣ) = c⁻¹ := eq_inv_of_mul_eq_one_left (by simpa [pow_succ] using hc3)
  refine ⟨g * w, ?_, ?_⟩
  · rw [map_mul, hwθ, mul_one]
  · show A * glAut φ ((g : GL (Fin 3) F) * GeneralLinearGroup.scalar (Fin 3) c⁻¹) * A⁻¹ =
      (g : GL (Fin 3) F) * GeneralLinearGroup.scalar (Fin 3) c⁻¹
    rw [map_mul, hφw]
    have hcentral : A * GeneralLinearGroup.scalar (Fin 3) c * A⁻¹ = GeneralLinearGroup.scalar (Fin 3) c := by
      rw [(commute_scalar c A).eq, mul_inv_cancel_right]
    calc A * (glAut φ (g : GL (Fin 3) F) * GeneralLinearGroup.scalar (Fin 3) c) * A⁻¹
        = (A * glAut φ (g : GL (Fin 3) F) * A⁻¹) * (A * GeneralLinearGroup.scalar (Fin 3) c * A⁻¹) := by group
      _ = (g * GeneralLinearGroup.scalar (Fin 3) c) * GeneralLinearGroup.scalar (Fin 3) c := by
          rw [hcentral, ← hz, ← hg'GL]
      _ = (g : GL (Fin 3) F) * GeneralLinearGroup.scalar (Fin 3) c⁻¹ := by
          rw [mul_assoc, ← map_mul, hcc]

end Fixed

section Graph

theorem ringChar_ne_two_of_two_ne_zero {R : Type} [Ring R] (h2 : (2 : R) ≠ 0) : ringChar R ≠ 2 :=
  fun h => h2 (by
    have : CharP R 2 := h ▸ ringChar.charP R
    exact CharTwo.two_eq_zero)

theorem graphData_of_typeII (h : UnitaryFieldData p f F) (h5 : 5 ≤ p ^ f) (hq : Odd (p ^ f))
    {K : Type} [Group K] {θ : ↥(unitarySU p f F 3) →* K} (hθ : IsCover h θ)
    {σ : MulAut K} {φ : F ≃+* F} {A : GL (Fin 3) F} (hφ : ∀ c, φ c = h.bar c)
    (hAu : ((A : Matrix (Fin 3) (Fin 3) F).map h.bar)ᵀ * (A : Matrix (Fin 3) (Fin 3) F) = 1)
    (hAA : (A : Matrix (Fin 3) (Fin 3) F) * (A : Matrix (Fin 3) (Fin 3) F).map h.bar = 1)
    (hrel : ∀ g : ↥(unitarySU p f F 3), ∃ g' : ↥(unitarySU p f F 3),
      (g' : GL (Fin 3) F) = A * glAut φ (g : GL (Fin 3) F) * A⁻¹ ∧ θ g' = σ (θ g)) :
    ∃ N : Subgroup K, CFSG.GH74.KGroups.L3Eps.GraphData K σ N := by
  have h2 : (2 : F) ≠ 0 := two_ne_zero_of_odd_pow h hq
  have : Finite F := h.finite
  obtain ⟨D⟩ := exists_realData h h2 hAu hAA
  have hk2 : (2 : h.fixedField) ≠ 0 := CFSG.GH74.Generic.S45.Uni.two_ne_zero_fixedField h h2
  have hk : ringChar h.fixedField ≠ 2 := ringChar_ne_two_of_two_ne_zero hk2
  have h3 : Nat.card h.fixedField ≠ 3 := by rw [h.card_fixedField]; omega
  have hΩq := isQuasisimple_commutator_isometryGroup hk h3 D.G D.hGs
  let Ω : Subgroup (GL (Fin 3) h.fixedField) := ⁅D.Iso, D.Iso⁆
  have hΩle : Ω ≤ D.Iso1 := by
    refine Subgroup.commutator_le.2 fun x hx y hy => ⟨?_, ?_⟩
    · exact D.Iso.mul_mem (D.Iso.mul_mem (D.Iso.mul_mem hx hy) (D.Iso.inv_mem hx)) (D.Iso.inv_mem hy)
    · show ⁅x, y⁆ ∈ (Matrix.GeneralLinearGroup.det : GL (Fin 3) h.fixedField →* h.fixedFieldˣ).ker
      rw [MonoidHom.mem_ker, map_commutatorElement]
      exact commutatorElement_eq_one_iff_mul_comm.2 (mul_comm _ _)
  let ρ : ↥D.Iso1 →* K := θ.comp D.Phi
  have hρ : Function.Injective ρ := D.injective_theta_Phi hθ
  have hnorm : ∀ (X : ↥D.Iso1), ∀ ω ∈ Ω.subgroupOf D.Iso1, X * ω * X⁻¹ ∈ Ω.subgroupOf D.Iso1 := by
    intro X ω hω
    have hω' : (ω : GL (Fin 3) h.fixedField) ∈ Ω := hω
    show (X : GL (Fin 3) h.fixedField) * (ω : GL (Fin 3) h.fixedField) * (X : GL (Fin 3) h.fixedField)⁻¹ ∈ Ω
    have : (X : GL (Fin 3) h.fixedField) * (ω : GL (Fin 3) h.fixedField) * (X : GL (Fin 3) h.fixedField)⁻¹ =
        ⁅(X : GL (Fin 3) h.fixedField), (ω : GL (Fin 3) h.fixedField)⁆ * (ω : GL (Fin 3) h.fixedField) := by
      rw [commutatorElement_def]
      group
    rw [this]
    exact Ω.mul_mem (Subgroup.commutator_mem_commutator X.2.1 (hΩle hω').1) hω'
  have hcomm : ∀ (X Y : ↥D.Iso1), ⁅X, Y⁆ ∈ Ω.subgroupOf D.Iso1 := by
    intro X Y
    show ⁅(X : GL (Fin 3) h.fixedField), (Y : GL (Fin 3) h.fixedField)⁆ ∈ Ω
    exact Subgroup.commutator_mem_commutator X.2.1 Y.2.1
  have hfixPhi : ∀ X : ↥D.Iso1, σ (ρ X) = ρ X := by
    intro X
    obtain ⟨g', hg'GL, hg'θ⟩ := hrel (D.Phi X)
    have hgg : g' = D.Phi X := Subtype.ext (by rw [hg'GL]; exact D.Phi_fixed hφ X)
    rw [hgg] at hg'θ
    exact hg'θ.symm
  refine ⟨(Ω.subgroupOf D.Iso1).map ρ, ?_, ?_, ?_, ?_⟩
  · have e1 : ↥(Ω.subgroupOf D.Iso1) ≃* ↥Ω := Subgroup.subgroupOfEquivOfLe hΩle
    have e2 : ↥(Ω.subgroupOf D.Iso1) ≃* ↥((Ω.subgroupOf D.Iso1).map ρ) :=
      Subgroup.equivMapOfInjective _ ρ hρ
    exact LocalCores.isQuasisimple_of_mulEquiv (e1.symm.trans e2) hΩq
  · rintro n ⟨ω, -, rfl⟩
    exact hfixPhi ω
  · intro x hx n hn
    obtain ⟨g, rfl, hg⟩ := exists_fixed_rep h hθ hφ hrel hx
    obtain ⟨X, hX⟩ := D.exists_Phi_of_fixed hφ hg
    obtain ⟨ω, hω, rfl⟩ := hn
    refine ⟨X * ω * X⁻¹, hnorm X ω hω, ?_⟩
    have : θ g = ρ X := by rw [← hX]; rfl
    rw [this]
    simp only [map_mul, map_inv]
  · intro x y hx hy
    obtain ⟨g, rfl, hg⟩ := exists_fixed_rep h hθ hφ hrel hx
    obtain ⟨X, hX⟩ := D.exists_Phi_of_fixed hφ hg
    obtain ⟨g', rfl, hg'⟩ := exists_fixed_rep h hθ hφ hrel hy
    obtain ⟨Y, hY⟩ := D.exists_Phi_of_fixed hφ hg'
    refine ⟨⁅X, Y⁆, hcomm X Y, ?_⟩
    have h1 : θ g = ρ X := by rw [← hX]; rfl
    have h2' : θ g' = ρ Y := by rw [← hY]; rfl
    rw [h1, h2', map_commutatorElement]

end Graph

theorem graphData_of_cover (h : UnitaryFieldData p f F) (hp : p ≠ 2) (h5 : 5 ≤ p ^ f) (hq : Odd (p ^ f))
    {K : Type} [Group K] {θ : ↥(unitarySU p f F 3) →* K} (hθ : IsCover h θ)
    {σ : MulAut K} (hσ : σ * σ = 1)
    (hout : σ ∉ CFSG.ComponentClassification.OuterAutomorphisms.inner K) :
    ∃ N : Subgroup K, CFSG.GH74.KGroups.L3Eps.GraphData K σ N := by
  rcases involution_type h hp h5 hθ hσ with ⟨A, hAu, hAA, hrel⟩ | ⟨φ, A, hφ, hAu, hAA, hrel⟩
  · exfalso
    obtain ⟨y, hy⟩ := exists_conj_of_typeI h hθ hAu hAA hrel
    exact hout ⟨y, hy⟩
  · exact graphData_of_typeII h h5 hq hθ hφ hAu hAA hrel

end CFSG.GH74.KGroups.L3Eps.Uni
