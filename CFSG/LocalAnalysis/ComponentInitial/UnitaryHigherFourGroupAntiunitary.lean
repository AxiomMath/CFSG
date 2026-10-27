module

public import CFSG.LocalAnalysis.ComponentInitial.UnitaryHigherFourGroupTransport
public import CFSG.LocalAnalysis.ComponentInitial.UnitaryHigherConjDescent

public section

namespace CFSG.LocalAnalysis.ComponentInitial.UnitaryHigher

open Matrix Module CFSG.ClassicalGroups.UnitaryFlag
open LinearMap (BilinForm)
open CFSG.LocalAnalysis.ComponentInitial.FourGroupOddBilinear (isometrySL mem_isometrySL)

variable {p f : ℕ} {K : Type} [Field K] {r ε : ℕ}

theorem hypForm_semilinearMatrixMap (h : UnitaryFieldData p f K) {A : GL (HypIndex r ε) K}
    (hA : A ∈ hypUnitary h r ε) (v w : HypIndex r ε → K) :
    hypForm h r ε (semilinearMatrixMap h (A : Matrix (HypIndex r ε) (HypIndex r ε) K) v)
      (semilinearMatrixMap h (A : Matrix (HypIndex r ε) (HypIndex r ε) K) w) =
        h.bar (hypForm h r ε v w) := by
  rw [semilinearMatrixMap_apply, semilinearMatrixMap_apply, gramForm_mulVec, mem_hypUnitary.mp hA,
    gramForm_apply, gramForm_apply]
  simp only [dotProduct, map_sum, map_mul, h.bar_bar]
  refine Finset.sum_congr rfl fun a _ => ?_
  rw [RingHom.map_mulVec, hypGram_map]
  rfl

theorem scalar_transpose_mul_mul {ι k : Type*} [Fintype ι] [DecidableEq ι] [CommRing k] (a : k)
    (M : Matrix ι ι k) : (Matrix.scalar ι a)ᵀ * M * Matrix.scalar ι a = (a * a) • M := by
  ext i j
  rw [scalar_apply, diagonal_transpose, mul_diagonal, diagonal_mul, Matrix.smul_apply, smul_eq_mul]
  ring

theorem mul_map_bar_conj_eq (h : UnitaryFieldData p f K) {ι κ : Type*} [Fintype ι] [Fintype κ]
    [DecidableEq ι] [DecidableEq κ] {A : Matrix ι ι K} {Hm : Matrix ι κ K} {Wm : Matrix κ ι K}
    (hHW : Hm * Wm = 1) (hWH : Wm * Hm = 1) {d : K} (hAH : A * Hm.map h.bar = d • Hm)
    {G : Matrix κ κ K} (hG : G.map h.bar = G) :
    A * (Hm * G * Wm).map h.bar = (Hm * G * Wm) * A := by
  have h1 : Wm * A * Hm.map h.bar = d • (1 : Matrix κ κ K) := by
    rw [Matrix.mul_assoc, hAH, Matrix.mul_smul, hWH]
  have h3 : Hm.map h.bar * Wm.map h.bar = 1 := by
    rw [← Matrix.map_mul, hHW, Matrix.map_one _ (map_zero h.bar) (map_one h.bar)]
  have hWA : Wm * A = d • Wm.map h.bar := by
    calc Wm * A = Wm * A * (Hm.map h.bar * Wm.map h.bar) := by rw [h3, Matrix.mul_one]
      _ = d • Wm.map h.bar := by rw [← Matrix.mul_assoc, h1, Matrix.smul_mul, Matrix.one_mul]
  rw [Matrix.map_mul, Matrix.map_mul, hG, ← Matrix.mul_assoc, ← Matrix.mul_assoc, hAH,
    Matrix.smul_mul, Matrix.smul_mul, Matrix.mul_assoc (Hm * G), hWA, Matrix.mul_smul]

section Inclusion

variable (h : UnitaryFieldData p f K) {m : ℕ} {C₀ : Matrix (Fin m) (Fin m) K}
  {R : Matrix (Fin m) (Fin m) h.fixedField} {s : K} (hs0 : s ≠ 0)
  (hRC : R.map h.fixedField.subtype = s • C₀)

include hs0 hRC in
theorem map_mem_gramSU_of_mem_isometrySL {gS : Matrix.SpecialLinearGroup (Fin m) h.fixedField}
    (hgS : gS ∈ isometrySL R) :
    GeneralLinearGroup.map h.fixedField.subtype (Matrix.SpecialLinearGroup.toGL gS) ∈
      gramSU h C₀ := by
  have hg : (gS : Matrix (Fin m) (Fin m) h.fixedField)ᵀ * R *
      (gS : Matrix (Fin m) (Fin m) h.fixedField) = R := mem_isometrySL.mp hgS
  have hdet : (gS : Matrix (Fin m) (Fin m) h.fixedField).det = 1 := gS.prop
  rw [mem_gramSU]
  change (((gS : Matrix (Fin m) (Fin m) h.fixedField).map h.fixedField.subtype).map h.bar)ᵀ *
      C₀ * (gS : Matrix (Fin m) (Fin m) h.fixedField).map h.fixedField.subtype = C₀ ∧
    ((gS : Matrix (Fin m) (Fin m) h.fixedField).map h.fixedField.subtype).det = 1
  have hbarG : ((gS : Matrix (Fin m) (Fin m) h.fixedField).map h.fixedField.subtype).map h.bar =
      (gS : Matrix (Fin m) (Fin m) h.fixedField).map h.fixedField.subtype :=
    Matrix.ext fun i j => h.mem_fixedField.mp ((gS : Matrix (Fin m) (Fin m) h.fixedField) i j).2
  refine ⟨?_, ?_⟩
  · rw [hbarG]
    have h1 := congrArg (fun M => M.map h.fixedField.subtype) hg
    rw [Matrix.map_mul, Matrix.map_mul, transpose_map, hRC, Matrix.mul_smul,
      Matrix.smul_mul] at h1
    exact smul_right_injective (Matrix (Fin m) (Fin m) K) hs0 h1
  · rw [← RingHom.mapMatrix_apply, ← RingHom.map_det, hdet, map_one]

@[expose] noncomputable def isometryToGramSU : isometrySL R →* gramSU h C₀ :=
  ((GeneralLinearGroup.map h.fixedField.subtype).comp (Matrix.SpecialLinearGroup.toGL.comp
    (isometrySL R).subtype)).codRestrict (gramSU h C₀)
      fun g => map_mem_gramSU_of_mem_isometrySL h hs0 hRC g.2

theorem coe_isometryToGramSU (g : isometrySL R) :
    (((isometryToGramSU h hs0 hRC g : gramSU h C₀) : GL (Fin m) K) : Matrix (Fin m) (Fin m) K) =
      ((g : Matrix.SpecialLinearGroup (Fin m) h.fixedField) :
        Matrix (Fin m) (Fin m) h.fixedField).map h.fixedField.subtype :=
  rfl

include hs0 hRC in
theorem mem_scalars_iff_mem_normOneScalars (hm : 0 < m) (hR : R ≠ 0) (g : isometrySL R) :
    (g : Matrix.SpecialLinearGroup (Fin m) h.fixedField) ∈ LinearFlag.scalars m h.fixedField ↔
      isometryToGramSU h hs0 hRC g ∈ normOneScalars h (gramSU h C₀) m := by
  obtain ⟨i₀, j₀, hR0⟩ : ∃ i j, R i j ≠ 0 := by
    by_contra hall
    push Not at hall
    exact hR (Matrix.ext hall)
  constructor
  · rintro ⟨a, han, hga⟩
    have hg : ((g : Matrix.SpecialLinearGroup (Fin m) h.fixedField) :
        Matrix (Fin m) (Fin m) h.fixedField)ᵀ * R *
          (g : Matrix.SpecialLinearGroup (Fin m) h.fixedField) = R := mem_isometrySL.mp g.2
    rw [hga, scalar_transpose_mul_mul] at hg
    have ha2 : (a : h.fixedField) * a = 1 := by
      have h1 := congrFun (congrFun hg i₀) j₀
      rw [Matrix.smul_apply, smul_eq_mul] at h1
      exact mul_right_cancel₀ hR0 (h1.trans (one_mul _).symm)
    refine ⟨Units.map h.fixedField.subtype.toMonoidHom a, ?_, ?_, ?_⟩
    · rw [Units.coe_map, UnitaryFieldData.norm]
      change ((a : h.fixedField) : K) * h.bar ((a : h.fixedField) : K) = 1
      rw [h.mem_fixedField.mp (a : h.fixedField).2, ← Subfield.coe_mul, ha2, Subfield.coe_one]
    · rw [← map_pow, han, map_one]
    · refine Units.ext ?_
      change ((g : Matrix.SpecialLinearGroup (Fin m) h.fixedField) :
        Matrix (Fin m) (Fin m) h.fixedField).map h.fixedField.subtype = _
      rw [hga, GeneralLinearGroup.coe_scalar, scalar_apply, scalar_apply, diagonal_map (map_zero _),
        Units.coe_map]
      rfl
  · rintro ⟨c', -, hcn, hgc⟩
    have hentry : ∀ i j, (((g : Matrix.SpecialLinearGroup (Fin m) h.fixedField) :
        Matrix (Fin m) (Fin m) h.fixedField) i j : K) =
          Matrix.scalar (Fin m) (c' : K) i j := by
      intro i j
      have h1 := congrArg (fun M : GL (Fin m) K => (M : Matrix (Fin m) (Fin m) K) i j) hgc
      rw [← GeneralLinearGroup.coe_scalar]
      exact h1
    set a := ((g : Matrix.SpecialLinearGroup (Fin m) h.fixedField) :
      Matrix (Fin m) (Fin m) h.fixedField) ⟨0, hm⟩ ⟨0, hm⟩ with ha
    have hac : (a : K) = c' := by
      rw [ha, hentry, scalar_apply, diagonal_apply_eq]
    have ha0 : a ≠ 0 := fun h0 => c'.ne_zero (by rw [← hac, h0, ZeroMemClass.coe_zero])
    refine ⟨Units.mk0 a ha0, ?_, ?_⟩
    · refine Units.ext (Subtype.ext ?_)
      rw [Units.val_pow_eq_pow_val, Units.val_mk0, Units.val_one, SubmonoidClass.coe_pow, hac,
        OneMemClass.coe_one, ← Units.val_pow_eq_pow_val, hcn, Units.val_one]
    · refine Matrix.ext fun i j => Subtype.ext ?_
      rw [hentry, Units.val_mk0, scalar_apply, scalar_apply, diagonal_apply, diagonal_apply]
      split_ifs
      · exact hac.symm
      · rfl

end Inclusion

theorem exists_descended_form (h : UnitaryFieldData p f K) (hp : p ≠ 2) (hn : 1 ≤ 2 * r + ε)
    {A : GL (HypIndex r ε) K} (hA : A ∈ hypUnitary h r ε) {c : K} (hc0 : c ≠ 0)
    (hAc : (A : Matrix (HypIndex r ε) (HypIndex r ε) K) *
      (A : Matrix (HypIndex r ε) (HypIndex r ε) K).map h.bar = c • 1) :
    ∃ (b t : Kˣ) (s : K), h.bar (t : K) = -(t : K) ∧ s ≠ 0 ∧
      (∀ v, ((b : K) • semilinearMatrixMap h (A : Matrix (HypIndex r ε) (HypIndex r ε) K))
        (((b : K) • semilinearMatrixMap h (A : Matrix (HypIndex r ε) (HypIndex r ε) K)) v) = v) ∧
      finrank h.fixedField (conjFixed h
        ((b : K) • semilinearMatrixMap h (A : Matrix (HypIndex r ε) (HypIndex r ε) K))) =
          2 * r + ε ∧
      ∃ B : BilinForm h.fixedField (conjFixed h
          ((b : K) • semilinearMatrixMap h (A : Matrix (HypIndex r ε) (HypIndex r ε) K))),
        (∀ v w, (B v w : K) = s * hypForm h r ε v w) ∧ B.Nondegenerate ∧ (B.IsSymm ∨ B.IsAlt) := by
  have : CharP K p := h.charP
  have hpodd : Odd p := h.prime.odd_of_ne_two hp
  set Am := (A : Matrix (HypIndex r ε) (HypIndex r ε) K) with hAm
  set τ₀ := semilinearMatrixMap h Am with hτ₀def
  have hμ : ∀ v, τ₀ (τ₀ v) = ((Units.mk0 c hc0 : Kˣ) : K) • v := by
    intro v
    rw [hτ₀def, semilinearMatrixMap_apply, semilinearMatrixMap_apply, Units.val_mk0]
    have hbar : (fun i => h.bar ((Am *ᵥ fun j => h.bar (v j)) i)) = Am.map h.bar *ᵥ v := by
      funext i
      rw [RingHom.map_mulVec]
      congr 1
      funext j
      exact h.bar_bar (v j)
    rw [hbar, mulVec_mulVec, hAc, smul_mulVec, one_mulVec]
  have hτ₀ : Function.Bijective τ₀ := by
    refine ⟨fun v w hvw => ?_, fun w => ⟨τ₀ ((c⁻¹ : K) • w), ?_⟩⟩
    · have h1 := congrArg τ₀ hvw
      rw [hμ, hμ, Units.val_mk0] at h1
      exact smul_right_injective _ hc0 h1
    · rw [hμ, Units.val_mk0, smul_smul, mul_inv_cancel₀ hc0, one_smul]
  have hfinV : finrank K (HypIndex r ε → K) = 2 * r + ε := by
    rw [Module.finrank_fintype_fun_eq_card, card_hypIndex]
  obtain ⟨hμ1, ⟨b, hb⟩, ⟨t, ht⟩, hall⟩ := odd_unitary_conjugate_semilinear_involution_descent h
    hpodd (by omega) (hypForm_isSymm h) (hypForm_separatingLeft h) τ₀ hτ₀
    (hypForm_semilinearMatrixMap h hA) (Units.mk0 c hc0) hμ
  obtain ⟨hττ, hfinW, -, hB1, hB2⟩ := hall b t hb ht
  refine ⟨b, t, ?_⟩
  rcases hμ1 with h1 | h1
  · obtain ⟨B, hB, hsymm, hnd, -⟩ := hB1 h1
    exact ⟨1, ht, one_ne_zero, hττ, hfinW.trans hfinV, B, fun v w => by rw [hB, one_mul], hnd,
      Or.inl hsymm⟩
  · obtain ⟨B, hB, halt, hnd, -, -⟩ := hB2 h1
    exact ⟨(t : K)⁻¹, ht, inv_ne_zero t.ne_zero, hττ, hfinW.trans hfinV, B, hB, hnd, Or.inr halt⟩

theorem exists_fixed_transport (h : UnitaryFieldData p f K) (hp : p ≠ 2)
    {τ : (HypIndex r ε → K) →ₛₗ[h.bar] (HypIndex r ε → K)} (hττ : ∀ v, τ (τ v) = v)
    {t : K} (ht : h.bar t = -t) (ht0 : t ≠ 0)
    (hfin : finrank h.fixedField (conjFixed h τ) = 2 * r + ε) {s : K}
    {B : BilinForm h.fixedField (conjFixed h τ)}
    (hBs : ∀ v w, (B v w : K) = s * hypForm h r ε v w) (hBnd : B.Nondegenerate)
    (hBsym : B.IsSymm ∨ B.IsAlt) :
    ∃ (Hm : Matrix (HypIndex r ε) (Fin (2 * r + ε)) K) (Wm : Matrix (Fin (2 * r + ε))
      (HypIndex r ε) K) (C₀ : Matrix (Fin (2 * r + ε)) (Fin (2 * r + ε)) K)
      (R : Matrix (Fin (2 * r + ε)) (Fin (2 * r + ε)) h.fixedField),
      Hm * Wm = 1 ∧ Wm * Hm = 1 ∧ IsGramHypTransport h C₀ Wm ∧
      R.map h.fixedField.subtype = s • C₀ ∧ R.det ≠ 0 ∧ (Rᵀ = R ∨ Rᵀ = -R) ∧
      ∀ j, τ (fun a => Hm a j) = fun a => Hm a j := by
  have : CharP K p := h.charP
  have h2 : (2 : K) ≠ 0 := by
    intro h0
    have h3 : ((2 : ℕ) : K) = 0 := by exact_mod_cast h0
    have h4 := Nat.le_of_dvd two_pos ((CharP.cast_eq_zero_iff K p 2).mp h3)
    have := h.prime.two_le
    omega
  have : FiniteDimensional h.fixedField (conjFixed h τ) := finite_conjFixed
  set bW := Module.finBasisOfFinrankEq h.fixedField (conjFixed h τ) hfin with hbWdef
  set bV := conjFixedBasis hττ ht ht0 h2 bW with hbVdef
  have hHij : ∀ a j, (Pi.basisFun K (HypIndex r ε)).toMatrix bV a j =
      (bW j : HypIndex r ε → K) a := by
    intro a j
    rw [Basis.toMatrix_apply, Pi.basisFun_repr, hbVdef, conjFixedBasis_apply]
  set Hm := (Pi.basisFun K (HypIndex r ε)).toMatrix bV with hHmdef
  have hHcol : ∀ j, Hm *ᵥ Pi.single j 1 = (bW j : HypIndex r ε → K) := by
    intro j
    rw [mulVec_single_one]
    funext a
    rw [col_apply, hHij]
  refine ⟨Hm, bV.toMatrix (Pi.basisFun K (HypIndex r ε)), (Hm.map h.bar)ᵀ * hypGram r ε K * Hm,
    BilinForm.toMatrix bW B, (Pi.basisFun K (HypIndex r ε)).toMatrix_mul_toMatrix_flip bV,
    bV.toMatrix_mul_toMatrix_flip (Pi.basisFun K (HypIndex r ε)), ?_, ?_,
    (BilinForm.nondegenerate_iff_det_ne_zero bW).mp hBnd, ?_, fun j => ?_⟩
  · change ((bV.toMatrix (Pi.basisFun K (HypIndex r ε))).map h.bar)ᵀ *
      ((Hm.map h.bar)ᵀ * hypGram r ε K * Hm) * bV.toMatrix (Pi.basisFun K (HypIndex r ε)) =
        hypGram r ε K
    rw [← barTranspose_mul_mul, (Pi.basisFun K (HypIndex r ε)).toMatrix_mul_toMatrix_flip bV,
      Matrix.map_one _ (map_zero h.bar) (map_one h.bar), transpose_one, Matrix.one_mul,
      Matrix.mul_one]
  · refine Matrix.ext fun i j => ?_
    rw [map_apply, BilinForm.toMatrix_apply]
    change ((B (bW i) (bW j) : h.fixedField) : K) = _
    rw [hBs, Matrix.smul_apply, smul_eq_mul,
      ← gramForm_single h ((Hm.map h.bar)ᵀ * hypGram r ε K * Hm) i j, ← gramForm_mulVec, hHcol,
      hHcol]
  · rcases hBsym with hsymm | halt
    · left
      refine Matrix.ext fun i j => ?_
      rw [transpose_apply, BilinForm.toMatrix_apply, BilinForm.toMatrix_apply]
      exact hsymm.eq (bW j) (bW i)
    · right
      refine Matrix.ext fun i j => ?_
      rw [transpose_apply, Matrix.neg_apply, BilinForm.toMatrix_apply, BilinForm.toMatrix_apply]
      exact (halt.neg_eq (bW i) (bW j)).symm
  · have hcol : (fun a => Hm a j) = (bW j : HypIndex r ε → K) := funext fun a => hHij a j
    rw [hcol]
    exact mem_conjFixed.mp (bW j).2

theorem exists_four_group_of_antiunitary (h : UnitaryFieldData p f K) (hp : p ≠ 2)
    (hn : 3 ≤ 2 * r + ε) {A : GL (HypIndex r ε) K} (hA : A ∈ hypUnitary h r ε) {c : K}
    (hc0 : c ≠ 0) (hAc : (A : Matrix (HypIndex r ε) (HypIndex r ε) K) *
      (A : Matrix (HypIndex r ε) (HypIndex r ε) K).map h.bar = c • 1) :
    ∃ V : Subgroup (hypPSU h r ε), IsElementaryAbelian 2 V ∧ Nat.card V = 4 ∧
      ∀ x ∈ V, ∃ g : hypSU h r ε, hypProj h r ε g = x ∧
        (A : Matrix (HypIndex r ε) (HypIndex r ε) K) *
          ((g : GL (HypIndex r ε) K) : Matrix (HypIndex r ε) (HypIndex r ε) K).map h.bar =
            ((g : GL (HypIndex r ε) K) : Matrix (HypIndex r ε) (HypIndex r ε) K) *
              (A : Matrix (HypIndex r ε) (HypIndex r ε) K) := by
  have : CharP K p := h.charP
  have : Finite K := h.finite
  obtain ⟨b, t, s, ht, hs0, hττ, hfin, B, hBs, hBnd, hBsym⟩ :=
    exists_descended_form h hp (by omega) hA hc0 hAc
  obtain ⟨Hm, Wm, C₀, R, hHW, hWH, hW, hRC, hRdet, hRsym, hcol⟩ :=
    exists_fixed_transport h hp hττ ht t.ne_zero hfin hBs hBnd hBsym
  have hk : ringChar h.fixedField ≠ 2 := by
    rw [ringChar.eq h.fixedField p]
    exact hp
  obtain ⟨V₄, hV₄le, hV₄ab, hV₄card⟩ := odd_bilinear_isometry_projective_four_group hk hn
    (Matrix.GeneralLinearGroup.mkOfDetNeZero R hRdet) hRsym
  have hR0 : R ≠ 0 := fun h0 => by
    have : Nonempty (Fin (2 * r + ε)) := ⟨⟨0, by omega⟩⟩
    exact hRdet (by rw [h0, Matrix.det_zero])
  set ρ := (LinearFlag.proj (2 * r + ε) h.fixedField).comp (isometrySL R).subtype with hρdef
  set φ : isometrySL R →* hypPSU h r ε := (gramHypProjEquiv h C₀ hW).toMonoidHom.comp
    ((QuotientGroup.mk' _).comp (isometryToGramSU h hs0 hRC)) with hφdef
  have hker : ρ.ker = φ.ker := by
    ext g
    rw [MonoidHom.mem_ker, MonoidHom.mem_ker]
    change LinearFlag.proj _ _ (g : Matrix.SpecialLinearGroup (Fin (2 * r + ε)) h.fixedField) = 1 ↔
      gramHypProjEquiv h C₀ hW (QuotientGroup.mk (isometryToGramSU h hs0 hRC g)) = 1
    rw [LinearFlag.proj_eq_one_iff, MulEquiv.map_eq_one_iff, QuotientGroup.eq_one_iff]
    exact mem_scalars_iff_mem_normOneScalars h hs0 hRC (by omega) hR0 g
  have hV₄le' : V₄ ≤ ρ.range := by
    rw [hρdef, MonoidHom.range_comp, Subgroup.range_subtype]
    exact hV₄le
  have : IsElementaryAbelian 2 V₄ := hV₄ab
  obtain ⟨V, hVab, hVcard, hVmem⟩ := exists_subgroup_of_ker_eq (p := 2) ρ φ hker V₄ hV₄le'
  have hAH : (A : Matrix (HypIndex r ε) (HypIndex r ε) K) * Hm.map h.bar =
      ((b : K)⁻¹) • Hm := by
    refine Matrix.ext fun a j => ?_
    have h3 := congrFun (hcol j) a
    change (b : K) * ((A : Matrix (HypIndex r ε) (HypIndex r ε) K) *ᵥ
      fun k => h.bar (Hm k j)) a = Hm a j at h3
    rw [Matrix.smul_apply, smul_eq_mul, ← h3, ← mul_assoc, inv_mul_cancel₀ b.ne_zero, one_mul]
    simp only [Matrix.mul_apply, Matrix.mulVec, dotProduct, Matrix.map_apply]
  have hgramInv : gramHypInv h C₀ Wm = Hm := by
    calc gramHypInv h C₀ Wm = gramHypInv h C₀ Wm * (Wm * Hm) := by rw [hWH, Matrix.mul_one]
      _ = Hm := by rw [← Matrix.mul_assoc, gramHypInv_mul hW, Matrix.one_mul]
  refine ⟨V, hVab, hVcard.trans hV₄card, fun x hx => ?_⟩
  obtain ⟨g, rfl⟩ := hVmem x hx
  refine ⟨gramHypEquiv h C₀ hW (isometryToGramSU h hs0 hRC g),
    (gramHypProjEquiv_mk hW (isometryToGramSU h hs0 hRC g)).symm, ?_⟩
  rw [coe_gramHypEquiv, hgramInv]
  refine mul_map_bar_conj_eq h hHW hWH hAH ?_
  rw [coe_isometryToGramSU]
  exact Matrix.ext fun i j => h.mem_fixedField.mp (((g : Matrix.SpecialLinearGroup
    (Fin (2 * r + ε)) h.fixedField) : Matrix (Fin (2 * r + ε)) (Fin (2 * r + ε)) h.fixedField) i
      j).2

end CFSG.LocalAnalysis.ComponentInitial.UnitaryHigher
