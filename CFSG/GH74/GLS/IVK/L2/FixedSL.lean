module

public import CFSG.GH74.GLS.IVK.L2.FixedPGL
public import CFSG.GH74.GLS.IVK.Defs

public section

namespace CFSG.GH74.GLS.IVK

open CFSG CFSG.GorensteinWalter CFSG.Assembly.LowTwoRank

section SLIncl

variable {F : Type} [Field F] (σ : F ≃+* F)

theorem exists_specialLinear_map_eq (S : Matrix.SpecialLinearGroup (Fin 2) F)
    (hS : ∀ i j, σ (S i j) = S i j) :
    ∃ M : Matrix.SpecialLinearGroup (Fin 2) (fixedField σ),
      Matrix.SpecialLinearGroup.map (fixedField σ).subtype M = S := by
  let W : Matrix (Fin 2) (Fin 2) (fixedField σ) :=
    fun i j => ⟨S i j, (mem_fixedField_iff σ _).mpr (hS i j)⟩
  have hW : W.map (fixedField σ).subtype = (S : Matrix (Fin 2) (Fin 2) F) := rfl
  have hdet : W.det = 1 := by
    apply (fixedField σ).subtype.injective
    have h1 : (fixedField σ).subtype W.det = (S : Matrix (Fin 2) (Fin 2) F).det := by
      rw [RingHom.map_det]
      exact congrArg Matrix.det hW
    rw [h1, Matrix.SpecialLinearGroup.det_coe, map_one]
  exact ⟨⟨W, hdet⟩, Subtype.ext hW⟩

@[expose] noncomputable def slIncl :
    Matrix.SpecialLinearGroup (Fin 2) (fixedField σ) →* SL2 F :=
  (specialLinearGroupEquivStatedSL 2 F).toMonoidHom.comp
    (Matrix.SpecialLinearGroup.map (fixedField σ).subtype)

theorem slIncl_injective : Function.Injective (slIncl σ) := by
  intro M N h
  have h1 := (specialLinearGroupEquivStatedSL 2 F).injective h
  refine Matrix.SpecialLinearGroup.ext _ _ fun i j => Subtype.ext ?_
  exact congrArg (fun S : Matrix.SpecialLinearGroup (Fin 2) F => (S : Matrix (Fin 2) (Fin 2) F) i j)
    h1

theorem range_slIncl : (slIncl σ).range = slFixed σ := by
  ext X
  constructor
  · rintro ⟨M, rfl⟩
    show Matrix.GeneralLinearGroup.map σ.toRingHom ((slIncl σ M : SL2 F) : GL (Fin 2) F) =
      ((slIncl σ M : SL2 F) : GL (Fin 2) F)
    apply Matrix.GeneralLinearGroup.ext
    intro i j
    rw [Matrix.GeneralLinearGroup.map_apply]
    exact fixedField_apply σ (M i j)
  · intro hX
    obtain ⟨S, hS⟩ := (specialLinearGroupEquivStatedSL 2 F).surjective X
    have hX' : Matrix.GeneralLinearGroup.map σ.toRingHom ((X : SL2 F) : GL (Fin 2) F) =
        ((X : SL2 F) : GL (Fin 2) F) := hX
    have hfix : ∀ i j, σ (S i j) = S i j := by
      intro i j
      have h1 := congrArg (fun G : GL (Fin 2) F => (G : Matrix (Fin 2) (Fin 2) F) i j) hX'
      simpa [← hS, specialLinearGroupEquivStatedSL_coe, Matrix.GeneralLinearGroup.map_apply]
        using h1
    obtain ⟨M, hM⟩ := exists_specialLinear_map_eq σ S hfix
    refine ⟨M, ?_⟩
    show (specialLinearGroupEquivStatedSL 2 F)
      (Matrix.SpecialLinearGroup.map (fixedField σ).subtype M) = X
    rw [hM, hS]

theorem hasSL2Model_slFixed [Finite F] :
    HasSL2Model ↥(slFixed σ) (fun q₀ => q₀ ^ orderOf σ = Nat.card F) := by
  refine ⟨↥(fixedField σ), inferInstance, inferInstance, fixedField_card_pow σ, ⟨?_⟩⟩
  exact (MulEquiv.subgroupCongr (range_slIncl σ)).symm.trans
    ((MonoidHom.ofInjective (slIncl_injective σ)).symm.trans
      (specialLinearGroupEquivStatedSL 2 (fixedField σ)))

end SLIncl

section PSLIncl

variable {F : Type} [Field F] (σ : F ≃+* F)

@[expose] noncomputable def pslIncl : PSL2 (fixedField σ) →* PSL2 F :=
  QuotientGroup.map _ _ (Matrix.SpecialLinearGroup.map (fixedField σ).subtype) (by
    intro z hz
    rw [Subgroup.mem_comap]
    obtain ⟨r, hr, hz'⟩ := Matrix.SpecialLinearGroup.mem_center_iff.mp hz
    refine Matrix.SpecialLinearGroup.mem_center_iff.mpr ⟨(r : F), ?_, ?_⟩
    · have := congrArg (fixedField σ).subtype hr
      simpa using this
    · ext i j
      have := congrArg (fun M : Matrix (Fin 2) (Fin 2) (fixedField σ) => (M i j : F)) hz'
      by_cases hij : i = j
      · subst hij
        simpa [Matrix.scalar_apply] using this
      · simpa [Matrix.scalar_apply, hij] using this)

theorem pslIncl_mk (S : Matrix.SpecialLinearGroup (Fin 2) (fixedField σ)) :
    pslIncl σ (QuotientGroup.mk S) =
      QuotientGroup.mk (Matrix.SpecialLinearGroup.map (fixedField σ).subtype S) := rfl

theorem toPGL_pslIncl (x : PSL2 (fixedField σ)) :
    Matrix.ProjectiveSpecialLinearGroup.toPGL (pslIncl σ x) =
      pgl2Incl σ (Matrix.ProjectiveSpecialLinearGroup.toPGL x) := by
  induction x using QuotientGroup.induction_on with
  | H S =>
    rw [pslIncl_mk, Matrix.ProjectiveSpecialLinearGroup.toPGL_mk,
      Matrix.ProjectiveSpecialLinearGroup.toPGL_mk, pgl2Incl_mk]
    congr 1
    exact Matrix.GeneralLinearGroup.ext fun i j => rfl

theorem pslIncl_injective : Function.Injective (pslIncl σ) := by
  intro x y h
  apply Matrix.ProjectiveSpecialLinearGroup.toPGL_injective
  apply pgl2Incl_injective σ
  rw [← toPGL_pslIncl, ← toPGL_pslIncl, h]

theorem sq_pow_apply_of_apply_eq_neg (y : F) (h1 : σ y = -y) (k : ℕ) :
    (σ ^ k) y = (-1) ^ k * y := by
  induction k with
  | zero => simp
  | succ k ih =>
    rw [pow_succ', RingAut.mul_apply, ih, map_mul, map_pow, map_neg, map_one, h1]
    ring

theorem apply_eq_of_eq_mul_of_odd (hodd : Odd (orderOf σ)) (y c : F) (hc : c * c = 1)
    (h : y = σ y * c) : σ y = y := by
  rcases mul_self_eq_one_iff.mp hc with hc1 | hc1
  · rw [hc1, mul_one] at h
    exact h.symm
  · rw [hc1, mul_neg_one] at h
    have h1 : σ y = -y := by linear_combination h
    have h2 := sq_pow_apply_of_apply_eq_neg σ y h1 (orderOf σ)
    rw [pow_orderOf_eq_one, RingAut.one_apply, hodd.neg_one_pow] at h2
    have h3 : y = -y := by simpa using h2
    rw [h1]
    exact h3.symm

theorem exists_map_eq_of_psl_fixed (hodd : Odd (orderOf σ))
    (Y : Matrix.SpecialLinearGroup (Fin 2) F)
    (hy : (QuotientGroup.mk (Matrix.SpecialLinearGroup.map σ.toRingHom Y) : PSL2 F) =
      QuotientGroup.mk Y) :
    ∃ M : Matrix.SpecialLinearGroup (Fin 2) (fixedField σ),
      Matrix.SpecialLinearGroup.map (fixedField σ).subtype M = Y := by
  rw [QuotientGroup.eq] at hy
  obtain ⟨c, hc2, hc⟩ := Matrix.SpecialLinearGroup.mem_center_iff.mp hy
  have hY : (Y : Matrix (Fin 2) (Fin 2) F) =
      (Matrix.SpecialLinearGroup.map σ.toRingHom Y : Matrix (Fin 2) (Fin 2) F) *
        Matrix.scalar (Fin 2) c := by
    rw [hc, ← Matrix.SpecialLinearGroup.coe_mul, mul_inv_cancel_left]
  have hij : ∀ i j, Y i j = σ (Y i j) * c := by
    intro i j
    have := congrArg (fun M : Matrix (Fin 2) (Fin 2) F => M i j) hY
    simpa [Matrix.scalar_apply, Matrix.mul_diagonal] using this
  have hc' : c * c = 1 := by simpa [sq] using hc2
  exact exists_specialLinear_map_eq σ Y
    (fun i j => apply_eq_of_eq_mul_of_odd σ hodd _ c hc' (hij i j))

theorem mem_range_pslIncl_iff (hodd : Odd (orderOf σ)) (y : PSL2 F) :
    y ∈ (pslIncl σ).range ↔ psl2FieldAut F σ y = y := by
  constructor
  · rintro ⟨x, rfl⟩
    induction x using QuotientGroup.induction_on with
    | H S =>
      rw [pslIncl_mk, psl2FieldAut_apply]
      change psl2RingEquiv σ (QuotientGroup.mk' (Subgroup.center _) _) =
        QuotientGroup.mk' (Subgroup.center _) _
      rw [psl2RingEquiv_mk]
      congr 1
      refine Matrix.SpecialLinearGroup.ext _ _ fun i j => ?_
      exact fixedField_apply σ (S i j)
  · intro hy
    obtain ⟨Y, rfl⟩ := QuotientGroup.mk_surjective y
    have h1 : psl2FieldAut F σ (QuotientGroup.mk Y : PSL2 F) =
        QuotientGroup.mk (Matrix.SpecialLinearGroup.map σ.toRingHom Y) := by
      rw [psl2FieldAut_apply]
      exact psl2RingEquiv_mk σ Y
    have hy' : (QuotientGroup.mk (Matrix.SpecialLinearGroup.map σ.toRingHom Y) : PSL2 F) =
        QuotientGroup.mk Y := h1.symm.trans hy
    obtain ⟨M, hM⟩ := exists_map_eq_of_psl_fixed σ hodd Y hy'
    refine ⟨QuotientGroup.mk M, ?_⟩
    rw [pslIncl_mk, hM]

end PSLIncl

end CFSG.GH74.GLS.IVK
