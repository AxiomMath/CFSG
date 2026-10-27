module

public import CFSG.HardMathSupport.Solomon.Coordinator.SeitzOuterCube.U3Heis.Cube
public import CFSG.HardMathSupport.Solomon.Coordinator.SeitzOuterCube.U3Heis.Matrices

public section

namespace CFSG.HardMathSupport.Solomon.Coordinator.SeitzOuterCube.U3Heis

open Matrix CFSG.LocalAnalysis.ComponentInitial CFSG.RankThree.PartTwo.KFacts
open CFSG.ClassicalGroups.UnitaryFlag
open CFSG.LocalAnalysis.ComponentInitial.UnitaryHigher (glAut coe_glAut)
open CFSG.HardMathSupport.Malle.Coordinator.SeitzA2Three
open CFSG.HardMathSupport.Malle.Coordinator.CoverThreeNoInner (monomGL diagGL)

variable {ℓ f : ℕ} {F : Type} [Field F] (h : UnitaryFieldData ℓ f F)

@[expose] noncomputable def suOf (M : Matrix (Fin 3) (Fin 3) F) (hU : (M.map h.bar)ᵀ * M = 1)
    (hdet : M.det = 1) : unitarySU ℓ f F 3 :=
  ⟨⟨M, (M.map h.bar)ᵀ, mul_eq_one_comm.1 hU, hU⟩, (mem_unitarySU_iff h).2 ⟨hdet, hU⟩⟩

theorem coe_suOf (M : Matrix (Fin 3) (Fin 3) F) (hU : (M.map h.bar)ᵀ * M = 1) (hdet : M.det = 1) :
    (((suOf h M hU hdet : unitarySU ℓ f F 3) : GL (Fin 3) F) : Matrix (Fin 3) (Fin 3) F) = M :=
  rfl

@[expose] def liftU (S : Set (unitaryPSU h 3)) : Subgroup (GL (Fin 3) F) :=
  ((Subgroup.closure S).comap (unitaryProj h 3)).map (unitarySU ℓ f F 3).subtype

variable {h}

theorem mem_liftU_of {S : Set (unitaryPSU h 3)} {g : unitarySU ℓ f F 3}
    (hg : (g : unitaryPSU h 3) ∈ S) : (g : GL (Fin 3) F) ∈ liftU h S :=
  ⟨g, Subgroup.subset_closure hg, rfl⟩

theorem liftU_le (S : Set (unitaryPSU h 3)) : liftU h S ≤ unitarySU ℓ f F 3 := by
  rintro _ ⟨g, -, rfl⟩
  exact g.2

theorem closure_eq_top_of_le_liftU {S : Set (unitaryPSU h 3)}
    (hle : unitarySU ℓ f F 3 ≤ liftU h S) : Subgroup.closure S = ⊤ := by
  rw [eq_top_iff]
  intro y _
  obtain ⟨g, rfl⟩ := unitaryProj_surjective h 3 y
  obtain ⟨g', hg', hgg⟩ := hle g.2
  have : g' = g := Subtype.ext hgg
  subst this
  exact hg'

theorem mk_eq_of_eq_scalar_mul {g g' : unitarySU ℓ f F 3} {c : Fˣ} (hc3 : c ^ 3 = 1)
    (hcn : h.bar (c : F) * c = 1)
    (hgg : (g' : GL (Fin 3) F) = Matrix.GeneralLinearGroup.scalar (Fin 3) c * g) :
    (g' : unitaryPSU h 3) = (g : unitaryPSU h 3) := by
  rw [QuotientGroup.eq]
  refine ⟨c⁻¹, ?_, ?_, ?_⟩
  · rw [UnitaryFieldData.norm, Units.val_inv_eq_inv_val, map_inv₀, ← mul_inv, mul_comm, hcn,
      inv_one]
  · rw [inv_pow, hc3, inv_one]
  · rw [Subgroup.coe_mul, Subgroup.coe_inv, hgg, _root_.mul_inv_rev, ← map_inv, mul_assoc,
      ← (commute_scalar c⁻¹ (g : GL (Fin 3) F)).eq, ← mul_assoc, inv_mul_cancel, one_mul]

theorem psuField_mk_of {σ : F ≃+* F} {g : unitarySU ℓ f F 3} {c : Fˣ} (hc3 : c ^ 3 = 1)
    (hcn : h.bar (c : F) * c = 1)
    (hg : glAut σ (g : GL (Fin 3) F) = Matrix.GeneralLinearGroup.scalar (Fin 3) c * g) :
    psuField h σ (g : unitaryPSU h 3) = g := by
  rw [psuField_mk]
  exact mk_eq_of_eq_scalar_mul hc3 hcn (by rw [coe_suField]; exact hg)

theorem psuConj_mk_of {A : unitaryIsom3 h} {g : unitarySU ℓ f F 3} {c : Fˣ} (hc3 : c ^ 3 = 1)
    (hcn : h.bar (c : F) * c = 1)
    (hg : (A : GL (Fin 3) F) * g = Matrix.GeneralLinearGroup.scalar (Fin 3) c * g * A) :
    psuConj h A (g : unitaryPSU h 3) = g := by
  rw [psuConj_mk]
  refine mk_eq_of_eq_scalar_mul hc3 hcn ?_
  rw [coe_suConj, Subgroup.coe_inv, hg, mul_inv_cancel_right]

theorem one_cube_norm : h.bar ((1 : Fˣ) : F) * ((1 : Fˣ) : F) = 1 := by
  rw [Units.val_one, map_one, one_mul]

theorem unitary_diagonal {t : Fin 3 → F} (ht : ∀ i, h.bar (t i) * t i = 1) :
    ((diagonal t).map h.bar)ᵀ * diagonal t = 1 := by
  rw [diagonal_map (map_zero h.bar), diagonal_transpose, diagonal_mul_diagonal, ← diagonal_one]
  congr 1
  funext i
  exact ht i

theorem det_diagonal_three (t : Fin 3 → F) : (diagonal t).det = t 0 * t 1 * t 2 := by
  rw [det_diagonal, Fin.prod_univ_three]

@[expose] noncomputable def diagSU (t : Fin 3 → F) (ht : ∀ i, h.bar (t i) * t i = 1)
    (hd : t 0 * t 1 * t 2 = 1) : unitarySU ℓ f F 3 :=
  suOf h (diagonal t) (unitary_diagonal ht) (by rw [det_diagonal_three]; exact hd)

theorem coe_diagSU (t : Fin 3 → F) (ht : ∀ i, h.bar (t i) * t i = 1) (hd : t 0 * t 1 * t 2 = 1) :
    (((diagSU t ht hd : unitarySU ℓ f F 3) : GL (Fin 3) F) : Matrix (Fin 3) (Fin 3) F) =
      diagonal t := rfl

theorem permP_mul_diagonal (t : Fin 3 → F) :
    (permP : Matrix (Fin 3) (Fin 3) F) * diagonal t = diagonal ![t 2, t 0, t 1] * permP := by
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [permP, Matrix.mul_apply, Fin.sum_univ_three, diagonal_apply]

theorem monomGL_one_val : ((monomGL F 1 : GL (Fin 3) F) : Matrix (Fin 3) (Fin 3) F) = permP := by
  ext i j
  fin_cases i <;> fin_cases j <;> simp [monomGL, permP]

theorem coe_scalar_mul (c : Fˣ) (g : GL (Fin 3) F) :
    ((Matrix.GeneralLinearGroup.scalar (Fin 3) c * g : GL (Fin 3) F) : Matrix (Fin 3) (Fin 3) F) =
      (c : F) • ((g : GL (Fin 3) F) : Matrix (Fin 3) (Fin 3) F) := by
  rw [Units.val_mul, Matrix.GeneralLinearGroup.coe_scalar, smul_eq_diagonal_mul]
  rfl

section Members

variable [Finite F] {σ : F ≃+* F} {ω : Fˣ} {D X : unitaryIsom3 h}

theorem psuField_mk_of' {g : unitarySU ℓ f F 3} {c : Fˣ} (hc3 : c ^ 3 = 1)
    (hcn : h.bar (c : F) * c = 1)
    (hgσ : ((g : GL (Fin 3) F) : Matrix (Fin 3) (Fin 3) F).map σ =
      (c : F) • ((g : GL (Fin 3) F) : Matrix (Fin 3) (Fin 3) F)) :
    psuField h σ (g : unitaryPSU h 3) = g := by
  refine psuField_mk_of hc3 hcn ?_
  apply Units.ext
  rw [coe_glAut, coe_scalar_mul, hgσ]

theorem mem_liftU_of_fU_cX (hh : HeisHypU h σ 1 ω D X) {g : unitarySU ℓ f F 3} {c : Fˣ}
    (hc3 : c ^ 3 = 1) (hcn : h.bar (c : F) * c = 1)
    (hgσ : ((g : GL (Fin 3) F) : Matrix (Fin 3) (Fin 3) F).map σ =
      (c : F) • ((g : GL (Fin 3) F) : Matrix (Fin 3) (Fin 3) F))
    (hgX : permP * ((g : GL (Fin 3) F) : Matrix (Fin 3) (Fin 3) F) =
      ((g : GL (Fin 3) F) : Matrix (Fin 3) (Fin 3) F) * permP) :
    (g : GL (Fin 3) F) ∈ liftU h (hyperFixU h σ D X) := by
  refine mem_liftU_of (mem_hyperFixU_of_fU_cX hh (psuField_mk_of' hc3 hcn hgσ) ?_)
  refine psuConj_mk_of (c := 1) (one_pow 3) one_cube_norm ?_
  rw [map_one, one_mul]
  apply Units.ext
  rw [Units.val_mul, Units.val_mul, hh.hX, monomGL_one_val, hgX]

theorem mem_liftU_of_fU_cD (hh : HeisHypU h σ 1 ω D X) {g : unitarySU ℓ f F 3} {c : Fˣ}
    (hc3 : c ^ 3 = 1) (hcn : h.bar (c : F) * c = 1)
    (hgσ : ((g : GL (Fin 3) F) : Matrix (Fin 3) (Fin 3) F).map σ =
      (c : F) • ((g : GL (Fin 3) F) : Matrix (Fin 3) (Fin 3) F))
    {t : Fin 3 → F} (hgt : ((g : GL (Fin 3) F) : Matrix (Fin 3) (Fin 3) F) =
      diagonal t) :
    (g : GL (Fin 3) F) ∈ liftU h (hyperFixU h σ D X) := by
  refine mem_liftU_of (mem_hyperFixU_of_fU_cD hh (psuField_mk_of' hc3 hcn hgσ) ?_)
  refine psuConj_mk_of (c := 1) (one_pow 3) one_cube_norm ?_
  rw [map_one, one_mul]
  apply Units.ext
  rw [Units.val_mul, Units.val_mul, hh.hD, hgt]
  change diagonal ![((1 : Fˣ) : F), (ω : F), ((ω ^ 2 : Fˣ) : F)] * diagonal t =
    diagonal t * diagonal ![((1 : Fˣ) : F), (ω : F), ((ω ^ 2 : Fˣ) : F)]
  rw [diagonal_mul_diagonal, diagonal_mul_diagonal]
  congr 1
  funext i
  exact mul_comm _ _

theorem coe_suConj_X_diag (hh : HeisHypU h σ 1 ω D X) {g : unitarySU ℓ f F 3} {t : Fin 3 → F}
    (hgt : ((g : GL (Fin 3) F) : Matrix (Fin 3) (Fin 3) F) = diagonal t) :
    (((suConj h X g : unitarySU ℓ f F 3) : GL (Fin 3) F) : Matrix (Fin 3) (Fin 3) F) =
      diagonal ![t 2, t 0, t 1] := by
  have hXg : ((X : GL (Fin 3) F) : Matrix (Fin 3) (Fin 3) F) *
      ((g : GL (Fin 3) F) : Matrix (Fin 3) (Fin 3) F) =
      diagonal ![t 2, t 0, t 1] * ((X : GL (Fin 3) F) : Matrix (Fin 3) (Fin 3) F) := by
    rw [hh.hX, monomGL_one_val, hgt, permP_mul_diagonal]
  rw [coe_suConj, Units.val_mul, Units.val_mul, hXg, Matrix.mul_assoc, ← Units.val_mul,
    Subgroup.coe_inv, mul_inv_cancel, Units.val_one, Matrix.mul_one]

theorem σ_three (hh : HeisHypU h σ 1 ω D X) (a : F) : σ (σ (σ a)) = a := by
  have := congrArg (fun τ : F ≃+* F => τ a) hh.pow3
  simpa [pow_succ] using this

theorem mem_liftU_twist₁ (hh : HeisHypU h σ 1 ω D X) {g : unitarySU ℓ f F 3} {a : F}
    (hgt : ((g : GL (Fin 3) F) : Matrix (Fin 3) (Fin 3) F) = diagonal ![a, σ a, σ (σ a)]) :
    (g : GL (Fin 3) F) ∈ liftU h (hyperFixU h σ D X) := by
  refine mem_liftU_of (mem_hyperFixU_of_cD_fUcXpow hh (m := 1) (Or.inl rfl) ?_ ?_)
  · refine psuConj_mk_of (c := 1) (one_pow 3) one_cube_norm ?_
    rw [map_one, one_mul]
    apply Units.ext
    rw [Units.val_mul, Units.val_mul, hh.hD, hgt]
    change diagonal ![((1 : Fˣ) : F), (ω : F), ((ω ^ 2 : Fˣ) : F)] * diagonal _ =
      diagonal _ * diagonal ![((1 : Fˣ) : F), (ω : F), ((ω ^ 2 : Fˣ) : F)]
    rw [diagonal_mul_diagonal, diagonal_mul_diagonal]
    congr 1
    funext i
    exact mul_comm _ _
  · rw [pow_one, MulAut.mul_apply, psuConj_mk, psuField_mk]
    refine mk_eq_of_eq_scalar_mul (c := 1) (one_pow 3) one_cube_norm ?_
    rw [map_one, one_mul]
    apply Units.ext
    rw [coe_suField, coe_glAut, coe_suConj_X_diag hh hgt, hgt, diagonal_map (map_zero σ)]
    congr 1
    funext i
    fin_cases i <;> simp [σ_three hh]

theorem mem_liftU_twist₂ (hh : HeisHypU h σ 1 ω D X) {g : unitarySU ℓ f F 3} {a : F}
    (hgt : ((g : GL (Fin 3) F) : Matrix (Fin 3) (Fin 3) F) = diagonal ![a, σ (σ a), σ a]) :
    (g : GL (Fin 3) F) ∈ liftU h (hyperFixU h σ D X) := by
  refine mem_liftU_of (mem_hyperFixU_of_cD_fUcXpow hh (m := 2) (Or.inr rfl) ?_ ?_)
  · refine psuConj_mk_of (c := 1) (one_pow 3) one_cube_norm ?_
    rw [map_one, one_mul]
    apply Units.ext
    rw [Units.val_mul, Units.val_mul, hh.hD, hgt]
    change diagonal ![((1 : Fˣ) : F), (ω : F), ((ω ^ 2 : Fˣ) : F)] * diagonal _ =
      diagonal _ * diagonal ![((1 : Fˣ) : F), (ω : F), ((ω ^ 2 : Fˣ) : F)]
    rw [diagonal_mul_diagonal, diagonal_mul_diagonal]
    congr 1
    funext i
    exact mul_comm _ _
  · rw [pow_two, MulAut.mul_apply, MulAut.mul_apply, psuConj_mk, psuConj_mk, psuField_mk]
    refine mk_eq_of_eq_scalar_mul (c := 1) (one_pow 3) one_cube_norm ?_
    rw [map_one, one_mul]
    apply Units.ext
    rw [coe_suField, coe_glAut, coe_suConj_X_diag hh (coe_suConj_X_diag hh hgt), hgt,
      diagonal_map (map_zero σ)]
    congr 1
    funext i
    fin_cases i <;> simp [σ_three hh]

theorem X_mem_unitarySU (hh : HeisHypU h σ 1 ω D X) : (X : GL (Fin 3) F) ∈ unitarySU ℓ f F 3 := by
  refine (mem_unitarySU_iff h).2 ⟨?_, mem_unitaryIsom3.1 X.2⟩
  rw [hh.hX, monomGL_one_val, permP, Matrix.det_fin_three]
  simp

theorem mem_liftU_X (hh : HeisHypU h σ 1 ω D X) :
    (X : GL (Fin 3) F) ∈ liftU h (hyperFixU h σ D X) := by
  have := mem_liftU_of_fU_cX hh (g := ⟨X, X_mem_unitarySU hh⟩) (c := 1) (one_pow 3)
    one_cube_norm ?_ ?_
  · exact this
  · change ((X : GL (Fin 3) F) : Matrix (Fin 3) (Fin 3) F).map σ = _
    rw [Units.val_one, one_smul, hh.hX, monomGL_one_val]
    ext i j
    fin_cases i <;> fin_cases j <;> simp [permP]
  · change permP * ((X : GL (Fin 3) F) : Matrix (Fin 3) (Fin 3) F) = _ * permP
    rw [hh.hX, monomGL_one_val]

end Members

end CFSG.HardMathSupport.Solomon.Coordinator.SeitzOuterCube.U3Heis
