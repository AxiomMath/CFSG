module

public import CFSG.GH74.GLS.Stage2.Signalizer.Ivk8P4S55L2Out
public import CFSG.GH74.GLS.Stage2.Signalizer.Ivk8P4S55L2Par

public section

namespace CFSG.GH74.GLS.Stage2.Signalizer.Ivk8

open Subgroup CFSG CFSG.GorensteinWalter CFSG.ComponentClassification
  CFSG.ComponentClassification.CatalogueSchreierLinearTwo

section Unipotent

variable {F : Type} [Field F]

@[expose] def uniSLt (t : F) : Matrix.SpecialLinearGroup (Fin 2) F :=
  ⟨!![1, t; 0, 1], by simp [Matrix.det_fin_two_of]⟩

@[expose] def uniPSL (t : F) : PSL2 F :=
  QuotientGroup.mk' (Subgroup.center (Matrix.SpecialLinearGroup (Fin 2) F)) (uniSLt t)

theorem uniSLt_mul (s t : F) : uniSLt s * uniSLt t = uniSLt (s + t) := by
  apply Subtype.ext
  simp only [Matrix.SpecialLinearGroup.coe_mul]
  ext i j
  fin_cases i <;> fin_cases j <;> simp [uniSLt, Matrix.mul_apply, Fin.sum_univ_two]
  ring

theorem uniPSL_mul (s t : F) : uniPSL s * uniPSL t = uniPSL (s + t) := by
  simp only [uniPSL, ← map_mul, uniSLt_mul]

theorem uniPSL_zero : uniPSL (0 : F) = 1 := by
  have : uniSLt (0 : F) = 1 := by
    apply Subtype.ext
    ext i j
    fin_cases i <;> fin_cases j <;> simp [uniSLt]
  simp [uniPSL, this]

theorem uniPSL_ne_one : uniPSL (1 : F) ≠ 1 := by
  intro h
  have h1 : uniSLt (1 : F) ∈ Subgroup.center (Matrix.SpecialLinearGroup (Fin 2) F) :=
    (QuotientGroup.eq_one_iff _).mp h
  obtain ⟨c, -, hc⟩ := Matrix.SpecialLinearGroup.mem_center_iff.mp h1
  have h2 := congrFun (congrFun hc 0) 1
  simp [uniSLt] at h2

theorem uniPSL_pow_char {r : ℕ} [CharP F r] (t : F) : uniPSL t ^ r = 1 := by
  have : ∀ n : ℕ, uniPSL t ^ n = uniPSL ((n : F) * t) := by
    intro n
    induction n with
    | zero => simp [uniPSL_zero]
    | succ n ih => rw [pow_succ, ih, uniPSL_mul]; congr 1; push_cast; ring
  rw [this, CharP.cast_eq_zero, zero_mul, uniPSL_zero]

theorem psl2RingEquiv_uniPSL (σ : F ≃+* F) (t : F) :
    psl2RingEquiv σ (uniPSL t) = uniPSL (σ t) := by
  change psl2RingEquiv σ (QuotientGroup.mk' (Subgroup.center _) (uniSLt t)) = _
  rw [psl2RingEquiv_mk]
  change QuotientGroup.mk' (Subgroup.center _) _ = QuotientGroup.mk' (Subgroup.center _) (uniSLt _)
  congr 1
  apply Subtype.ext
  show σ.toRingHom.mapMatrix (!![1, t; 0, 1]) = !![1, σ t; 0, 1]
  ext i j
  fin_cases i <;> fin_cases j <;> simp [RingHom.mapMatrix_apply]

@[expose] def uniHomPSL : Multiplicative F →* PSL2 F where
  toFun t := uniPSL t.toAdd
  map_one' := uniPSL_zero
  map_mul' s t := (uniPSL_mul s.toAdd t.toAdd).symm

end Unipotent

section Inner

variable {Y : Type} [Group Y]

theorem l2_inner_of_no_invariant {r p f : ℕ} (hr : r.Prime) (hr2 : r ≠ 2) (hp : p.Prime)
    (hp2 : p ≠ 2) [Finite Y] (h : Blueprint.LieModel Y .PSL 2 r f) {b : MulAut Y} (hb1 : b ≠ 1)
    (hbp : b ^ p = 1)
    (hno : ∀ E : Subgroup Y, IsPGroup r ↥E → (∀ x ∈ E, b x ∈ E) → E = ⊥) :
    b ∈ (MulAut.conj : Y →* MulAut Y).range := by
  classical
  by_contra hnot
  obtain ⟨-, hf, -, -, F, _, _, hcard, ⟨e⟩⟩ := AutL2Facts.lieModel_psl2_data h
  have : Fact r.Prime := ⟨hr⟩
  have : Fact p.Prime := ⟨hp⟩
  have : CharP F r := charP_of_card_eq_pow hr hf hcard
  have hgord : orderOf (AutL2Facts.autEquiv e b) = p := by
    rw [MulEquiv.orderOf_eq]
    exact orderOf_eq_prime hbp hb1
  obtain ⟨-, x, σ, -, hconj, -⟩ :=
    outer_conj_fieldAut hr hr2 hp hp2 hf hcard hgord (autEquiv_not_psl e hnot)
  let Ubar : Subgroup (PSL2 F) := (uniHomPSL (F := F)).range
  let E' : Subgroup (PSL2 F) := Ubar.map (pglAction F x).toMonoidHom
  let E : Subgroup Y := E'.map e.symm.toMonoidHom
  have hsl : ∀ y' : PSL2 F, e (b (e.symm y')) =
      semilinearAction F (AutL2Facts.autEquiv e b) y' := by
    intro y'
    have := AutL2Facts.semilinearAction_autEquiv_apply e b (e.symm y')
    rw [MulEquiv.apply_symm_apply] at this
    exact this.symm
  have hUbar : ∀ u ∈ Ubar, psl2RingEquiv σ u ∈ Ubar := by
    rintro _ ⟨t, rfl⟩
    exact ⟨Multiplicative.ofAdd (σ t.toAdd), (psl2RingEquiv_uniPSL σ _).symm⟩
  have hEinv : ∀ y ∈ E, b y ∈ E := by
    rintro _ ⟨_, ⟨u, hu, rfl⟩, rfl⟩
    refine ⟨_, ⟨psl2RingEquiv σ u, hUbar u hu, rfl⟩, ?_⟩
    apply e.injective
    simp only [MulEquiv.coe_toMonoidHom, MulEquiv.apply_symm_apply]
    rw [hsl, hconj]
    simp [map_mul, map_inv, MulAut.mul_apply, MulAut.inv_apply, psl2FieldAut_apply]
  have hUp : IsPGroup r ↥Ubar := by
    rintro ⟨_, t, rfl⟩
    exact ⟨1, Subtype.ext (by
      simpa [uniHomPSL] using uniPSL_pow_char (r := r) (F := F) t.toAdd)⟩
  have hEp : IsPGroup r ↥E := (hUp.map _).map _
  have hEbot := hno E hEp hEinv
  have hU1 : uniPSL (1 : F) ∈ Ubar := ⟨Multiplicative.ofAdd 1, rfl⟩
  have hUbot : Ubar = ⊥ := by
    have h1 : E' = ⊥ :=
      (Subgroup.map_eq_bot_iff_of_injective E' e.symm.injective).mp hEbot
    exact (Subgroup.map_eq_bot_iff_of_injective Ubar (pglAction F x).injective).mp h1
  rw [hUbot, Subgroup.mem_bot] at hU1
  exact uniPSL_ne_one hU1

end Inner

end CFSG.GH74.GLS.Stage2.Signalizer.Ivk8
