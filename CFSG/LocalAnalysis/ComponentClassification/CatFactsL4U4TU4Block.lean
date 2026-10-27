module

public import CFSG.Assembly.ComponentTypeDefs
public import CFSG.LocalAnalysis.ComponentClassification.CatFactsL4U4StabU
public import CFSG.LocalAnalysis.ComponentClassification.CatFactsL4U4TBlocks

public section

namespace CFSG.ComponentClassification.CatFactsL4U4

namespace StabU

open Matrix CFSG.LocalAnalysis.ComponentInitial CFSG.LocalAnalysis.ComponentInitial.UnitaryHigher
  UnitaryOut UnitaryConj HBlocks ClassicalGroups.UnitaryFlag CFSG.Assembly.LowTwoRank TBlocks
  Subgroup
open scoped commutatorElement

variable {p f : ℕ} {K : Type} [Field K] (h : UnitaryFieldData p f K)

omit [Field K] in
theorem transpose_mul_jj_mul {L : Type} [Field L] (a : Matrix (Fin 2) (Fin 2) L) :
    aᵀ * jj * a = a.det • jj := by
  rw [Matrix.det_fin_two]
  ext i j
  fin_cases i <;> fin_cases j <;> simp [jj, Matrix.mul_apply, Fin.sum_univ_two] <;> ring

@[expose] noncomputable def bdK (x : SpecialLinearGroup (Fin 2) h.fixedField ×
    SpecialLinearGroup (Fin 2) h.fixedField) : Matrix (Fin 4) (Fin 4) K :=
  bd ((x.1 : Matrix (Fin 2) (Fin 2) h.fixedField).map h.fixedField.subtype)
    ((x.2 : Matrix (Fin 2) (Fin 2) h.fixedField).map h.fixedField.subtype)

theorem det_bdK (x : SpecialLinearGroup (Fin 2) h.fixedField ×
    SpecialLinearGroup (Fin 2) h.fixedField) : (bdK h x).det = 1 := by
  rw [bdK, det_bd]
  have e : ∀ y : SpecialLinearGroup (Fin 2) h.fixedField,
      ((y : Matrix (Fin 2) (Fin 2) h.fixedField).map h.fixedField.subtype).det = 1 := fun y => by
    rw [show ((y : Matrix (Fin 2) (Fin 2) h.fixedField).map h.fixedField.subtype) =
      h.fixedField.subtype.mapMatrix (y : Matrix (Fin 2) (Fin 2) h.fixedField) from rfl,
      ← RingHom.map_det, y.2, map_one]
  rw [e, e, mul_one]

theorem bdK_mul (x y : SpecialLinearGroup (Fin 2) h.fixedField ×
    SpecialLinearGroup (Fin 2) h.fixedField) : bdK h (x * y) = bdK h x * bdK h y := by
  rw [bdK, bdK, bdK, bd_mul, Prod.fst_mul, Prod.snd_mul, Matrix.SpecialLinearGroup.coe_mul,
    Matrix.SpecialLinearGroup.coe_mul, Matrix.map_mul, Matrix.map_mul]

theorem bdK_one : bdK h (1 : SpecialLinearGroup (Fin 2) h.fixedField ×
    SpecialLinearGroup (Fin 2) h.fixedField) = 1 := by
  rw [bdK, Prod.fst_one, Prod.snd_one, Matrix.SpecialLinearGroup.coe_one,
    Matrix.map_one _ (map_zero _) (map_one _), bd_one]

theorem map_bar_bdK (x : SpecialLinearGroup (Fin 2) h.fixedField ×
    SpecialLinearGroup (Fin 2) h.fixedField) : (bdK h x).map h.bar = bdK h x := by
  rw [bdK, map_bd, Matrix.map_map, Matrix.map_map]
  have e : (h.bar ∘ h.fixedField.subtype) = h.fixedField.subtype := by
    funext c
    exact h.mem_fixedField.1 c.2
  rw [e]

omit [Field K] in
theorem transpose_bd_bJ {L : Type} [Field L] {a b : Matrix (Fin 2) (Fin 2) L} (ha : a.det = 1)
    (hb : b.det = 1) : (bd a b)ᵀ * bJ 1 1 * bd a b = bJ 1 1 := by
  have e : bJ (1 : L) 1 = bd jj jj := by rw [← bd_eq_bJ, one_smul]
  rw [e, transpose_bd, bd_mul, bd_mul, transpose_mul_jj_mul, transpose_mul_jj_mul, ha, hb,
    one_smul]

theorem det_map_fixed (y : SpecialLinearGroup (Fin 2) h.fixedField) :
    ((y : Matrix (Fin 2) (Fin 2) h.fixedField).map h.fixedField.subtype).det = 1 := by
  rw [show ((y : Matrix (Fin 2) (Fin 2) h.fixedField).map h.fixedField.subtype) =
    h.fixedField.subtype.mapMatrix (y : Matrix (Fin 2) (Fin 2) h.fixedField) from rfl,
    ← RingHom.map_det, y.2, map_one]

theorem transpose_bdK_bJ (x : SpecialLinearGroup (Fin 2) h.fixedField ×
    SpecialLinearGroup (Fin 2) h.fixedField) : (bdK h x)ᵀ * bJ 1 1 * bdK h x = bJ 1 1 :=
  transpose_bd_bJ (det_map_fixed h x.1) (det_map_fixed h x.2)

@[expose] noncomputable def glBd : SpecialLinearGroup (Fin 2) h.fixedField ×
    SpecialLinearGroup (Fin 2) h.fixedField →* GL (Fin 4) K where
  toFun x := toGL (bdK h x) (det_bdK h x)
  map_one' := Units.ext (by
    change bdK h 1 = 1
    rw [bdK_one])
  map_mul' x y := Units.ext (by
    change bdK h (x * y) = bdK h x * bdK h y
    rw [bdK_mul])

theorem coe_glBd (x : SpecialLinearGroup (Fin 2) h.fixedField ×
    SpecialLinearGroup (Fin 2) h.fixedField) :
    ((glBd h x : GL (Fin 4) K) : Matrix (Fin 4) (Fin 4) K) = bdK h x := rfl

include h in
theorem conj_glBd_mem {R : GL (Fin 4) K} {t : K}
    (hR : uStar h (R : Matrix (Fin 4) (Fin 4) K) * (R : Matrix (Fin 4) (Fin 4) K) = t • bJ 1 1)
    (x : SpecialLinearGroup (Fin 2) h.fixedField × SpecialLinearGroup (Fin 2) h.fixedField) :
    MulAut.conj R (glBd h x) ∈ unitarySU p f K 4 := by
  have hRR : (R : Matrix (Fin 4) (Fin 4) K) * (↑R⁻¹ : Matrix (Fin 4) (Fin 4) K) = 1 := by
    rw [← Units.val_mul, mul_inv_cancel, Units.val_one]
  rw [mem_unitarySU_iff h, MulAut.conj_apply, Units.val_mul, Units.val_mul, coe_glBd]
  refine ⟨?_, ?_⟩
  · rw [det_mul, det_mul, det_bdK, mul_one, ← det_mul, hRR, det_one]
  · change uStar h _ * _ = 1
    have hX : uStar h (bdK h x) = (bdK h x)ᵀ := by rw [uStar, map_bar_bdK]
    have hRi : uStar h (↑R⁻¹ : Matrix (Fin 4) (Fin 4) K) * uStar h (R : Matrix (Fin 4) (Fin 4) K)
        = 1 := by rw [← uStar_mul, hRR, uStar_one]
    rw [uStar_mul, uStar_mul, hX]
    calc uStar h (↑R⁻¹ : Matrix (Fin 4) (Fin 4) K) * ((bdK h x)ᵀ *
          uStar h (R : Matrix (Fin 4) (Fin 4) K)) *
          ((R : Matrix (Fin 4) (Fin 4) K) * bdK h x * (↑R⁻¹ : Matrix (Fin 4) (Fin 4) K)) =
        uStar h (↑R⁻¹ : Matrix (Fin 4) (Fin 4) K) * ((bdK h x)ᵀ *
          (uStar h (R : Matrix (Fin 4) (Fin 4) K) * (R : Matrix (Fin 4) (Fin 4) K)) *
          bdK h x) * (↑R⁻¹ : Matrix (Fin 4) (Fin 4) K) := by simp only [Matrix.mul_assoc]
      _ = uStar h (↑R⁻¹ : Matrix (Fin 4) (Fin 4) K) *
          (uStar h (R : Matrix (Fin 4) (Fin 4) K) * (R : Matrix (Fin 4) (Fin 4) K)) *
          (↑R⁻¹ : Matrix (Fin 4) (Fin 4) K) := by
          rw [hR, Matrix.mul_smul, Matrix.smul_mul, transpose_bdK_bJ]
      _ = 1 := by rw [← Matrix.mul_assoc, hRi, Matrix.one_mul, hRR]

@[expose] noncomputable def bdHomU {R : GL (Fin 4) K} {t : K}
    (hR : uStar h (R : Matrix (Fin 4) (Fin 4) K) * (R : Matrix (Fin 4) (Fin 4) K) = t • bJ 1 1) :
    SpecialLinearGroup (Fin 2) h.fixedField × SpecialLinearGroup (Fin 2) h.fixedField →*
      unitarySU p f K 4 :=
  ((MulAut.conj R).toMonoidHom.comp (glBd h)).codRestrict _ (conj_glBd_mem h hR)

theorem val_bdHomU {R : GL (Fin 4) K} {t : K}
    (hR : uStar h (R : Matrix (Fin 4) (Fin 4) K) * (R : Matrix (Fin 4) (Fin 4) K) = t • bJ 1 1)
    (x : SpecialLinearGroup (Fin 2) h.fixedField × SpecialLinearGroup (Fin 2) h.fixedField) :
    (((bdHomU h hR x : unitarySU p f K 4) : GL (Fin 4) K) : Matrix (Fin 4) (Fin 4) K) =
      (R : Matrix (Fin 4) (Fin 4) K) * bdK h x * (↑R⁻¹ : Matrix (Fin 4) (Fin 4) K) := by
  change ((MulAut.conj R (glBd h x) : GL (Fin 4) K) : Matrix (Fin 4) (Fin 4) K) = _
  rw [MulAut.conj_apply, Units.val_mul, Units.val_mul, coe_glBd]

end StabU

end CFSG.ComponentClassification.CatFactsL4U4
