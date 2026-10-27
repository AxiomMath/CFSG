module

public import CFSG.CharacterTheory.Wreathed.CentralSL2.ProjectiveMap
public import CFSG.CharacterTheory.Wreathed.CentralSL2.NonsplitField

public section

open scoped BigOperators Classical

namespace CFSG.Wreathed.CentralSL2

open Matrix CFSG.Wreathed.CyclicCentralSL2Extension
open CFSG.ComponentClassification.CatalogueSchreierLinearTwo
open CFSG.Wreathed.CentralSL2Abelianization

section GLFacts

variable (F : Type) [Field F] [Fintype F] (E : Type) [Field E] [Algebra F E]
  (basis : Module.Basis (Fin 2) F E) (b : Fˣ)

omit [Fintype F] in
theorem scalar_comm (c : Fˣ) (M : GL (Fin 2) F) :
    GeneralLinearGroup.scalar (Fin 2) c * M = M * GeneralLinearGroup.scalar (Fin 2) c := by
  have h : GeneralLinearGroup.scalar (Fin 2) c ∈ Subgroup.center (GL (Fin 2) F) := by
    rw [GeneralLinearGroup.center_eq_range_scalar]
    exact ⟨c, rfl⟩
  exact (Subgroup.mem_center_iff.mp h M).symm

omit [Fintype F] in
theorem mulGL_unitE (c : Fˣ) :
    mulGL F E basis (unitE F E c) = GeneralLinearGroup.scalar (Fin 2) c := by
  apply Units.ext
  rw [mulGL_val, unitE_val, mulMatrix_algebraMap]
  rfl

omit [Fintype F] in
theorem mulGL_comm (s t : Eˣ) : mulGL F E basis s * mulGL F E basis t =
    mulGL F E basis t * mulGL F E basis s := by
  rw [← map_mul, mul_comm, map_mul]

omit [Fintype F] in
theorem mulGL_neg_one : mulGL F E basis (-1) = GeneralLinearGroup.scalar (Fin 2) (-1) := by
  rw [← mulGL_unitE F E basis]
  congr 1
  apply Units.ext
  simp

@[expose] noncomputable def frobGL : GL (Fin 2) F :=
  ⟨frobMatrix F E basis, frobMatrix F E basis, frobMatrix_mul_self F E basis,
    frobMatrix_mul_self F E basis⟩

theorem frobGL_val : ((frobGL F E basis : GL (Fin 2) F) : Matrix (Fin 2) (Fin 2) F) =
    frobMatrix F E basis := rfl

theorem frobGL_mul_self : frobGL F E basis * frobGL F E basis = 1 :=
  Units.ext (frobMatrix_mul_self F E basis)

theorem frobGL_inv : (frobGL F E basis)⁻¹ = frobGL F E basis :=
  inv_eq_of_mul_eq_one_right (frobGL_mul_self F E basis)

theorem frobGL_mul_mulGL (t : Eˣ) :
    frobGL F E basis * mulGL F E basis t =
      mulGL F E basis (t ^ Nat.card F) * frobGL F E basis := by
  apply Units.ext
  rw [Units.val_mul, Units.val_mul, frobGL_val, mulGL_val, mulGL_val, Units.val_pow_eq_pow_val,
    frobMatrix_mul_mulMatrix]

omit [Fintype F] in
theorem det_nonsquareMatrix : GeneralLinearGroup.det (nonsquareMatrix F b) = b := by
  apply Units.ext
  rw [GeneralLinearGroup.val_det_apply, nonsquareMatrix_val, Matrix.det_fin_two_of]
  ring

theorem det_mulMatrix_of_norm {z : Eˣ} {c : F}
    (hz : (z : E) * (z : E) ^ Nat.card F = algebraMap F E c) :
    (mulMatrix F E basis (z : E)).det = c := by
  apply (algebraMap F E).injective
  rw [algebraMap_det_mulMatrix, hz]

end GLFacts

section Matrices

variable (F : Type) [Field F] [Fintype F] (E : Type) [Field E] [Algebra F E]
  (basis : Module.Basis (Fin 2) F E) (b : Fˣ)

@[expose] noncomputable def vMatrix (z : Eˣ)
    (hz : (z : E) * (z : E) ^ Nat.card F = algebraMap F E b) : SpecialLinearGroup (Fin 2) F :=
  ⟨mulMatrix F E basis (z : E) *
      (((nonsquareMatrix F b)⁻¹ : GL (Fin 2) F) : Matrix (Fin 2) (Fin 2) F), by
    rw [Matrix.det_mul, det_mulMatrix_of_norm F E basis hz, ← GeneralLinearGroup.val_det_apply,
      map_inv, det_nonsquareMatrix, Units.val_inv_eq_inv_val, mul_inv_cancel₀ b.ne_zero]⟩

theorem toGL_vMatrix (z : Eˣ) (hz : (z : E) * (z : E) ^ Nat.card F = algebraMap F E b) :
    SpecialLinearGroup.toGL (vMatrix F E basis b z hz) =
      mulGL F E basis z * (nonsquareMatrix F b)⁻¹ := Units.ext rfl

@[expose] noncomputable def wMatrix (h2 : (2 : F) ≠ 0) (y : Eˣ)
    (hy : (y : E) * (y : E) ^ Nat.card F = -1) : SpecialLinearGroup (Fin 2) F :=
  ⟨mulMatrix F E basis (y : E) * frobMatrix F E basis, by
    have hy' : (y : E) * (y : E) ^ Nat.card F = algebraMap F E (-1) := by
      rw [hy, map_neg, map_one]
    rw [Matrix.det_mul, det_mulMatrix_of_norm F E basis hy', det_frobMatrix F E basis h2]
    ring⟩

theorem toGL_wMatrix (h2 : (2 : F) ≠ 0) (y : Eˣ) (hy : (y : E) * (y : E) ^ Nat.card F = -1) :
    SpecialLinearGroup.toGL (wMatrix F E basis h2 y hy) =
      mulGL F E basis y * frobGL F E basis := Units.ext rfl

theorem toGL_mulSL (t : normOne F E) :
    SpecialLinearGroup.toGL (mulSL F E basis t) = mulGL F E basis (t : Eˣ) := Units.ext rfl

theorem mulSL_negOneE (h2 : (2 : F) ≠ 0) :
    mulSL F E basis (negOneE F E h2) = CFSG.Semidihedral.ProjectiveSL2Cover.minusIdentity F := by
  apply SpecialLinearGroup.toGL_injective
  rw [toGL_mulSL, toGL_minusIdentity]
  exact mulGL_neg_one F E basis

end Matrices

section Elements

variable (F : Type) [Field F] [Fintype F] (b : Fˣ) (m : ℕ) (hm : 0 < m) (heven : Even m)
  (E : Type) [Field E] [Algebra F E] (basis : Module.Basis (Fin 2) F E)

@[expose] noncomputable def nonsplitDiag : normOne F E →* CentralExtension F b m hm heven :=
  (specialInclusion F b m hm heven).comp (mulSL F E basis)

@[expose] noncomputable def nonsplitGenerator (z : Eˣ)
    (hz : (z : E) * (z : E) ^ Nat.card F = algebraMap F E b) : CentralExtension F b m hm heven :=
  specialInclusion F b m hm heven (vMatrix F E basis b z hz) * cyclicGenerator F b m hm heven

@[expose] noncomputable def nonsplitWeyl (h2 : (2 : F) ≠ 0) (y : Eˣ)
    (hy : (y : E) * (y : E) ^ Nat.card F = -1) : CentralExtension F b m hm heven :=
  specialInclusion F b m hm heven (wMatrix F E basis h2 y hy)

variable {F b m hm heven E basis}
variable (z : Eˣ) (hz : (z : E) * (z : E) ^ Nat.card F = algebraMap F E b)

omit [Fintype F] in
include hz in
theorem pow_card_eq_unitE_mul_inv :
    z ^ Nat.card F = unitE F E b * z⁻¹ := by
  rw [eq_mul_inv_iff_mul_eq, mul_comm]
  apply Units.ext
  rw [Units.val_mul, Units.val_pow_eq_pow_val, hz]
  rfl

theorem nonsplitGenerator_mul_nonsplitDiag (t : normOne F E) :
    nonsplitGenerator F b m hm heven E basis z hz * nonsplitDiag F b m hm heven E basis t =
      nonsplitDiag F b m hm heven E basis t * nonsplitGenerator F b m hm heven E basis z hz := by
  unfold nonsplitGenerator nonsplitDiag
  rw [MonoidHom.comp_apply, mul_assoc, cyclicGenerator_mul_specialInclusion, ← mul_assoc,
    ← map_mul, ← mul_assoc, ← map_mul]
  congr 2
  apply SpecialLinearGroup.toGL_injective
  rw [map_mul, map_mul, beta_toGL, toGL_vMatrix, toGL_mulSL]
  have hc := mulGL_comm F E basis z (t : Eˣ)
  calc mulGL F E basis z * (nonsquareMatrix F b)⁻¹ *
        (nonsquareMatrix F b * mulGL F E basis (t : Eˣ) * (nonsquareMatrix F b)⁻¹)
      = mulGL F E basis z * mulGL F E basis (t : Eˣ) * (nonsquareMatrix F b)⁻¹ := by group
    _ = _ := by rw [hc]; group

theorem nonsplitGenerator_sq (h2 : (2 : F) ≠ 0) :
    nonsplitGenerator F b m hm heven E basis z hz ^ 2 =
      nonsplitDiag F b m hm heven E basis (rE F E b h2 z hz) *
        cyclicGenerator F b m hm heven ^ 2 := by
  unfold nonsplitGenerator nonsplitDiag
  rw [pow_two, mul_assoc, ← mul_assoc (cyclicGenerator F b m hm heven),
    cyclicGenerator_mul_specialInclusion, mul_assoc,
    ← mul_assoc (specialInclusion F b m hm heven _),
    ← map_mul, ← pow_two, MonoidHom.comp_apply]
  congr 2
  apply SpecialLinearGroup.toGL_injective
  rw [map_mul, beta_toGL, toGL_vMatrix, toGL_mulSL]
  have hJ : (nonsquareMatrix F b)⁻¹ * (nonsquareMatrix F b)⁻¹ =
      GeneralLinearGroup.scalar (Fin 2) (-b)⁻¹ := by
    rw [← _root_.mul_inv_rev, ← pow_two, nonsquareMatrix_square, map_inv]
  have hr : ((rE F E b h2 z hz : normOne F E) : Eˣ) = z * z * unitE F E (-b)⁻¹ := by
    apply Units.ext
    simp only [rE, Units.val_mul, Units.val_neg, Units.val_pow_eq_pow_val, Units.val_inv_eq_inv_val,
      unitE_val, map_inv₀, map_neg]
    ring
  rw [hr, map_mul, map_mul, mulGL_unitE, ← hJ]
  group

theorem nonsplitDiag_negOneE (h2 : (2 : F) ≠ 0) :
    nonsplitDiag F b m hm heven E basis (negOneE F E h2) = cyclicGenerator F b m hm heven ^ m := by
  rw [nonsplitDiag, MonoidHom.comp_apply, mulSL_negOneE, cyclicGenerator_pow_m]

theorem nonsplitGenerator_pow_m (h2 : (2 : F) ≠ 0) :
    nonsplitGenerator F b m hm heven E basis z hz ^ m =
      nonsplitDiag F b m hm heven E basis (cMinus F E b m h2 z hz) := by
  obtain ⟨k, hk⟩ := id heven
  have hdiv : m / 2 = k := by omega
  have hpow : nonsplitGenerator F b m hm heven E basis z hz ^ m =
      (nonsplitGenerator F b m hm heven E basis z hz ^ 2) ^ k := by
    rw [← pow_mul]
    congr 1
    omega
  have hupow : (cyclicGenerator F b m hm heven ^ 2) ^ k = cyclicGenerator F b m hm heven ^ m := by
    rw [← pow_mul]
    congr 1
    omega
  have hcomm : Commute (nonsplitDiag F b m hm heven E basis (rE F E b h2 z hz))
      (cyclicGenerator F b m hm heven ^ 2) := (cyclicGenerator_sq_comm F b m hm heven _).symm
  rw [hpow, nonsplitGenerator_sq z hz h2, hcomm.mul_pow, hupow,
    ← nonsplitDiag_negOneE (hm := hm) (heven := heven) (basis := basis) h2, ← map_pow, ← map_mul,
    cMinus, hdiv, mul_comm (rE F E b h2 z hz ^ k)]

variable (y : Eˣ) (hy : (y : E) * (y : E) ^ Nat.card F = -1)

omit [Field F] [Fintype F] [Algebra F E] in
include hy in
theorem mul_pow_card_eq_neg_one : y * y ^ Nat.card F = -1 := by
  apply Units.ext
  rw [Units.val_mul, Units.val_pow_eq_pow_val, hy, Units.val_neg, Units.val_one]

theorem nonsplitWeyl_sq (h2 : (2 : F) ≠ 0) :
    nonsplitWeyl F b m hm heven E basis h2 y hy ^ 2 = cyclicGenerator F b m hm heven ^ m := by
  rw [pow_two, nonsplitWeyl, ← map_mul, cyclicGenerator_pow_m]
  congr 1
  apply SpecialLinearGroup.toGL_injective
  rw [map_mul, toGL_wMatrix, toGL_minusIdentity]
  calc mulGL F E basis y * frobGL F E basis * (mulGL F E basis y * frobGL F E basis)
      = mulGL F E basis y * (frobGL F E basis * mulGL F E basis y) * frobGL F E basis := by
        group
    _ = mulGL F E basis (y * y ^ Nat.card F) * (frobGL F E basis * frobGL F E basis) := by
        rw [frobGL_mul_mulGL, map_mul]
        group
    _ = _ := by
        rw [frobGL_mul_self, mul_one, mul_pow_card_eq_neg_one y hy, mulGL_neg_one]

theorem nonsplitWeyl_conj_nonsplitDiag (h2 : (2 : F) ≠ 0) (t : normOne F E) :
    nonsplitWeyl F b m hm heven E basis h2 y hy * nonsplitDiag F b m hm heven E basis t *
        (nonsplitWeyl F b m hm heven E basis h2 y hy)⁻¹ =
      nonsplitDiag F b m hm heven E basis t⁻¹ := by
  rw [nonsplitWeyl, nonsplitDiag, MonoidHom.comp_apply, MonoidHom.comp_apply, ← map_inv,
    ← map_mul, ← map_mul]
  congr 1
  apply SpecialLinearGroup.toGL_injective
  rw [map_mul, map_mul, map_inv, toGL_wMatrix, toGL_mulSL, toGL_mulSL]
  have htq : (t : Eˣ) ^ Nat.card F = ((t⁻¹ : normOne F E) : Eˣ) := by
    apply Units.ext
    rw [Units.val_pow_eq_pow_val, pow_card_of_mem_normOne F E t.2, Subgroup.coe_inv,
      Units.val_inv_eq_inv_val]
  calc mulGL F E basis y * frobGL F E basis * mulGL F E basis (t : Eˣ) *
        (mulGL F E basis y * frobGL F E basis)⁻¹
      = mulGL F E basis y * (frobGL F E basis * mulGL F E basis (t : Eˣ)) *
          (frobGL F E basis)⁻¹ * (mulGL F E basis y)⁻¹ := by group
    _ = mulGL F E basis y * mulGL F E basis ((t : Eˣ) ^ Nat.card F) *
          (mulGL F E basis y)⁻¹ := by
        rw [frobGL_mul_mulGL]
        group
    _ = mulGL F E basis ((t : Eˣ) ^ Nat.card F) := by
        rw [mulGL_comm]
        group
    _ = _ := by rw [htq]

theorem nonsplitWeyl_conj_nonsplitGenerator (h2 : (2 : F) ≠ 0) :
    nonsplitWeyl F b m hm heven E basis h2 y hy * nonsplitGenerator F b m hm heven E basis z hz *
        (nonsplitWeyl F b m hm heven E basis h2 y hy)⁻¹ =
      cyclicGenerator F b m hm heven ^ 2 * cyclicGenerator F b m hm heven ^ m *
        (nonsplitGenerator F b m hm heven E basis z hz)⁻¹ := by
  have hL : nonsplitWeyl F b m hm heven E basis h2 y hy *
      nonsplitGenerator F b m hm heven E basis z hz *
        (nonsplitWeyl F b m hm heven E basis h2 y hy)⁻¹ =
      specialInclusion F b m hm heven (wMatrix F E basis h2 y hy * vMatrix F E basis b z hz *
        beta F b (wMatrix F E basis h2 y hy)⁻¹) * cyclicGenerator F b m hm heven := by
    rw [nonsplitWeyl, nonsplitGenerator, map_mul, map_mul, ← cyclicGenerator_conjugation,
      map_inv]
    group
  have hR : cyclicGenerator F b m hm heven ^ 2 * cyclicGenerator F b m hm heven ^ m *
      (nonsplitGenerator F b m hm heven E basis z hz)⁻¹ =
      specialInclusion F b m hm heven
        (CFSG.Semidihedral.ProjectiveSL2Cover.minusIdentity F *
          beta F b (vMatrix F E basis b z hz)⁻¹) * cyclicGenerator F b m hm heven := by
    rw [nonsplitGenerator, map_mul, ← cyclicGenerator_pow_m, ← cyclicGenerator_conjugation,
      map_inv]
    group
  rw [hL, hR]
  congr 2
  apply SpecialLinearGroup.toGL_injective
  rw [map_mul, map_mul, map_mul, beta_toGL, beta_toGL, map_inv, map_inv, toGL_wMatrix,
    toGL_vMatrix, toGL_minusIdentity]
  have hJ := nonsquareMatrix_square F b
  have hzq := pow_card_eq_unitE_mul_inv z hz
  calc mulGL F E basis y * frobGL F E basis * (mulGL F E basis z * (nonsquareMatrix F b)⁻¹) *
        (nonsquareMatrix F b * (mulGL F E basis y * frobGL F E basis)⁻¹ *
          (nonsquareMatrix F b)⁻¹)
      = mulGL F E basis y * (frobGL F E basis * mulGL F E basis z) * (frobGL F E basis)⁻¹ *
          (mulGL F E basis y)⁻¹ * (nonsquareMatrix F b)⁻¹ := by group
    _ = mulGL F E basis y * mulGL F E basis (z ^ Nat.card F) * (mulGL F E basis y)⁻¹ *
          (nonsquareMatrix F b)⁻¹ := by
        rw [frobGL_mul_mulGL]
        group
    _ = mulGL F E basis (z ^ Nat.card F) * (nonsquareMatrix F b)⁻¹ := by
        rw [mulGL_comm F E basis y]
        group
    _ = GeneralLinearGroup.scalar (Fin 2) (-1) * GeneralLinearGroup.scalar (Fin 2) (-b) *
          (mulGL F E basis z)⁻¹ * (nonsquareMatrix F b)⁻¹ := by
        rw [hzq, map_mul, map_inv, mulGL_unitE, ← map_mul, neg_one_mul, neg_neg]
    _ = GeneralLinearGroup.scalar (Fin 2) (-1) *
          (nonsquareMatrix F b * (mulGL F E basis z * (nonsquareMatrix F b)⁻¹)⁻¹ *
            (nonsquareMatrix F b)⁻¹) := by
        rw [← hJ, pow_two]
        group

theorem nonsplitWeyl_conj_nonsplitGenerator' (h2 : (2 : F) ≠ 0) :
    nonsplitWeyl F b m hm heven E basis h2 y hy * nonsplitGenerator F b m hm heven E basis z hz *
        (nonsplitWeyl F b m hm heven E basis h2 y hy)⁻¹ =
      nonsplitDiag F b m hm heven E basis (βE F E basis z) *
        nonsplitGenerator F b m hm heven E basis z hz := by
  rw [nonsplitWeyl_conj_nonsplitGenerator z hz y hy h2]
  have ha : cyclicGenerator F b m hm heven ^ 2 =
      nonsplitDiag F b m hm heven E basis (rE F E b h2 z hz)⁻¹ *
        nonsplitGenerator F b m hm heven E basis z hz ^ 2 := by
    rw [nonsplitGenerator_sq z hz h2, map_inv, inv_mul_cancel_left]
  have hcomm := nonsplitGenerator_mul_nonsplitDiag (hm := hm) (heven := heven) (basis := basis)
    z hz (negOneE F E h2)
  have hcomm2 := (Commute.pow_left hcomm 2).eq
  rw [ha, ← nonsplitDiag_negOneE (hm := hm) (heven := heven) (basis := basis) h2,
    βE_eq F E basis b h2 z hz, mul_comm (negOneE F E h2), map_mul]
  calc nonsplitDiag F b m hm heven E basis (rE F E b h2 z hz)⁻¹ *
        nonsplitGenerator F b m hm heven E basis z hz ^ 2 *
        nonsplitDiag F b m hm heven E basis (negOneE F E h2) *
        (nonsplitGenerator F b m hm heven E basis z hz)⁻¹
      = nonsplitDiag F b m hm heven E basis (rE F E b h2 z hz)⁻¹ *
          (nonsplitGenerator F b m hm heven E basis z hz ^ 2 *
            nonsplitDiag F b m hm heven E basis (negOneE F E h2)) *
          (nonsplitGenerator F b m hm heven E basis z hz)⁻¹ := by group
    _ = _ := by rw [hcomm2]; group

theorem nonsplitWeyl_inv_conj (h2 : (2 : F) ≠ 0) (g : CentralExtension F b m hm heven) :
    (nonsplitWeyl F b m hm heven E basis h2 y hy)⁻¹ * g *
        nonsplitWeyl F b m hm heven E basis h2 y hy =
      nonsplitWeyl F b m hm heven E basis h2 y hy * g *
        (nonsplitWeyl F b m hm heven E basis h2 y hy)⁻¹ := by
  have hw2 := nonsplitWeyl_sq (b := b) (hm := hm) (heven := heven) (basis := basis) y hy h2
  have hxc := cyclicGenerator_pow_m_comm F b m hm heven
  have hinv : (nonsplitWeyl F b m hm heven E basis h2 y hy)⁻¹ =
      cyclicGenerator F b m hm heven ^ m * nonsplitWeyl F b m hm heven E basis h2 y hy := by
    rw [inv_eq_iff_mul_eq_one, ← mul_assoc, ← hxc, mul_assoc, ← pow_two, hw2, ← pow_add,
      ← two_mul, cyclicGenerator_pow_two_m]
  rw [hinv, ← mul_assoc (nonsplitWeyl F b m hm heven E basis h2 y hy * g),
    ← hxc (nonsplitWeyl F b m hm heven E basis h2 y hy * g)]
  simp only [mul_assoc]

theorem baseResidue_nonsplitDiag (t : normOne F E) :
    baseResidue F b m hm heven (nonsplitDiag F b m hm heven E basis t) = 1 :=
  baseResidue_specialInclusion F b m hm heven _

theorem baseResidue_nonsplitGenerator :
    baseResidue F b m hm heven (nonsplitGenerator F b m hm heven E basis z hz) =
      Multiplicative.ofAdd 1 := by
  rw [nonsplitGenerator, map_mul, baseResidue_specialInclusion, one_mul, cyclicGenerator,
    baseResidue_quotientClass, map_one]

theorem baseResidue_nonsplitGenerator_pow (k : ℕ) :
    baseResidue F b m hm heven (nonsplitGenerator F b m hm heven E basis z hz ^ k) =
      Multiplicative.ofAdd (k : ZMod m) := by
  rw [map_pow, baseResidue_nonsplitGenerator, ← ofAdd_nsmul, nsmul_one]

theorem projectiveMap_nonsplitDiag (t : normOne F E) :
    projectiveMap F b m hm heven (nonsplitDiag F b m hm heven E basis t) =
      ProjGenLinGroup.mk (mulGL F E basis (t : Eˣ)) := by
  rw [nonsplitDiag, MonoidHom.comp_apply, projectiveMap_specialInclusion, toGL_mulSL]

theorem projectiveMap_nonsplitGenerator :
    projectiveMap F b m hm heven (nonsplitGenerator F b m hm heven E basis z hz) =
      ProjGenLinGroup.mk (mulGL F E basis z) := by
  rw [nonsplitGenerator, map_mul, projectiveMap_specialInclusion, projectiveMap_cyclicGenerator,
    toGL_vMatrix, ← map_mul, inv_mul_cancel_right]

end Elements

end CFSG.Wreathed.CentralSL2
