module

public import CFSG.GH74.Uniqueness.Bender.OddComplement
public import CFSG.GH74.Uniqueness.Bender.UnitaryIrreducible
public import CFSG.LocalAnalysis.ProperTwoGeneratedCore.UnitaryPairIndexModel
public import CFSG.LocalAnalysis.ProperTwoGeneratedCore.RootCenterAutomorphismUnitary
public import CFSG.LocalAnalysis.ShultStronglyClosedTI.OddPrimeInvertersLinear

public noncomputable section

namespace CFSG.GH74.Uniqueness.Bender

open Subgroup Matrix
open scoped Pointwise

section Model

open CFSG.BenderSuzuki CFSG.BenderSuzuki.MatrixGroups CFSG.BenderSuzuki.External
open CFSG.ShultStronglyClosedTI CFSG.ShultStronglyClosedTI.UnitaryAutomorphism
open CFSG.ShultStronglyClosedTI.UnitaryHulls
open CFSG.ProperTwoGeneratedCore.RootCenter
open CFSG.ProperTwoGeneratedCore.UnitaryPairIndex.Frame
open CFSG.ProperTwoGeneratedCore.UnitaryPairIndex.Model

variable {E : Type} [Field E] [Finite E] [CharP E 2] (J : HermitianForm 3 E)
  (hJ : J.form = !![0, 0, 1; 0, 1, 0; 1, 0, 0])

def sublineP : Subgroup (ProjectiveSpecialUnitaryMatrixGroup J) :=
  (sublineL J (scalarCenter J) hJ).map (coverPSUEquiv J hJ).toMonoidHom

def torusP : Subgroup (ProjectiveSpecialUnitaryMatrixGroup J) :=
  (torusL J (scalarCenter J) hJ).map (coverPSUEquiv J hJ).toMonoidHom

omit [Finite E] [CharP E 2] in
theorem coverPSUEquiv_mk' (g : J.specialSubgroup) :
    coverPSUEquiv J hJ (QuotientGroup.mk' (scalarCenter J) g) = psuMk J g :=
  (coverPSUEquiv_apply J hJ _).trans (coverToPSU_mk hJ le_rfl g)

omit [Finite E] in
theorem mem_sublineP_iff {x : ProjectiveSpecialUnitaryMatrixGroup J} :
    x ∈ sublineP J hJ ↔ ∃ m, psuMk J (sublineHom J hJ m) = x := by
  constructor
  · rintro ⟨_, ⟨m, rfl⟩, rfl⟩
    exact ⟨m, (coverPSUEquiv_mk' J hJ _).symm⟩
  · rintro ⟨m, rfl⟩
    exact ⟨_, ⟨m, rfl⟩, coverPSUEquiv_mk' J hJ _⟩

omit [Finite E] [CharP E 2] in
theorem mem_torusP_iff {x : ProjectiveSpecialUnitaryMatrixGroup J} :
    x ∈ torusP J hJ ↔ ∃ c, psuMk J (torusHom J hJ c) = x := by
  constructor
  · rintro ⟨_, ⟨c, rfl⟩, rfl⟩
    exact ⟨c, (coverPSUEquiv_mk' J hJ _).symm⟩
  · rintro ⟨c, rfl⟩
    exact ⟨_, ⟨c, rfl⟩, coverPSUEquiv_mk' J hJ _⟩

omit [Finite E] in
theorem diag3_one_mul_conj_sublineHom (c : normOne J)
    (m : SpecialLinearGroup (Fin 2) (unitaryCoverFixedField J)) :
    diag3 1 (c : Eˣ) 1 * ((sublineHom J hJ m : J.specialSubgroup) : GL (Fin 3) E) *
        (diag3 1 (c : Eˣ) 1)⁻¹ = ((sublineHom J hJ m : J.specialSubgroup) : GL (Fin 3) E) := by
  apply Units.ext
  simp only [Units.val_mul, coe_sublineHom, coe_diag3, coe_diag3_inv]
  ext i j
  fin_cases i <;> fin_cases j <;> simp [Matrix.mul_apply, Fin.sum_univ_three]

omit [Finite E] [CharP E 2] in
theorem diag3_one_mul_conj_torusHom (c d : normOne J) :
    diag3 1 (c : Eˣ) 1 * ((torusHom J hJ d : J.specialSubgroup) : GL (Fin 3) E) *
        (diag3 1 (c : Eˣ) 1)⁻¹ = ((torusHom J hJ d : J.specialSubgroup) : GL (Fin 3) E) := by
  apply Units.ext
  simp only [Units.val_mul, coe_torusHom, coe_diag3, coe_diag3_inv]
  have hc0 : ((c : Eˣ) : E) ≠ 0 := Units.ne_zero _
  ext i j
  fin_cases i <;> fin_cases j <;> simp [Matrix.mul_apply, Fin.sum_univ_three]
  field_simp

omit [Finite E] [CharP E 2] in
theorem diagAut_psuMk (c : normOne J) (g : J.specialSubgroup) :
    ∃ g' : J.specialSubgroup, ((g' : J.specialSubgroup) : GL (Fin 3) E) =
        diag3 1 (c : Eˣ) 1 * (g : GL (Fin 3) E) * (diag3 1 (c : Eˣ) 1)⁻¹ ∧
      diagAut J hJ c (psuMk J g) = psuMk J g' := by
  have hmem : diag3 1 (c : Eˣ) 1 * (g : GL (Fin 3) E) * (diag3 1 (c : Eˣ) 1)⁻¹ ∈
      J.specialSubgroup := conj_mem_specialSubgroup (diag3_one_mem_unitary hJ c.2) g.2
  refine ⟨⟨_, hmem⟩, rfl, ?_⟩
  apply Subtype.ext
  exact coe_psuAut_mk J _ _ g.2

omit [Finite E] in
theorem diagAut_fixed_of_mem (c : normOne J) {x : ProjectiveSpecialUnitaryMatrixGroup J}
    (hx : x ∈ sublineP J hJ ⊔ torusP J hJ) : diagAut J hJ c x = x := by
  have hle : sublineP J hJ ⊔ torusP J hJ ≤
      MonoidHom.eqLocus (diagAut J hJ c).toMonoidHom (MonoidHom.id _) := by
    refine sup_le ?_ ?_
    · intro y hy
      obtain ⟨m, rfl⟩ := (mem_sublineP_iff J hJ).mp hy
      obtain ⟨g', hg', hδ⟩ := diagAut_psuMk J hJ c (sublineHom J hJ m)
      rw [diag3_one_mul_conj_sublineHom J hJ] at hg'
      have : g' = sublineHom J hJ m := Subtype.ext hg'
      rw [this] at hδ
      exact hδ
    · intro y hy
      obtain ⟨d, rfl⟩ := (mem_torusP_iff J hJ).mp hy
      obtain ⟨g', hg', hδ⟩ := diagAut_psuMk J hJ c (torusHom J hJ d)
      rw [diag3_one_mul_conj_torusHom J hJ] at hg'
      have : g' = torusHom J hJ d := Subtype.ext hg'
      rw [this] at hδ
      exact hδ
  exact hle hx

omit [Finite E] [CharP E 2] in
theorem block_diag_of_entries {c u : E} (hc1 : c ≠ 1)
    (M : Matrix (Fin 3) (Fin 3) E) (hdet : M.det = 1)
    (e00 : M 0 0 * u = M 0 0) (e02 : M 0 2 * u = M 0 2) (e20 : M 2 0 * u = M 2 0)
    (e22 : M 2 2 * u = M 2 2) (e11 : M 1 1 * u = M 1 1)
    (e10 : c * M 1 0 * u = M 1 0) (e12 : c * M 1 2 * u = M 1 2)
    (e01 : M 0 1 * c⁻¹ * u = M 0 1) (e21 : M 2 1 * c⁻¹ * u = M 2 1) :
    u = 1 ∧ M 0 1 = 0 ∧ M 1 0 = 0 ∧ M 1 2 = 0 ∧ M 2 1 = 0 := by
  have hu : u = 1 := by
    by_contra hu1
    have hu1' : u - 1 ≠ 0 := sub_ne_zero.mpr hu1
    have h00 : M 0 0 = 0 := by
      have : M 0 0 * (u - 1) = 0 := by linear_combination e00
      exact (mul_eq_zero.mp this).resolve_right hu1'
    have h02 : M 0 2 = 0 := by
      have : M 0 2 * (u - 1) = 0 := by linear_combination e02
      exact (mul_eq_zero.mp this).resolve_right hu1'
    have h20 : M 2 0 = 0 := by
      have : M 2 0 * (u - 1) = 0 := by linear_combination e20
      exact (mul_eq_zero.mp this).resolve_right hu1'
    have h22 : M 2 2 = 0 := by
      have : M 2 2 * (u - 1) = 0 := by linear_combination e22
      exact (mul_eq_zero.mp this).resolve_right hu1'
    have h11 : M 1 1 = 0 := by
      have : M 1 1 * (u - 1) = 0 := by linear_combination e11
      exact (mul_eq_zero.mp this).resolve_right hu1'
    rw [Matrix.det_fin_three, h00, h02, h20, h22, h11] at hdet
    simp at hdet
  subst hu
  have hc' : c - 1 ≠ 0 := sub_ne_zero.mpr hc1
  have hci : c⁻¹ - 1 ≠ 0 := by
    intro h
    exact hc1 (inv_eq_one.mp (sub_eq_zero.mp h))
  refine ⟨rfl, ?_, ?_, ?_, ?_⟩
  · have : M 0 1 * (c⁻¹ - 1) = 0 := by linear_combination e01
    exact (mul_eq_zero.mp this).resolve_right hci
  · have : M 1 0 * (c - 1) = 0 := by linear_combination e10
    exact (mul_eq_zero.mp this).resolve_right hc'
  · have : M 1 2 * (c - 1) = 0 := by linear_combination e12
    exact (mul_eq_zero.mp this).resolve_right hc'
  · have : M 2 1 * (c⁻¹ - 1) = 0 := by linear_combination e21
    exact (mul_eq_zero.mp this).resolve_right hci

omit [Finite E] [CharP E 2] in
theorem coe_diag3_one_eq_diagonal (c : Eˣ) :
    ((diag3 1 c 1 : GL (Fin 3) E) : Matrix (Fin 3) (Fin 3) E) =
      Matrix.diagonal ![(1 : E), (c : E), 1] := by
  rw [coe_diag3]
  ext i j
  fin_cases i <;> fin_cases j <;> simp

omit [Finite E] [CharP E 2] in
theorem coe_diag3_one_inv_eq_diagonal (c : Eˣ) :
    (((diag3 1 c 1)⁻¹ : GL (Fin 3) E) : Matrix (Fin 3) (Fin 3) E) =
      Matrix.diagonal ![(1 : E), ((c : E))⁻¹, 1] := by
  rw [coe_diag3_inv]
  ext i j
  fin_cases i <;> fin_cases j <;> simp

theorem mem_sup_of_diagAut_fixed {c : normOne J} (hc : c ≠ 1)
    (hcube : ∃ c' : normOne J, ((c' : Eˣ) : E) ^ 3 ≠ 1)
    {x : ProjectiveSpecialUnitaryMatrixGroup J} (hx : diagAut J hJ c x = x) :
    x ∈ sublineP J hJ ⊔ torusP J hJ := by
  obtain ⟨c', hc'3⟩ := hcube
  obtain ⟨g, rfl⟩ := psuMk_surjective x
  obtain ⟨g', hg', hδ⟩ := diagAut_psuMk J hJ c g
  rw [hδ] at hx
  obtain ⟨u, hu⟩ := psuMk_eq_psuMk_iff.mp hx
  have hcne : ((c : Eˣ) : E) ≠ 1 := fun h => hc (Subtype.ext (Units.ext h))
  have hc0 : ((c : Eˣ) : E) ≠ 0 := Units.ne_zero _
  have hdet : (((g : J.specialSubgroup) : GL (Fin 3) E) : Matrix (Fin 3) (Fin 3) E).det = 1 := by
    have h := congrArg Units.val ((J.mem_specialSubgroup_iff (g : GL (Fin 3) E)).mp g.2).2
    rwa [GeneralLinearGroup.val_det_apply, Units.val_one] at h
  have hu' := congrArg (fun a : GL (Fin 3) E => (a : Matrix (Fin 3) (Fin 3) E)) hu
  rw [hg'] at hu'
  simp only [Units.val_mul, coe_diag3_one_eq_diagonal, coe_diag3_one_inv_eq_diagonal,
    GeneralLinearGroup.coe_scalar] at hu'
  have e00 := congrFun (congrFun hu' 0) 0
  have e01 := congrFun (congrFun hu' 0) 1
  have e02 := congrFun (congrFun hu' 0) 2
  have e10 := congrFun (congrFun hu' 1) 0
  have e11 := congrFun (congrFun hu' 1) 1
  have e12 := congrFun (congrFun hu' 1) 2
  have e20 := congrFun (congrFun hu' 2) 0
  have e21 := congrFun (congrFun hu' 2) 1
  have e22 := congrFun (congrFun hu' 2) 2
  simp [scalar_apply] at e00 e01 e02 e10 e11 e12 e20 e21 e22
  have e11' : ((g : GL (Fin 3) E) : Matrix (Fin 3) (Fin 3) E) 1 1 * ((u : Eˣ) : E) =
      ((g : GL (Fin 3) E) : Matrix (Fin 3) (Fin 3) E) 1 1 := by
    have : ((c : Eˣ) : E) * ((g : GL (Fin 3) E) : Matrix (Fin 3) (Fin 3) E) 1 1 *
        ((c : Eˣ) : E)⁻¹ = ((g : GL (Fin 3) E) : Matrix (Fin 3) (Fin 3) E) 1 1 := by
      field_simp
    rwa [this] at e11
  obtain ⟨-, h01, h10, h12, h21⟩ := block_diag_of_entries (c := ((c : Eˣ) : E))
    (u := ((u : Eˣ) : E)) hcne ((g : GL (Fin 3) E) : Matrix (Fin 3) (Fin 3) E) hdet e00 e02 e20
    e22 e11' e10 e12 e01 e21
  have hcomm : g * torusHom J hJ c' = torusHom J hJ c' * g := by
    apply Subtype.ext
    apply Units.ext
    simp only [Subgroup.coe_mul, Units.val_mul, coe_torusHom, coe_diag3]
    ext i j
    fin_cases i <;> fin_cases j <;>
      simp [Matrix.mul_apply, Fin.sum_univ_three, h01, h10, h12, h21, mul_comm]
  obtain ⟨m, d, hmd⟩ := eq_subline_mul_torus_of_commute (C := ⊥) hJ bot_le hc'3 (g := g)
    (by rw [hcomm])
  rw [hmd, map_mul]
  exact Subgroup.mul_mem_sup ((mem_sublineP_iff J hJ).mpr ⟨m, rfl⟩)
    ((mem_torusP_iff J hJ).mpr ⟨d, rfl⟩)

omit [CharP E 2] in
theorem exists_pow_three_ne_one (f : ℕ) (hf : 2 ≤ f) (hcard : Nat.card E = (2 ^ f) ^ 2)
    (hfixed : Nat.card {x : E // J.conj x = x} = 2 ^ f) :
    ∃ c : normOne J, ((c : Eˣ) : E) ^ 3 ≠ 1 := by
  by_contra hcon
  have hcon' : ∀ c : normOne J, ((c : Eˣ) : E) ^ 3 = 1 := fun c => by
    by_contra hc
    exact hcon ⟨c, hc⟩
  have hq : 2 < 2 ^ f := lt_of_lt_of_le (by norm_num) (Nat.pow_le_pow_right two_pos hf)
  have hq4 : 4 ≤ 2 ^ f := le_trans (by norm_num) (Nat.pow_le_pow_right two_pos hf)
  have hM : Nat.card (normOne J) = 2 ^ f + 1 := card_normOne Nat.prime_two hq hcard hfixed
  obtain ⟨g, hg⟩ := IsCyclic.exists_generator (α := normOne J)
  have h1 : g ^ 3 = 1 := Subtype.ext (Units.ext (by simpa using hcon' g))
  have h2 : orderOf g = Nat.card (normOne J) := orderOf_eq_card_of_forall_mem_zpowers hg
  have h3 : orderOf g ∣ 3 := orderOf_dvd_of_pow_eq_one h1
  have := Nat.le_of_dvd (by norm_num) h3
  omega

theorem diagAut_fixed_iff (f : ℕ) (hf : 2 ≤ f) (hcard : Nat.card E = (2 ^ f) ^ 2)
    (hfixed : Nat.card {x : E // J.conj x = x} = 2 ^ f) {c : normOne J} (hc : c ≠ 1)
    (x : ProjectiveSpecialUnitaryMatrixGroup J) :
    diagAut J hJ c x = x ↔ x ∈ sublineP J hJ ⊔ torusP J hJ :=
  ⟨mem_sup_of_diagAut_fixed J hJ hc (exists_pow_three_ne_one J f hf hcard hfixed),
    diagAut_fixed_of_mem J hJ c⟩

omit [Finite E] [CharP E 2] in
theorem psuMk_torusHom_eq_hermitianTorusPSU (c : normOne J) :
    psuMk J (torusHom J hJ c) = hermitianTorusPSU J hJ (c : Eˣ) := by
  apply Subtype.ext
  rw [coe_psuMk, hermitianTorusPSU_val]
  congr 1
  apply Matrix.GeneralLinearGroup.ext
  intro i j
  have hc : J.conj ((c : Eˣ) : E) = ((c : Eˣ) : E)⁻¹ := conj_eq_inv_of_mem_normOne J c.2
  rw [hermitianTorusGL_val, hermitianTorusMatrix_eq, coe_torusHom, coe_diag3]
  fin_cases i <;> fin_cases j <;> simp [hc, sq]

omit [Finite E] [CharP E 2] in
theorem torusP_le_unitaryCoverTorus : torusP J hJ ≤ unitaryCoverTorus J hJ := by
  intro y hy
  obtain ⟨c, rfl⟩ := (mem_torusP_iff J hJ).mp hy
  exact ⟨(c : Eˣ), (psuMk_torusHom_eq_hermitianTorusPSU J hJ c).symm⟩

omit [Finite E] [CharP E 2] in
theorem psuMk_torusHom_eq_one_of_pow_three {c : normOne J} (h3 : ((c : Eˣ) : E) ^ 3 = 1) :
    psuMk J (torusHom J hJ c) = 1 := by
  rw [psuMk_eq_one_iff]
  refine ⟨(c : Eˣ), ?_⟩
  have hc3 : (c : Eˣ) ^ 3 = 1 := Units.ext (by simpa using h3)
  have hinv : (c : Eˣ)⁻¹ ^ 2 = (c : Eˣ) := by
    have h1 : (c : Eˣ)⁻¹ ^ 2 * (c : Eˣ) ^ 3 = (c : Eˣ) := by group
    rw [hc3, mul_one] at h1
    exact h1
  rw [coe_torusHom, hinv]
  apply Units.ext
  rw [GeneralLinearGroup.coe_scalar, coe_diag3, scalar_apply]
  ext i j
  fin_cases i <;> fin_cases j <;> simp

omit [Finite E] [CharP E 2] in
theorem coe_diag3_eq_diagonal (a b c : Eˣ) :
    ((diag3 a b c : GL (Fin 3) E) : Matrix (Fin 3) (Fin 3) E) =
      Matrix.diagonal ![(a : E), (b : E), (c : E)] := by
  rw [coe_diag3]
  ext i j
  fin_cases i <;> fin_cases j <;> simp

omit [Finite E] [CharP E 2] in
theorem coe_diag3_inv_eq_diagonal (a b c : Eˣ) :
    (((diag3 a b c)⁻¹ : GL (Fin 3) E) : Matrix (Fin 3) (Fin 3) E) =
      Matrix.diagonal ![((a⁻¹ : Eˣ) : E), ((b⁻¹ : Eˣ) : E), ((c⁻¹ : Eˣ) : E)] := by
  rw [coe_diag3_inv]
  ext i j
  fin_cases i <;> fin_cases j <;> simp

omit [Finite E] [CharP E 2] in
theorem conj_psuMk_torusHom (c : normOne J) :
    MulAut.conj (psuMk J (torusHom J hJ c)) = diagAut J hJ (c ^ 3)⁻¹ := by
  refine MulEquiv.ext fun z => ?_
  obtain ⟨g, rfl⟩ := psuMk_surjective z
  obtain ⟨g', hg', hδ⟩ := diagAut_psuMk J hJ (c ^ 3)⁻¹ g
  rw [hδ, MulAut.conj_apply, ← map_inv, ← map_mul, ← map_mul]
  refine congrArg (psuMk J) ?_
  apply Subtype.ext
  rw [hg']
  apply Units.ext
  have hc0 : ((c : Eˣ) : E) ≠ 0 := Units.ne_zero _
  simp only [Subgroup.coe_mul, Subgroup.coe_inv, Units.val_mul, coe_torusHom,
    coe_diag3_eq_diagonal, coe_diag3_inv_eq_diagonal, Subgroup.coe_pow]
  ext i j
  simp only [Matrix.diagonal_mul, Matrix.mul_diagonal]
  fin_cases i <;> fin_cases j <;> simp <;> field_simp

theorem mul_comm_iff_mem_sup_of_mem_torusP (f : ℕ) (hf : 2 ≤ f)
    (hcard : Nat.card E = (2 ^ f) ^ 2) (hfixed : Nat.card {x : E // J.conj x = x} = 2 ^ f)
    {y : ProjectiveSpecialUnitaryMatrixGroup J} (hy : y ∈ torusP J hJ) (hy1 : y ≠ 1)
    (w : ProjectiveSpecialUnitaryMatrixGroup J) :
    y * w = w * y ↔ w ∈ sublineP J hJ ⊔ torusP J hJ := by
  obtain ⟨c, rfl⟩ := (mem_torusP_iff J hJ).mp hy
  have hc3 : ((c : Eˣ) : E) ^ 3 ≠ 1 := fun h => hy1 (psuMk_torusHom_eq_one_of_pow_three J hJ h)
  have hd : (c ^ 3)⁻¹ ≠ 1 := by
    intro h
    apply hc3
    have := inv_eq_one.mp h
    simpa using congrArg (fun x : normOne J => ((x : Eˣ) : E)) this
  rw [← diagAut_fixed_iff J hJ f hf hcard hfixed hd w, ← conj_psuMk_torusHom J hJ c,
    MulAut.conj_apply, mul_inv_eq_iff_eq_mul]

theorem card_torusP (f : ℕ) (hf : 2 ≤ f) (hcard : Nat.card E = (2 ^ f) ^ 2)
    (hfixed : Nat.card {x : E // J.conj x = x} = 2 ^ f) :
    Nat.card (torusP J hJ) = (2 ^ f + 1) / Nat.gcd 3 (2 ^ f + 1) := by
  rw [torusP, Subgroup.card_map_of_injective (coverPSUEquiv J hJ).injective]
  exact card_torusL_scalarCenter hf hcard hfixed hJ

omit [Finite E] in
theorem sublineP_commute_torusP : ∀ x ∈ sublineP J hJ, ∀ y ∈ torusP J hJ, x * y = y * x := by
  intro x hx y hy
  obtain ⟨m, rfl⟩ := (mem_sublineP_iff J hJ).mp hx
  obtain ⟨c, rfl⟩ := (mem_torusP_iff J hJ).mp hy
  rw [← map_mul, ← map_mul, sublineHom_commute_torusHom hJ m c]

omit [Finite E] in
theorem sublineP_inf_torusP : sublineP J hJ ⊓ torusP J hJ = ⊥ := by
  rw [sublineP, torusP, ← Subgroup.map_inf_eq _ _ _ (coverPSUEquiv J hJ).injective,
    sublineL_inf_torusL hJ le_rfl, Subgroup.map_bot]

theorem nonempty_sublineP_equiv (f : ℕ) (hf : 2 ≤ f) (_hcard : Nat.card E = (2 ^ f) ^ 2)
    (hfixed : Nat.card {x : E // J.conj x = x} = 2 ^ f) :
    Nonempty (sublineP J hJ ≃* PSL2Model f) := by
  have hk0 := card_unitaryCoverFixedField (J := J) hfixed
  exact ⟨((Subgroup.equivMapOfInjective _ (coverPSUEquiv J hJ).toMonoidHom
    (coverPSUEquiv J hJ).injective).symm.trans ((sublineEquiv hJ le_rfl).symm.trans
      (CFSG.ShultStronglyClosedTI.OddPrimeInverters.sl2EquivPSL2Binary (by omega) hk0)))⟩

omit [CharP E 2] in
theorem unitaryRootCenter_eq_rootCenter (f : ℕ) (hf : 2 ≤ f) (hcard : Nat.card E = (2 ^ f) ^ 2)
    (hfixed : Nat.card {x : E // J.conj x = x} = 2 ^ f) :
    unitaryRootCenter J hJ = rootCenter (unitaryCoverRoot J hJ) := by
  ext x
  rw [mem_rootCenter_iff,
    (unitaryRootCenterAutomorphisms J f hf hcard hfixed hJ).center_iff x]
  constructor <;> rintro ⟨h1, h2⟩ <;> exact ⟨h1, fun y hy => (h2 y hy).symm⟩

theorem rootCenter_le_sublineP (f : ℕ) (_hf : 2 ≤ f) (hcard : Nat.card E = (2 ^ f) ^ 2)
    (hfixed : Nat.card {x : E // J.conj x = x} = 2 ^ f) :
    rootCenter (unitaryCoverRoot J hJ) ≤ sublineP J hJ := by
  intro z hz
  obtain ⟨w, hw0, rfl⟩ := (mem_rootCenter_unitaryCoverRoot_iff J hJ f hcard hfixed).mp hz
  have hmem := (mem_upperRootL_iff (C := scalarCenter J) hJ
    (heisL J (scalarCenter J) hJ w)).mpr ⟨w, hw0, rfl⟩
  refine ⟨_, upperRootL_le_sublineL hJ hmem, ?_⟩
  refine (coverPSUEquiv_mk' J hJ (hermitianUnipotentSU J hJ w)).trans ?_
  apply Subtype.ext
  rfl

omit [CharP E 2] in
theorem exists_conj_diag_of_odd (f : ℕ) (hf : 2 ≤ f) (hcard : Nat.card E = (2 ^ f) ^ 2)
    (hfixed : Nat.card {x : E // J.conj x = x} = 2 ^ f)
    (A : Subgroup (MulAut (ProjectiveSpecialUnitaryMatrixGroup J)))
    (hA : A ≤ rootCenterAut (unitaryCoverRoot J hJ) (unitaryRootCenter J hJ))
    (hodd : Odd (Nat.card A)) :
    ∃ r ∈ unitaryCoverRoot J hJ, ∀ σ ∈ A,
      MulAut.conj r * σ * (MulAut.conj r)⁻¹ ∈ (diagHom J hJ).range := by
  classical
  have : Finite (Matrix.ProjGenLinGroup (Fin 3) E) :=
    Finite.of_surjective Matrix.ProjGenLinGroup.mk Matrix.ProjGenLinGroup.mk_surjective
  have : Finite (ProjectiveSpecialUnitaryMatrixGroup J) :=
    Finite.of_injective _ Subtype.coe_injective
  have : Finite (MulAut (ProjectiveSpecialUnitaryMatrixGroup J)) :=
    Finite.of_injective _ DFunLike.coe_injective
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  set G₁ := rootCenterAut (unitaryCoverRoot J hJ) (unitaryRootCenter J hJ) with hG₁
  set Rc : Subgroup (MulAut (ProjectiveSpecialUnitaryMatrixGroup J)) :=
    (unitaryCoverRoot J hJ).map MulAut.conj with hRc
  have hsup : Rc ⊔ diagBar J hJ = G₁ := conj_root_sup_diagBar J hJ f hf hcard hfixed
  have hinf : Rc ⊓ diagBar J hJ = ⊥ := conj_root_inf_diagBar J hJ f hf hcard hfixed
  have hRcG : Rc ≤ G₁ := by rw [← hsup]; exact le_sup_left
  have hDG : diagBar J hJ ≤ G₁ := by rw [← hsup]; exact le_sup_right
  have hD₃D : (diagHom J hJ).range ≤ diagBar J hJ := le_sup_left
  have : (Rc.subgroupOf G₁).Normal := conj_root_normal J hJ
  have hRp : IsPGroup 2 Rc := by
    obtain ⟨S, hS⟩ := (unitaryRootCenterAutomorphisms J f hf hcard hfixed hJ).exists_sylow
    rintro ⟨x, r, hr, rfl⟩
    have hrS : r ∈ (S : Subgroup (ProjectiveSpecialUnitaryMatrixGroup J)) := by
      rw [hS]; exact hr
    obtain ⟨k, hk⟩ := S.isPGroup' ⟨r, hrS⟩
    refine ⟨k, Subtype.ext ?_⟩
    have hk' : r ^ 2 ^ k = 1 := by simpa using congrArg Subtype.val hk
    rw [Subgroup.coe_pow, Subgroup.coe_one]
    show (MulAut.conj r) ^ 2 ^ k = 1
    rw [← map_pow, hk', map_one]
  have hRpG : IsPGroup 2 (Rc.subgroupOf G₁) :=
    hRp.of_injective (Subgroup.subgroupOfEquivOfLe hRcG).toMonoidHom
      (Subgroup.subgroupOfEquivOfLe hRcG).injective
  have hND : Rc.subgroupOf G₁ ⊓ (diagBar J hJ).subgroupOf G₁ = ⊥ := by
    rw [eq_bot_iff]
    rintro ⟨x, hxG⟩ ⟨h1, h2⟩
    have : x ∈ Rc ⊓ diagBar J hJ := ⟨h1, h2⟩
    rw [hinf, Subgroup.mem_bot] at this
    exact Subgroup.mem_bot.mpr (Subtype.ext this)
  have hsup' : Rc.subgroupOf G₁ ⊔ (diagBar J hJ).subgroupOf G₁ = ⊤ := by
    rw [← Subgroup.subgroupOf_sup hRcG hDG, hsup, Subgroup.subgroupOf_self]
  have hD₃ : ∀ d ∈ (diagBar J hJ).subgroupOf G₁, Odd (orderOf d) →
      d ∈ (diagHom J hJ).range.subgroupOf G₁ := by
    intro d hd hodd'
    have hd' : (d : MulAut (ProjectiveSpecialUnitaryMatrixGroup J)) ∈ diagBar J hJ := hd
    have hodd'' : Odd (orderOf (d : MulAut (ProjectiveSpecialUnitaryMatrixGroup J))) := by
      rwa [Subgroup.orderOf_coe]
    obtain ⟨c, ε, hdε⟩ := (mem_diagBar_iff J hJ).1 hd'
    rw [Subgroup.mem_subgroupOf]
    fin_cases ε
    · have hdε' : (d : MulAut (ProjectiveSpecialUnitaryMatrixGroup J)) = diagAut J hJ c := by
        simpa using hdε
      exact ⟨c, by rw [hdε', diagHom_apply]⟩
    · exfalso
      have hdε' : (d : MulAut (ProjectiveSpecialUnitaryMatrixGroup J)) =
          diagAut J hJ c * barAut J hJ := by simpa using hdε
      have hsq : (d : MulAut (ProjectiveSpecialUnitaryMatrixGroup J)) ^ 2 = 1 := by
        rw [hdε', pow_two]
        calc diagAut J hJ c * barAut J hJ * (diagAut J hJ c * barAut J hJ)
            = diagAut J hJ c * (barAut J hJ * diagAut J hJ c) * barAut J hJ := by group
          _ = diagAut J hJ c * (diagAut J hJ c⁻¹ * barAut J hJ) * barAut J hJ := by
            rw [barAut_mul_diagAut J hJ c]
          _ = diagAut J hJ c * diagAut J hJ c⁻¹ * (barAut J hJ * barAut J hJ) := by group
          _ = 1 := by
            rw [barAut_mul_self J hJ, ← diagAut_mul J hJ, mul_inv_cancel, diagAut_one J hJ,
              mul_one]
      have hne : (d : MulAut (ProjectiveSpecialUnitaryMatrixGroup J)) ≠ 1 := by
        intro h1
        have h0 : diagAut J hJ c * barAut J hJ = 1 := by rw [← hdε']; exact h1
        have h : MulAut.conj (1 : ProjectiveSpecialUnitaryMatrixGroup J) * diagAut J hJ c *
            barAut J hJ ^ ((1 : Fin 2) : ℕ) = MulAut.conj 1 * diagAut J hJ 1 *
              barAut J hJ ^ ((0 : Fin 2) : ℕ) := by
          simp only [map_one, one_mul, diagAut_one J hJ, Fin.val_zero, pow_zero, mul_one,
            Fin.val_one, pow_one]
          exact h0
        exact absurd (eq_of_conj_diag_bar_eq J hJ f hf hcard hfixed (one_mem _) (one_mem _)
          h).2.2 (by decide)
      have h2 : orderOf (d : MulAut (ProjectiveSpecialUnitaryMatrixGroup J)) = 2 :=
        orderOf_eq_prime hsq hne
      rw [h2] at hodd''
      exact absurd hodd'' (by decide)
  have hA' : Odd (Nat.card (A.subgroupOf G₁)) := by
    rwa [Nat.card_congr (Subgroup.subgroupOfEquivOfLe hA).toEquiv]
  obtain ⟨n, hn, hconj⟩ := exists_conj_mem_of_odd_card (G := G₁) (N := Rc.subgroupOf G₁)
    (D := (diagBar J hJ).subgroupOf G₁) (D₃ := (diagHom J hJ).range.subgroupOf G₁)
    (A := A.subgroupOf G₁) hRpG hND hsup' (fun x hx => hD₃D hx) hD₃ hA'
  obtain ⟨r, hr, hrn⟩ := hn
  refine ⟨r, hr, fun σ hσ => ?_⟩
  have h1 := hconj ⟨σ, hA hσ⟩ hσ
  have h2 : ((n * ⟨σ, hA hσ⟩ * n⁻¹ : G₁) : MulAut (ProjectiveSpecialUnitaryMatrixGroup J)) ∈
      (diagHom J hJ).range := h1
  have hrn' : (n : MulAut (ProjectiveSpecialUnitaryMatrixGroup J)) = MulAut.conj r := hrn.symm
  rw [Subgroup.coe_mul, Subgroup.coe_mul, Subgroup.coe_inv, hrn'] at h2
  exact h2

end Model

end CFSG.GH74.Uniqueness.Bender
