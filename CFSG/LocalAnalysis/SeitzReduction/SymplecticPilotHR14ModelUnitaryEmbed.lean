module

public import CFSG.LocalAnalysis.SeitzReduction.F4PilotMainGraphUnitaryModel
public import CFSG.LocalAnalysis.SeitzReduction.SymplecticPilotHR14ModelEmbed
public import CFSG.LocalAnalysis.SeitzReduction.UnitaryPilotNeighbourParam
public import CFSG.LocalAnalysis.SeitzReduction.UnitaryPilotSwapUniqueOuter

public section

namespace CFSG.SeitzReduction.SymplecticPilot

open Subgroup Matrix CFSG.Blueprint CFSG.Assembly.LowTwoRank CFSG.LocalAnalysis.ComponentInitial
open CFSG.LocalAnalysis.ComponentInitial.UnitaryHigher CFSG.ClassicalGroups.UnitaryFlag
open CFSG.ComponentClassification
open CFSG.ComponentClassification.FixedCommutingProduct (fixedSubgroup)
open CFSG.LocalAnalysis.ComponentInitial.FourGroupEvenCanonical (matrixIsometryGroup
  mem_matrixIsometryGroup)
open CFSG.ComponentClassification.UnbalancedCatalog.UnitaryFieldTransfer (fixedField_charP
  fixedField_finite map_subtype_map_bar map_subtype_injective)

section Embed

variable {f : ℕ} {K' : Type} [Field K'] (h : UnitaryFieldData 2 f K') {n : ℕ}
  [CharP h.fixedField 2] {C₀ : GL (Fin (2 * n)) K'}

omit [CharP h.fixedField 2] in
theorem map_subtype_blockSwapJ :
    (blockSwapJ (2 * n) n : Matrix (Fin (2 * n)) (Fin (2 * n)) h.fixedField).map
      h.fixedField.subtype = blockSwapJ (2 * n) n := by
  ext i j
  simp only [Matrix.map_apply, blockSwapJ, Matrix.of_apply]
  split_ifs <;> simp

theorem uModel_mem (hC₀ : (C₀ : Matrix (Fin (2 * n)) (Fin (2 * n)) K') = blockSwapJ (2 * n) n)
    (x : StatedSp n h.fixedField) :
    SpecialLinearGroup.toGL (SpecialLinearGroup.map h.fixedField.subtype
      (spModelSL n h.fixedField x)) ∈ gramSU h (C₀ : Matrix (Fin (2 * n)) (Fin (2 * n)) K') := by
  rw [hC₀, ← map_subtype_blockSwapJ h]
  exact F4Pilot.toGL_map_mem_gramSU h (spModelSL_mem x)

@[expose] noncomputable def uModelSU
    (hC₀ : (C₀ : Matrix (Fin (2 * n)) (Fin (2 * n)) K') = blockSwapJ (2 * n) n) :
    StatedSp n h.fixedField →* gramSU h (C₀ : Matrix (Fin (2 * n)) (Fin (2 * n)) K') :=
  (SpecialLinearGroup.toGL.comp ((SpecialLinearGroup.map h.fixedField.subtype).comp
    (spModelSL n h.fixedField))).codRestrict _ (uModel_mem h hC₀)

@[expose] noncomputable def uModelP
    (hC₀ : (C₀ : Matrix (Fin (2 * n)) (Fin (2 * n)) K') = blockSwapJ (2 * n) n) :
    StatedSp n h.fixedField →* primeFormP h (C₀ : Matrix (Fin (2 * n)) (Fin (2 * n)) K') :=
  (QuotientGroup.mk' _).comp (uModelSU h hC₀)

variable {h}

theorem coe_uModelSU (hC₀ : (C₀ : Matrix (Fin (2 * n)) (Fin (2 * n)) K') = blockSwapJ (2 * n) n)
    (x : StatedSp n h.fixedField) :
    (((uModelSU h hC₀ x : gramSU h (C₀ : Matrix (Fin (2 * n)) (Fin (2 * n)) K')) :
        GL (Fin (2 * n)) K') : Matrix (Fin (2 * n)) (Fin (2 * n)) K') =
      ((spModelSL n h.fixedField x : SpecialLinearGroup (Fin (2 * n)) h.fixedField) :
        Matrix (Fin (2 * n)) (Fin (2 * n)) h.fixedField).map h.fixedField.subtype :=
  rfl

theorem uModelP_apply (hC₀ : (C₀ : Matrix (Fin (2 * n)) (Fin (2 * n)) K') = blockSwapJ (2 * n) n)
    (x : StatedSp n h.fixedField) :
    uModelP h hC₀ x = ((uModelSU h hC₀ x : gramSU h (C₀ : Matrix (Fin (2 * n)) (Fin (2 * n)) K')) :
      primeFormP h (C₀ : Matrix (Fin (2 * n)) (Fin (2 * n)) K')) := rfl

theorem uModelSU_injective
    (hC₀ : (C₀ : Matrix (Fin (2 * n)) (Fin (2 * n)) K') = blockSwapJ (2 * n) n) :
    Function.Injective (uModelSU h hC₀) := by
  intro x y hxy
  apply spModelSL_injective
  apply Subtype.ext
  apply map_subtype_injective h
  have := congrArg (fun z : gramSU h (C₀ : Matrix (Fin (2 * n)) (Fin (2 * n)) K') =>
    ((z : GL (Fin (2 * n)) K') : Matrix (Fin (2 * n)) (Fin (2 * n)) K')) hxy
  simpa only [coe_uModelSU] using this

theorem uModelP_injective (hn : 1 ≤ n)
    (hC₀ : (C₀ : Matrix (Fin (2 * n)) (Fin (2 * n)) K') = blockSwapJ (2 * n) n) :
    Function.Injective (uModelP h hC₀) := by
  rw [injective_iff_map_eq_one]
  intro x hx
  rw [uModelP_apply, QuotientGroup.eq_one_iff] at hx
  obtain ⟨c, -, -, hc⟩ := hx
  have hmat := congrArg (fun g : GL (Fin (2 * n)) K' => (g : Matrix (Fin (2 * n)) (Fin (2 * n)) K'))
    hc
  simp only [coe_uModelSU, GeneralLinearGroup.coe_scalar] at hmat
  set i₀ : Fin (2 * n) := ⟨0, by omega⟩
  set c' : h.fixedField :=
    ((spModelSL n h.fixedField x : SpecialLinearGroup (Fin (2 * n)) h.fixedField) :
      Matrix (Fin (2 * n)) (Fin (2 * n)) h.fixedField) i₀ i₀ with hc'
  have hscal : ((spModelSL n h.fixedField x : SpecialLinearGroup (Fin (2 * n)) h.fixedField) :
      Matrix (Fin (2 * n)) (Fin (2 * n)) h.fixedField) = scalar (Fin (2 * n)) c' := by
    apply map_subtype_injective h
    beta_reduce
    rw [hmat]
    have hcc : h.fixedField.subtype c' = (c : K') := by
      rw [hc']
      have := congrFun (congrFun hmat i₀) i₀
      simpa only [Matrix.map_apply, scalar_apply, diagonal_apply_eq] using this
    ext i j
    simp only [Matrix.map_apply, scalar_apply, diagonal_apply]
    split_ifs <;> simp [hcc]
  have : NeZero (2 * n) := ⟨by omega⟩
  have hJ : (blockSwapJ (2 * n) n : Matrix (Fin (2 * n)) (Fin (2 * n)) h.fixedField) ≠ 0 := by
    intro h0
    have h1 := blockSwapJ_two_mul_mul_self n h.fixedField
    rw [h0, zero_mul] at h1
    exact zero_ne_one h1
  have h1 : SpecialLinearGroup.toGL (spModelSL n h.fixedField x) = 1 :=
    FourGroupEvenCanonical.eq_one_of_mem_of_scalar hJ (spModelSL_mem x) hscal
  apply spModelSL_injective
  rw [map_one]
  apply Subtype.ext
  exact congrArg (fun g : GL (Fin (2 * n)) h.fixedField =>
    (g : Matrix (Fin (2 * n)) (Fin (2 * n)) h.fixedField)) h1

theorem fieldBar_uModelP (hC : IsPrimeFormGram C₀)
    (hC₀ : (C₀ : Matrix (Fin (2 * n)) (Fin (2 * n)) K') = blockSwapJ (2 * n) n)
    (x : StatedSp n h.fixedField) :
    primeFormFieldHom h hC (UnitaryPilot.barRingEquiv h) (uModelP h hC₀ x) = uModelP h hC₀ x := by
  rw [uModelP_apply]
  change primeFormFieldAut h hC (UnitaryPilot.barRingEquiv h) _ = _
  rw [primeFormFieldAut_mk]
  congr 1
  apply Subtype.ext
  apply Units.ext
  rw [F4Pilot.coe_primeFormFieldSU, coe_uModelSU]
  ext i j
  simp only [Matrix.map_apply, UnitaryPilot.barRingEquiv_apply]
  exact (((spModelSL n h.fixedField x : SpecialLinearGroup (Fin (2 * n)) h.fixedField) :
    Matrix (Fin (2 * n)) (Fin (2 * n)) h.fixedField) i j).2

theorem range_uModelP (hn : 2 ≤ n) (hq : ¬(2 * n = 3 ∧ 2 ^ f = 2)) (hC : IsPrimeFormGram C₀)
    (hC₀ : (C₀ : Matrix (Fin (2 * n)) (Fin (2 * n)) K') = blockSwapJ (2 * n) n) :
    (uModelP h hC₀).range =
      fixedSubgroup (primeFormFieldHom h hC (UnitaryPilot.barRingEquiv h)) := by
  have : Finite K' := h.finite
  have := fixedField_finite h
  have hle : (uModelP h hC₀).range ≤
      fixedSubgroup (primeFormFieldHom h hC (UnitaryPilot.barRingEquiv h)) := by
    rintro _ ⟨x, rfl⟩
    exact fieldBar_uModelP hC hC₀ x
  obtain ⟨Cl, hCl, ⟨Φ⟩⟩ := UnitaryPilot.fixedSubgroup_primeFormFieldHom_equiv h (by omega) hq hC
    (Or.inr ⟨n, rfl, hC₀⟩) _ (fun x => UnitaryPilot.barRingEquiv_apply h x)
  have hClJ : (Cl : Matrix (Fin (2 * n)) (Fin (2 * n)) h.fixedField) = blockSwapJ (2 * n) n := by
    apply map_subtype_injective h
    beta_reduce
    rw [hCl, hC₀, map_subtype_blockSwapJ]
  refine Subgroup.eq_of_le_of_card_ge hle ?_
  rw [Nat.card_congr Φ.toEquiv, hClJ,
    Nat.card_congr (CFSG.ComponentClassification.OutcomeLocal.blockSwapIsometryEquivStatedSp
      (k := h.fixedField) (two_mul n).symm).toEquiv,
    ← Nat.card_congr (MonoidHom.ofInjective (uModelP_injective (by omega) hC₀)).toEquiv]

end Embed

end CFSG.SeitzReduction.SymplecticPilot
