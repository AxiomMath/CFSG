module

public import CFSG.LocalAnalysis.SeitzReduction.SymplecticPilotGraphUnitaryEnd

public section

namespace CFSG.SeitzReduction.SymplecticPilot

open Matrix Subgroup CFSG.LocalAnalysis.ComponentInitial CFSG.LocalAnalysis.ComponentInitial.UnitaryHigher
open CFSG.ClassicalGroups.UnitaryFlag
open CFSG.ComponentClassification.OuterAutomorphisms (inner)

section Bar

variable {f : ℕ} {K' : Type} [Field K'] (h : UnitaryFieldData 2 f K') {m : ℕ}

theorem scalar_mem_primeFormUnitary (C : Matrix (Fin m) (Fin m) K') {c : K'ˣ}
    (hc : h.norm (c : K') = 1) :
    GeneralLinearGroup.scalar (Fin m) c ∈ primeFormUnitary h C := by
  rw [mem_primeFormUnitary, GeneralLinearGroup.coe_scalar, scalar_barTranspose_mul_mul, hc,
    one_smul]

end Bar

theorem primeFormBarInvertsInput_holds : PrimeFormBarInvertsInput := by
  intro f K' _ h m C hC hm φ hφ d hd hcomm
  obtain ⟨A, rfl⟩ := hd
  have hf1 : 1 ≤ f := h.one_le
  have e1 : primeFormConjHom h _ A * primeFormFieldHom h hC φ * (primeFormConjHom h _ A)⁻¹ *
      (primeFormFieldHom h hC φ)⁻¹ =
        primeFormConjHom h _ (A * primeFormFieldU h hC φ A⁻¹) := by
    rw [map_mul, ← primeFormField_conj_eq, map_inv]
    group
  rw [e1] at hcomm
  obtain ⟨s, hs⟩ := (mem_inner_primeFormP h _ _).1 hcomm
  have e2 : primeFormPsi h hC ⟨A * primeFormFieldU h hC φ A⁻¹ *
      (⟨s, s.2.1⟩ : primeFormUnitary h (C : Matrix (Fin m) (Fin m) K'))⁻¹, 1⟩ = 1 := by
    rw [primeFormPsi_apply, map_one, mul_one, map_mul _ (A * primeFormFieldU h hC φ A⁻¹), hs,
      map_inv, mul_inv_cancel]
  obtain ⟨-, c, hcN, hcB⟩ := (primeFormPsi_eq_one_iff h hC hm _).1 e2
  set δ : K'ˣ := GeneralLinearGroup.det (A : GL (Fin m) K') with hδ
  have hsdet : GeneralLinearGroup.det (s : GL (Fin m) K') = 1 := by
    ext
    rw [GeneralLinearGroup.val_det_apply, Units.val_one]
    exact s.2.2
  have hδφ : Units.map (φ : K' →* K') δ = δ ^ 2 ^ f := by
    ext
    rw [Units.coe_map, Units.val_pow_eq_pow_val]
    change φ (δ : K') = _
    rw [hφ, h.bar_apply]
  have hδN : δ ^ (2 ^ f + 1) = 1 := by
    ext
    rw [Units.val_pow_eq_pow_val, Units.val_one, ← h.norm_eq_pow, hδ,
      GeneralLinearGroup.val_det_apply]
    exact norm_det_eq_one h C A.2
  have hdet := congrArg GeneralLinearGroup.det hcB
  change GeneralLinearGroup.det ((A : GL (Fin m) K') * glAut φ ((A : GL (Fin m) K')⁻¹) *
    (s : GL (Fin m) K')⁻¹) = _ at hdet
  have det_glAut : ∀ X : GL (Fin m) K', GeneralLinearGroup.det (glAut φ X) =
      Units.map (φ : K' →* K') (GeneralLinearGroup.det X) := fun X => by
    ext
    rw [GeneralLinearGroup.val_det_apply, Units.coe_map, GeneralLinearGroup.val_det_apply]
    change ((X : Matrix (Fin m) (Fin m) K').map φ).det = φ (X : Matrix (Fin m) (Fin m) K').det
    rw [show (X : Matrix (Fin m) (Fin m) K').map φ =
      (φ : K' →+* K').mapMatrix (X : Matrix (Fin m) (Fin m) K') from rfl, ← RingHom.map_det]
    rfl
  rw [map_mul, map_mul, det_glAut] at hdet
  simp only [map_inv, hsdet, inv_one, mul_one] at hdet
  rw [GeneralLinearGroup.det_scalar, Fintype.card_fin, ← hδ, hδφ] at hdet
  have hδ2 : δ ^ 2 = c ^ m := by
    have h1 : (δ ^ 2 ^ f)⁻¹ = δ := by
      rw [inv_eq_iff_mul_eq_one, ← pow_succ, hδN]
    rw [h1] at hdet
    rw [sq, hdet]
  set μ : K'ˣ := c ^ (2 ^ (f - 1) + 1) with hμ
  have h2f : 2 ^ (f - 1) * 2 = 2 ^ f := by rw [← pow_succ]; congr 1; omega
  have hμm : μ ^ m = δ := by
    have e3 : 2 * (2 ^ (f - 1) + 1) = (2 ^ f + 1) + 1 := by omega
    rw [hμ, ← pow_mul, mul_comm, pow_mul, ← hδ2, ← pow_mul, e3, pow_succ, hδN, one_mul]
  have hcN' : (c : K') ^ (2 ^ f + 1) = 1 := by rw [← h.norm_eq_pow]; exact hcN
  have hμN : h.norm (μ : K') = 1 := by
    rw [h.norm_eq_pow, hμ, Units.val_pow_eq_pow_val, ← pow_mul, mul_comm, pow_mul, hcN', one_pow]
  have hμU := scalar_mem_primeFormUnitary h (C : Matrix (Fin m) (Fin m) K') hμN
  set A' : GL (Fin m) K' := (A : GL (Fin m) K') * (GeneralLinearGroup.scalar (Fin m) μ)⁻¹ with hA'
  have hA'U : A' ∈ primeFormUnitary h (C : Matrix (Fin m) (Fin m) K') :=
    mul_mem A.2 (inv_mem hμU)
  have hA'det : (A' : Matrix (Fin m) (Fin m) K').det = 1 := by
    rw [← GeneralLinearGroup.val_det_apply, hA', map_mul, map_inv, GeneralLinearGroup.det_scalar,
      Fintype.card_fin, ← hδ, hμm, mul_inv_cancel, Units.val_one]
  have hA'SU : A' ∈ gramSU h (C : Matrix (Fin m) (Fin m) K') := ⟨hA'U, hA'det⟩
  have hμ1 : primeFormConjHom h _ ⟨GeneralLinearGroup.scalar (Fin m) μ, hμU⟩ = 1 := by
    have h1 := (primeFormPsi_eq_one_iff h hC hm ⟨⟨_, hμU⟩, 1⟩).2 ⟨rfl, μ, hμN, rfl⟩
    rwa [primeFormPsi_apply, map_one, mul_one] at h1
  have hAeq : A = ⟨A', hA'U⟩ * ⟨GeneralLinearGroup.scalar (Fin m) μ, hμU⟩ :=
    Subtype.ext (by
      change (A : GL (Fin m) K') = A' * GeneralLinearGroup.scalar (Fin m) μ
      rw [hA', inv_mul_cancel_right])
  rw [hAeq, map_mul, hμ1, mul_one]
  exact (mem_inner_primeFormP h _ _).2 ⟨⟨A', hA'SU⟩, rfl⟩

end CFSG.SeitzReduction.SymplecticPilot
