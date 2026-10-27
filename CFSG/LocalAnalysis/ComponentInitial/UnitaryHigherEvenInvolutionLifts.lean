module

public import CFSG.LocalAnalysis.ComponentInitial.UnitaryHigherPrimeFormRealization
public import CFSG.LocalAnalysis.ComponentInitial.UnitaryHigherLinearTwoEven

public section

namespace CFSG.LocalAnalysis.ComponentInitial.UnitaryHigher

open Matrix CFSG.ClassicalGroups.UnitaryFlag
open CFSG.ComponentClassification.OuterAutomorphisms (inner)

variable {f n : ℕ} {K : Type} [Field K] (h : UnitaryFieldData 2 f K) {C : GL (Fin n) K}
  (hC : IsPrimeFormGram C) (hn : 3 ≤ n) (hq : ¬(n = 3 ∧ 2 ^ f = 2))

include hn in
theorem primeFormPsi_sq_eq_one {A : primeFormUnitary h (C : Matrix (Fin n) (Fin n) K)}
    {φ : K ≃+* K} (hα : (primeFormPsi h hC ⟨A, φ⟩) ^ 2 = 1) :
    φ * φ = 1 ∧ ∃ c : Kˣ, h.norm (c : K) = 1 ∧
      (A : GL (Fin n) K) * glAut φ (A : GL (Fin n) K) = GeneralLinearGroup.scalar (Fin n) c := by
  rw [sq, ← map_mul] at hα
  obtain ⟨hφ, c, hcN, hc⟩ := (primeFormPsi_eq_one_iff h hC hn _).mp hα
  exact ⟨hφ, c, hcN, hc⟩

include hn hq in
theorem exists_sq_eq_one_of_fieldFactor_eq_one
    (α : MulAut (primeFormP h (C : Matrix (Fin n) (Fin n) K))) (hα : orderOf α = 2)
    (hφ : primeFormFieldFactor h hC hn hq α = RingEquiv.refl K) :
    ∃ s : gramSU h (C : Matrix (Fin n) (Fin n) K), (s : GL (Fin n) K) ≠ 1 ∧
      (s : GL (Fin n) K) * s = 1 ∧
        α = primeFormConjHom h (C : Matrix (Fin n) (Fin n) K) ⟨s, s.2.1⟩ := by
  have : CharP K 2 := h.charP
  have := h.finite
  obtain ⟨⟨A, φ⟩, rfl⟩ := primeFormPsi_surjective h hC hn hq α
  rw [primeFormFieldFactor_psi] at hφ
  change φ = RingEquiv.refl K at hφ
  subst hφ
  have hα2 : (primeFormPsi h hC ⟨A, RingEquiv.refl K⟩) ^ 2 = 1 := by
    have h1 := pow_orderOf_eq_one (primeFormPsi h hC ⟨A, RingEquiv.refl K⟩)
    rwa [hα] at h1
  obtain ⟨-, c, hcN, hc⟩ := primeFormPsi_sq_eq_one h hC hn hα2
  have hg1 : glAut (RingEquiv.refl K) (A : GL (Fin n) K) = A := by
    rw [show RingEquiv.refl K = (1 : K ≃+* K) from rfl, map_one, MulAut.one_apply]
  rw [hg1] at hc
  obtain ⟨b, hb⟩ := FiniteField.isSquare_of_char_two (ringChar.eq K 2) (((c⁻¹ : Kˣ) : K))
  have hb0 : b ≠ 0 := by
    rintro rfl
    rw [mul_zero] at hb
    exact Units.ne_zero _ hb
  have hbN : h.norm b = 1 := by
    refine eq_one_of_sq_eq_one ?_
    rw [sq, ← norm_mul_eq h, ← hb, Units.val_inv_eq_inv_val, norm_inv_eq h, hcN, inv_one]
  set u : Kˣ := Units.mk0 b hb0 with hu
  have hbU : GeneralLinearGroup.scalar (Fin n) u ∈
      primeFormUnitary h (C : Matrix (Fin n) (Fin n) K) := by
    rw [mem_primeFormUnitary, GeneralLinearGroup.coe_scalar, scalar_barTranspose_mul_mul,
      Units.val_mk0, hbN, one_smul]
  set s : GL (Fin n) K := GeneralLinearGroup.scalar (Fin n) u * A with hs
  have hsU : s ∈ primeFormUnitary h (C : Matrix (Fin n) (Fin n) K) := mul_mem hbU A.2
  have hss : s * s = 1 := by
    rw [hs, show GeneralLinearGroup.scalar (Fin n) u * (A : GL (Fin n) K) *
        (GeneralLinearGroup.scalar (Fin n) u * A) = GeneralLinearGroup.scalar (Fin n) u *
          GeneralLinearGroup.scalar (Fin n) u * ((A : GL (Fin n) K) * A) by
        rw [mul_assoc, ← mul_assoc (A : GL (Fin n) K), (commute_scalar u _).eq]
        simp only [mul_assoc], hc, ← map_mul, ← map_mul]
    rw [← map_one (GeneralLinearGroup.scalar (Fin n))]
    congr 1
    refine Units.ext ?_
    rw [Units.val_mul, Units.val_mul, Units.val_mk0, ← hb, Units.val_inv_eq_inv_val, Units.val_one,
      inv_mul_cancel₀ (Units.ne_zero c)]
  have hsdet : (s : Matrix (Fin n) (Fin n) K).det = 1 := by
    refine eq_one_of_sq_eq_one ?_
    rw [sq, ← det_mul, ← Units.val_mul, hss, Units.val_one, det_one]
  have h2 : primeFormConjHom h _ ⟨_, hbU⟩ = 1 := by
    have h3 := (primeFormPsi_eq_one_iff h hC hn ⟨⟨_, hbU⟩, 1⟩).mpr ⟨rfl, u, hbN, rfl⟩
    rwa [primeFormPsi_apply, map_one, mul_one] at h3
  have hαs : primeFormPsi h hC ⟨A, RingEquiv.refl K⟩ = primeFormConjHom h _ ⟨s, hsU⟩ := by
    rw [primeFormPsi_apply, show RingEquiv.refl K = (1 : K ≃+* K) from rfl, map_one, mul_one,
      show (⟨s, hsU⟩ : primeFormUnitary h (C : Matrix (Fin n) (Fin n) K)) = ⟨_, hbU⟩ * A from rfl,
      map_mul, h2, one_mul]
  refine ⟨⟨s, hsU, hsdet⟩, fun hs1 => ?_, hss, hαs⟩
  have h4 : primeFormConjHom h _ ⟨s, hsU⟩ = 1 := by
    rw [show (⟨s, hsU⟩ : primeFormUnitary h (C : Matrix (Fin n) (Fin n) K)) = 1 from
      Subtype.ext hs1, map_one]
  rw [hαs, h4, orderOf_one] at hα
  omega

include hn hq in
theorem exists_bar_lift_of_fieldFactor_bar
    (α : MulAut (primeFormP h (C : Matrix (Fin n) (Fin n) K))) (hα : orderOf α = 2)
    (hφ : ∀ x, primeFormFieldFactor h hC hn hq α x = h.bar x) :
    ∃ A : primeFormUnitary h (C : Matrix (Fin n) (Fin n) K),
      α = primeFormPsi h hC ⟨A, primeFormFieldFactor h hC hn hq α⟩ ∧
      ((A : GL (Fin n) K) : Matrix (Fin n) (Fin n) K) *
        ((A : GL (Fin n) K) : Matrix (Fin n) (Fin n) K).map h.bar = 1 ∧
      (∀ v : Fin n → K, ((A : GL (Fin n) K) : Matrix (Fin n) (Fin n) K) *ᵥ
        (fun i => h.bar ((((A : GL (Fin n) K) : Matrix (Fin n) (Fin n) K) *ᵥ
          fun j => h.bar (v j)) i)) = v) ∧
      ∀ v w : Fin n → K, gramForm h (C : Matrix (Fin n) (Fin n) K)
        (((A : GL (Fin n) K) : Matrix (Fin n) (Fin n) K) *ᵥ fun i => h.bar (v i))
        (((A : GL (Fin n) K) : Matrix (Fin n) (Fin n) K) *ᵥ fun i => h.bar (w i)) =
          h.bar (gramForm h (C : Matrix (Fin n) (Fin n) K) v w) := by
  have : CharP K 2 := h.charP
  obtain ⟨⟨A, φ⟩, rfl⟩ := primeFormPsi_surjective h hC hn hq α
  rw [primeFormFieldFactor_psi] at hφ ⊢
  change ∀ x, φ x = h.bar x at hφ
  refine ⟨A, rfl, ?_⟩
  have hα2 : (primeFormPsi h hC ⟨A, φ⟩) ^ 2 = 1 := by
    have h1 := pow_orderOf_eq_one (primeFormPsi h hC ⟨A, φ⟩)
    rwa [hα] at h1
  obtain ⟨-, c, hcN, hc⟩ := primeFormPsi_sq_eq_one h hC hn hα2
  set Am := ((A : GL (Fin n) K) : Matrix (Fin n) (Fin n) K) with hAm
  have hmap : Am.map φ = Am.map h.bar := Matrix.ext fun i j => hφ _
  have hc' : Am * Am.map h.bar = Matrix.scalar (Fin n) (c : K) := by
    have h1 := congrArg (fun g : GL (Fin n) K => (g : Matrix (Fin n) (Fin n) K)) hc
    simp only [Units.val_mul, coe_glAut, GeneralLinearGroup.coe_scalar] at h1
    rwa [hmap] at h1
  have hbarbar : (Am.map h.bar).map h.bar = Am := Matrix.ext fun i j => h.bar_bar _
  have h1 : Am.map h.bar * Am = Matrix.scalar (Fin n) (h.bar (c : K)) := by
    have h3 := congrArg (fun M : Matrix (Fin n) (Fin n) K => M.map h.bar) hc'
    simp only [Matrix.map_mul, hbarbar] at h3
    rw [h3, scalar_apply, scalar_apply, diagonal_map (map_zero h.bar)]
  have hAinv : ((A⁻¹ : primeFormUnitary h (C : Matrix (Fin n) (Fin n) K)) : GL (Fin n) K) *
      (A : GL (Fin n) K) = 1 := by
    rw [← Subgroup.coe_mul, inv_mul_cancel, Subgroup.coe_one]
  have hAinvm : (((A⁻¹ : primeFormUnitary h (C : Matrix (Fin n) (Fin n) K)) : GL (Fin n) K) :
      Matrix (Fin n) (Fin n) K) * Am = 1 := by
    rw [hAm, ← Units.val_mul, hAinv, Units.val_one]
  have h2 : Am.map h.bar * Am = Matrix.scalar (Fin n) (c : K) := by
    calc Am.map h.bar * Am
        = (((A⁻¹ : primeFormUnitary h (C : Matrix (Fin n) (Fin n) K)) : GL (Fin n) K) :
            Matrix (Fin n) (Fin n) K) * (Am * Am.map h.bar) * Am := by
          rw [← Matrix.mul_assoc, hAinvm, Matrix.one_mul]
      _ = Matrix.scalar (Fin n) (c : K) := by
          rw [hc', Matrix.mul_assoc,
            ((Matrix.scalar_commute (c : K) (fun r => Commute.all (c : K) r)) Am).eq,
            ← Matrix.mul_assoc, hAinvm, Matrix.one_mul]
  have hbarc : h.bar (c : K) = c := by
    have h3 := congrFun (congrFun (h1.symm.trans h2) ⟨0, by omega⟩) ⟨0, by omega⟩
    simpa using h3
  have hc1 : (c : K) = 1 := by
    refine eq_one_of_sq_eq_one ?_
    calc (c : K) ^ 2 = c * h.bar c := by rw [hbarc, sq]
      _ = 1 := hcN
  have hA : Am * Am.map h.bar = 1 := by rw [hc', hc1, map_one]
  have hbarmul : ∀ (M : Matrix (Fin n) (Fin n) K) (u : Fin n → K),
      (fun i => h.bar ((M *ᵥ u) i)) = M.map h.bar *ᵥ fun i => h.bar (u i) := fun M u => by
    funext i
    exact RingHom.map_mulVec h.bar M u i
  refine ⟨hA, fun v => ?_, fun v w => ?_⟩
  · rw [hbarmul, mulVec_mulVec, hA, one_mulVec]
    funext i
    exact h.bar_bar (v i)
  · rw [gramForm_mulVec, mem_primeFormUnitary.mp A.2, gramForm_apply, gramForm_apply]
    simp only [dotProduct, map_sum, map_mul, h.bar_bar]
    refine Finset.sum_congr rfl fun a _ => ?_
    rw [RingHom.map_mulVec, hC.map_eq h.bar]
    rfl

include hn hq in
theorem even_unitary_involution_matrix_lifts
    (α : MulAut (primeFormP h (C : Matrix (Fin n) (Fin n) K))) (hα : orderOf α = 2) :
    (primeFormFieldFactor h hC hn hq α = RingEquiv.refl K ∨
      ∀ x, primeFormFieldFactor h hC hn hq α x = h.bar x) ∧
    (primeFormFieldFactor h hC hn hq α = RingEquiv.refl K →
      ∃ s : gramSU h (C : Matrix (Fin n) (Fin n) K), (s : GL (Fin n) K) ≠ 1 ∧
        (s : GL (Fin n) K) * s = 1 ∧
          α = primeFormConjHom h (C : Matrix (Fin n) (Fin n) K) ⟨s, s.2.1⟩) ∧
    ((∀ x, primeFormFieldFactor h hC hn hq α x = h.bar x) →
      ∃ A : primeFormUnitary h (C : Matrix (Fin n) (Fin n) K),
        α = primeFormPsi h hC ⟨A, primeFormFieldFactor h hC hn hq α⟩ ∧
        ((A : GL (Fin n) K) : Matrix (Fin n) (Fin n) K) *
          ((A : GL (Fin n) K) : Matrix (Fin n) (Fin n) K).map h.bar = 1 ∧
        (∀ v : Fin n → K, ((A : GL (Fin n) K) : Matrix (Fin n) (Fin n) K) *ᵥ
          (fun i => h.bar ((((A : GL (Fin n) K) : Matrix (Fin n) (Fin n) K) *ᵥ
            fun j => h.bar (v j)) i)) = v) ∧
        ∀ v w : Fin n → K, gramForm h (C : Matrix (Fin n) (Fin n) K)
          (((A : GL (Fin n) K) : Matrix (Fin n) (Fin n) K) *ᵥ fun i => h.bar (v i))
          (((A : GL (Fin n) K) : Matrix (Fin n) (Fin n) K) *ᵥ fun i => h.bar (w i)) =
            h.bar (gramForm h (C : Matrix (Fin n) (Fin n) K) v w)) ∧
    ∀ β ∈ primeFormD h (C : Matrix (Fin n) (Fin n) K), orderOf β = 2 →
      β ∈ inner (primeFormP h (C : Matrix (Fin n) (Fin n) K)) := by
  have hF2 : primeFormFieldFactor h hC hn hq α * primeFormFieldFactor h hC hn hq α = 1 := by
    have h1 := pow_orderOf_eq_one α
    rw [hα] at h1
    rw [← map_mul, ← sq, h1, map_one]
  refine ⟨ringEquiv_eq_refl_or_bar h hF2, exists_sq_eq_one_of_fieldFactor_eq_one h hC hn hq α hα,
    exists_bar_lift_of_fieldFactor_bar h hC hn hq α hα, fun β hβ hβ2 => ?_⟩
  rw [← ker_primeFormFieldFactor h hC hn hq, MonoidHom.mem_ker] at hβ
  obtain ⟨s, -, -, hs⟩ := exists_sq_eq_one_of_fieldFactor_eq_one h hC hn hq β hβ2 hβ
  exact (mem_inner_primeFormP h _ β).mpr ⟨s, hs⟩

end CFSG.LocalAnalysis.ComponentInitial.UnitaryHigher
