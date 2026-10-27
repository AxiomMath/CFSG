module

public import CFSG.CGT.PushingUpLit.CGT6X.K7aOrth
public import CFSG.LocalAnalysis.ComponentInitial.UnitaryHigherAntiunitaryDescent
public import CFSG.LocalAnalysis.ShultStronglyClosedTI.UnitaryRootAutomorphismModel

public section

namespace CFSG.CGT.PushingUpLit.CGT6X.K7a

open Matrix CFSG.LocalAnalysis.ComponentInitial CFSG.LocalAnalysis.ComponentInitial.UnitaryHigher
  CFSG.ClassicalGroups.UnitaryFlag CFSG.LocalAnalysis
  CFSG.ShultStronglyClosedTI.UnitaryRootAutomorphism

section Defs

variable {f : ℕ} {K : Type} [Field K]

abbrev PI (h : UnitaryFieldData 2 f K) : Type :=
  primeFormP h ((1 : GL (Fin 3) K) : Matrix (Fin 3) (Fin 3) K)

variable (h : UnitaryFieldData 2 f K)

theorem orthGU_mem (A : orthSL h.fixedField) :
    (Matrix.SpecialLinearGroup.toGL (Matrix.SpecialLinearGroup.map h.fixedField.subtype A.1) :
      GL (Fin 3) K) ∈ gramSU h ((1 : GL (Fin 3) K) : Matrix (Fin 3) (Fin 3) K) := by
  have hmat : ((Matrix.SpecialLinearGroup.toGL
      (Matrix.SpecialLinearGroup.map h.fixedField.subtype A.1) : GL (Fin 3) K) :
        Matrix (Fin 3) (Fin 3) K) =
      (A.1 : Matrix (Fin 3) (Fin 3) h.fixedField).map h.fixedField.subtype := rfl
  rw [mem_gramSU, hmat]
  have hfix : ((A.1 : Matrix (Fin 3) (Fin 3) h.fixedField).map h.fixedField.subtype).map h.bar =
      (A.1 : Matrix (Fin 3) (Fin 3) h.fixedField).map h.fixedField.subtype := by
    ext i j
    exact (A.1 i j).2
  refine ⟨?_, ?_⟩
  · rw [hfix, Units.val_one, Matrix.mul_one, ← transpose_map, ← Matrix.map_mul,
      transpose_mul_self_of_mem A.2, Matrix.map_one _ (map_zero _) (map_one _)]
  · rw [← RingHom.mapMatrix_apply, ← RingHom.map_det, Matrix.SpecialLinearGroup.det_coe, map_one]

@[expose] noncomputable def orthGU :
    orthSL h.fixedField →* gramSU h ((1 : GL (Fin 3) K) : Matrix (Fin 3) (Fin 3) K) :=
  MonoidHom.codRestrict
    ((Matrix.SpecialLinearGroup.toGL.comp
      (Matrix.SpecialLinearGroup.map h.fixedField.subtype)).comp (orthSL h.fixedField).subtype)
    (gramSU h ((1 : GL (Fin 3) K) : Matrix (Fin 3) (Fin 3) K)) (fun A => orthGU_mem h A)

@[expose] noncomputable def orthToP : orthSL h.fixedField →* PI h :=
  (QuotientGroup.mk' (normOneScalars h (gramSU h ((1 : GL (Fin 3) K) : Matrix (Fin 3) (Fin 3) K))
    3)).comp (orthGU h)

@[expose] noncomputable def barAut : MulAut (PI h) :=
  primeFormFieldAut h isPrimeFormGram_one (fieldDataHermitianForm h).conj

theorem barAut_orthToP (A : orthSL h.fixedField) : barAut h (orthToP h A) = orthToP h A := by
  have hfix : ∀ i j, h.bar (((Matrix.SpecialLinearGroup.toGL
      (Matrix.SpecialLinearGroup.map h.fixedField.subtype A.1) : GL (Fin 3) K) :
        Matrix (Fin 3) (Fin 3) K) i j) =
      ((Matrix.SpecialLinearGroup.toGL
        (Matrix.SpecialLinearGroup.map h.fixedField.subtype A.1) : GL (Fin 3) K) :
        Matrix (Fin 3) (Fin 3) K) i j := fun i j => (A.1 i j).2
  show barAut h (↑(orthGU h A)) = ↑(orthGU h A)
  rw [barAut, primeFormFieldAut_mk]
  congr 1
  apply Subtype.ext
  apply Units.ext
  ext i j
  exact hfix i j

theorem barAut_fixed_imp (x : PI h) (hx : barAut h x = x) : x ∈ (orthToP h).range := by
  have hch : CharP K 2 := h.charP
  have hfin : Finite K := h.finite
  obtain ⟨g, rfl⟩ := QuotientGroup.mk_surjective x
  set φ : K ≃+* K := (fieldDataHermitianForm h).conj with hφ
  set F := primeFormFieldSU h (isPrimeFormGram_one (n := 3) (K := K)) φ with hF
  have hx' : ((F g : gramSU h ((1 : GL (Fin 3) K) : Matrix (Fin 3) (Fin 3) K)) : PI h) = ↑g := by
    rw [barAut, primeFormFieldAut_mk] at hx
    exact hx
  have hzN := QuotientGroup.eq.1 hx'
  obtain ⟨c, hcn, hc3, hcz⟩ := id hzN
  set M : Matrix (Fin 3) (Fin 3) K := ((g : GL (Fin 3) K) : Matrix (Fin 3) (Fin 3) K) with hM
  have hgeq : (g : GL (Fin 3) K) = (F g : GL (Fin 3) K) * GeneralLinearGroup.scalar (Fin 3) c := by
    rw [← hcz]
    simp
  have hMij : ∀ i j, M i j = h.bar (M i j) * (c : K) := by
    intro i j
    have h1 := congrArg (fun X : GL (Fin 3) K => (X : Matrix (Fin 3) (Fin 3) K) i j) hgeq
    simp only [Units.val_mul, GeneralLinearGroup.coe_scalar, Matrix.scalar_apply,
      Matrix.mul_diagonal] at h1
    exact h1
  have hc3' : (c : K) ^ 3 = 1 := by rw [← Units.val_pow_eq_pow_val, hc3, Units.val_one]
  have hbarc : h.bar (c : K) = (c : K) * c := by
    have hn : (c : K) * h.bar (c : K) = 1 := hcn
    have h2 : (c : K) * h.bar c = (c : K) * ((c : K) * c) := by
      rw [hn]
      linear_combination -hc3'
    exact mul_left_cancel₀ c.ne_zero h2
  set g' : gramSU h ((1 : GL (Fin 3) K) : Matrix (Fin 3) (Fin 3) K) := g * ((F g)⁻¹ * g) with hg'
  set M' : Matrix (Fin 3) (Fin 3) K := ((g' : GL (Fin 3) K) : Matrix (Fin 3) (Fin 3) K) with hM'
  have hM'ij : ∀ i j, M' i j = M i j * (c : K) := by
    intro i j
    have h1 : (g' : GL (Fin 3) K) = (g : GL (Fin 3) K) * GeneralLinearGroup.scalar (Fin 3) c := by
      rw [hg', Subgroup.coe_mul, hcz]
    have h2 := congrArg (fun X : GL (Fin 3) K => (X : Matrix (Fin 3) (Fin 3) K) i j) h1
    simp only [Units.val_mul, GeneralLinearGroup.coe_scalar, Matrix.scalar_apply,
      Matrix.mul_diagonal] at h2
    exact h2
  have hM'fix : ∀ i j, h.bar (M' i j) = M' i j := by
    intro i j
    rw [hM'ij, map_mul, hbarc]
    linear_combination (-(c : K)) * hMij i j
  have hM'barmap : M'.map h.bar = M' := Matrix.ext fun i j => hM'fix i j
  have hM'det : M'.det = 1 := g'.2.2
  have hgram : M'ᵀ * M' = 1 := by
    have h1 := g'.2.1
    rw [hM'barmap] at h1
    simpa using h1
  let Ak' : Matrix (Fin 3) (Fin 3) h.fixedField := Matrix.of fun i j => ⟨M' i j, hM'fix i j⟩
  have hAkmap : Ak'.map h.fixedField.subtype = M' := by
    ext i j
    rfl
  have hdetk : Ak'.det = 1 := by
    apply h.fixedField.subtype.injective
    rw [RingHom.map_det, RingHom.mapMatrix_apply, hAkmap, hM'det, map_one]
  have hAkorth : Ak' * Ak'ᵀ = 1 := by
    apply Matrix.map_injective h.fixedField.subtype.injective
    show (Ak' * Ak'ᵀ).map h.fixedField.subtype = (1 : Matrix (Fin 3) (Fin 3) h.fixedField).map
      h.fixedField.subtype
    rw [Matrix.map_mul, transpose_map, hAkmap, Matrix.map_one _ (map_zero _) (map_one _)]
    exact mul_eq_one_comm.mp hgram
  let Ak : Matrix.SpecialLinearGroup (Fin 3) h.fixedField := ⟨Ak', hdetk⟩
  have hAk : Ak ∈ orthSL h.fixedField := hAkorth
  refine ⟨⟨Ak, hAk⟩, ?_⟩
  show (↑(orthGU h ⟨Ak, hAk⟩) : PI h) = ↑g
  have hgg : orthGU h ⟨Ak, hAk⟩ = g' := by
    apply Subtype.ext
    apply Units.ext
    exact hAkmap
  rw [hgg, hg']
  exact QuotientGroup.mk_mul_of_mem g hzN

theorem barAut_fixed_iff (x : PI h) : barAut h x = x ↔ x ∈ (orthToP h).range := by
  constructor
  · exact barAut_fixed_imp h x
  · rintro ⟨A, rfl⟩
    exact barAut_orthToP h A

theorem card_range_orthToP_le : Nat.card (orthToP h).range ≤
    Nat.card (Matrix.SpecialLinearGroup (Fin 2) h.fixedField) := by
  have : Finite K := h.finite
  have : CharP K 2 := h.charP
  exact (Nat.card_le_card_of_surjective _ (orthToP h).rangeRestrict_surjective).trans
    card_orthSL_le

theorem unitary_surviving (Y : Subgroup (PI h))
    (hY : Nat.card Y = Nat.card (Matrix.SpecialLinearGroup (Fin 2) h.fixedField))
    (hYt : ∀ y ∈ Y, barAut h y = y) : Y = (orthToP h).range := by
  have : Finite K := h.finite
  apply Subgroup.eq_of_le_of_card_ge
  · exact fun y hy => (barAut_fixed_iff h y).1 (hYt y hy)
  · rw [hY]
    exact card_range_orthToP_le h

theorem unitary_involution_surviving (hf : 2 ≤ f) (t : MulAut (PI h)) (ht : orderOf t = 2)
    (htout : ∀ y, t ≠ MulAut.conj y) (Y : Subgroup (PI h))
    (hY : Nat.card Y = Nat.card (Matrix.SpecialLinearGroup (Fin 2) h.fixedField))
    (hYt : ∀ y ∈ Y, t y = y) :
    ∃ (θ : PI h ≃* PI h) (H : GL (Fin 3) K),
      ((H : Matrix (Fin 3) (Fin 3) K).map h.bar)ᵀ * (H : Matrix (Fin 3) (Fin 3) K) = 1 ∧
      (∀ g g' : gramSU h ((1 : GL (Fin 3) K) : Matrix (Fin 3) (Fin 3) K),
        (g' : GL (Fin 3) K) = H * g * H⁻¹ → θ (g : PI h) = g') ∧
      (∀ x, t (θ x) = θ (barAut h x)) ∧ Y = (orthToP h).range.map θ.toMonoidHom := by
  have hq : ¬(3 = 3 ∧ 2 ^ f = 2) := by
    rintro ⟨-, h2⟩
    have : 2 ^ 2 ≤ 2 ^ f := Nat.pow_le_pow_right (by norm_num) hf
    omega
  have hlift := even_unitary_involution_matrix_lifts h isPrimeFormGram_one (by norm_num) hq t ht
  rcases hlift.1 with hφ | hφ
  · obtain ⟨s, -, -, hs⟩ := hlift.2.1 hφ
    exact absurd (hs.trans (primeFormConjHom_eq_conj h _ s)) (htout _)
  obtain ⟨-, H, C₀, hC₀, hC₀1, -, -, hHgram, -, ⟨θ, hθH, hθα⟩, -⟩ :=
    even_unitary_antiunitary_involution_descent h isPrimeFormGram_one (by norm_num) hq t ht hφ
  obtain rfl : C₀ = 1 := by
    rcases hC₀1 with h1 | ⟨r, hr, -⟩
    · exact Units.ext h1
    · omega
  have hφJ : primeFormFieldFactor h isPrimeFormGram_one (by norm_num) hq t =
      (fieldDataHermitianForm h).conj := RingEquiv.ext fun x => (hφ x).trans rfl
  have hθ : ∀ x, t (θ x) = θ (barAut h x) := by
    intro x
    have h1 := hθα (θ x)
    rw [MulEquiv.symm_apply_apply, hφJ] at h1
    exact h1
  refine ⟨θ, H, ?_, hθH, hθ, ?_⟩
  · have h1 := hHgram
    rw [Units.val_one, Matrix.mul_one] at h1
    exact h1
  ·
    have hfix : ∀ y' ∈ Y.map θ.symm.toMonoidHom, barAut h y' = y' := by
      rintro _ ⟨y, hy, rfl⟩
      have h1 := hθ (θ.symm y)
      rw [MulEquiv.apply_symm_apply, hYt y hy] at h1
      show barAut h (θ.symm y) = θ.symm y
      apply θ.injective
      rw [← h1, MulEquiv.apply_symm_apply]
    have hcard : Nat.card (Y.map θ.symm.toMonoidHom) =
        Nat.card (Matrix.SpecialLinearGroup (Fin 2) h.fixedField) :=
      (Nat.card_congr (Subgroup.equivMapOfInjective Y θ.symm.toMonoidHom
        θ.symm.injective).toEquiv).symm.trans hY
    have hEq := unitary_surviving h _ hcard hfix
    ext x
    constructor
    · intro hx
      refine ⟨θ.symm x, ?_, by simp⟩
      rw [← hEq]
      exact ⟨x, hx, rfl⟩
    · rintro ⟨z, hz, rfl⟩
      rw [← hEq] at hz
      obtain ⟨y, hy, rfl⟩ := hz
      simpa using hy

end Defs

end CFSG.CGT.PushingUpLit.CGT6X.K7a
