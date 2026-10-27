module

public import CFSG.GH74.Generic.S1.RUniRep

public section

namespace CFSG.GH74.Generic.S1.Uni

open CFSG CFSG.GH74 CFSG.GH74.L5U5 CFSG.Assembly.LowTwoRank Matrix
  CFSG.LocalAnalysis.ComponentInitial CFSG.LocalAnalysis.ComponentInitial.UnitaryHigher
  CFSG.ClassicalGroups.UnitaryFlag
open scoped MatrixGroups

variable {p f : ℕ} {F : Type} [Field F]

theorem rmem_statedSU (h : UnitaryFieldData p f F) {g : GL (Fin 4) F} :
    g ∈ StatedSU 4 (p ^ f) F ↔ (g : Matrix (Fin 4) (Fin 4) F).det = 1 ∧
      ((g : Matrix (Fin 4) (Fin 4) F).map h.bar)ᵀ * (g : Matrix (Fin 4) (Fin 4) F) = 1 := by
  have hfin : Finite F := h.finite
  have : Fact p.Prime := ⟨h.prime⟩
  have : CharP F p := h.charP
  have hF : Nat.card F = (p ^ f) ^ 2 := h.card_eq_sq
  rw [← CFSG.LieType.Universal.Unitary.SUid_eq_statedSU hF 4,
    CFSG.LieType.Universal.Unitary.mem_SUid]
  have hmap : (g : Matrix (Fin 4) (Fin 4) F).map (CFSG.LieType.BorelTits.unitaryInvolution F p f) =
      (g : Matrix (Fin 4) (Fin 4) F).map h.bar := by
    ext i j
    simp only [Matrix.map_apply]
    rw [CFSG.LieType.BorelTits.unitaryInvolution_apply, UnitaryFieldData.bar_apply]
  unfold CFSG.LieType.Universal.Unitary.conjTr
  rw [hmap]


@[expose] def RIsom (h : UnitaryFieldData p f F) (N : Matrix (Fin 4) (Fin 4) F) : Prop :=
  (N.map h.bar)ᵀ * N = 1

theorem risom_glAut (h : UnitaryFieldData p f F) {N : GL (Fin 4) F}
    (hN : RIsom h (N : Matrix (Fin 4) (Fin 4) F)) (σ : F ≃+* F) :
    RIsom h ((glAut σ N : GL (Fin 4) F) : Matrix (Fin 4) (Fin 4) F) := by
  unfold RIsom at hN ⊢
  rw [coe_glAut]
  have h2 : ((N : Matrix (Fin 4) (Fin 4) F).map σ).map h.bar =
      ((N : Matrix (Fin 4) (Fin 4) F).map h.bar).map σ := by
    ext i j
    simp [rrep_comm_bar h σ]
  rw [h2, ← Matrix.transpose_map, ← map_mul_σ, hN]
  exact map_one_σ σ

theorem risom_mul (h : UnitaryFieldData p f F) {N N' : Matrix (Fin 4) (Fin 4) F}
    (hN : RIsom h N) (hN' : RIsom h N') : RIsom h (N * N') := by
  unfold RIsom at *
  rw [Matrix.map_mul, Matrix.transpose_mul]
  calc (N'.map h.bar)ᵀ * (N.map h.bar)ᵀ * (N * N')
      = (N'.map h.bar)ᵀ * ((N.map h.bar)ᵀ * N) * N' := by simp only [Matrix.mul_assoc]
    _ = 1 := by rw [hN, Matrix.mul_one, hN']

theorem risom_one (h : UnitaryFieldData p f F) : RIsom h (1 : Matrix (Fin 4) (Fin 4) F) := by
  unfold RIsom
  rw [Matrix.map_one _ (map_zero h.bar) (map_one h.bar), Matrix.transpose_one, Matrix.mul_one]

theorem risom_inv (h : UnitaryFieldData p f F) {N : GL (Fin 4) F}
    (hN : RIsom h (N : Matrix (Fin 4) (Fin 4) F)) :
    RIsom h ((N⁻¹ : GL (Fin 4) F) : Matrix (Fin 4) (Fin 4) F) := by
  have h1 : (N : Matrix (Fin 4) (Fin 4) F) * ((N⁻¹ : GL (Fin 4) F) : Matrix (Fin 4) (Fin 4) F) =
      1 := by rw [← Units.val_mul, mul_inv_cancel, Units.val_one]
  have hinv : ((N : Matrix (Fin 4) (Fin 4) F).map h.bar)ᵀ =
      ((N⁻¹ : GL (Fin 4) F) : Matrix (Fin 4) (Fin 4) F) :=
    left_inv_eq_right_inv hN h1
  have h2 : (((N : Matrix (Fin 4) (Fin 4) F).map h.bar)ᵀ.map h.bar)ᵀ =
      (N : Matrix (Fin 4) (Fin 4) F) := by
    rw [Matrix.transpose_map, map_bar_bar, Matrix.transpose_transpose]
  unfold RIsom
  rw [← hinv, h2]
  exact mul_eq_one_comm.1 hN

@[expose] def UniPair (h : UnitaryFieldData p f F) : Subgroup (GL (Fin 4) F ⋊[glAut] (F ≃+* F)) where
  carrier := {x | ((x.left : Matrix (Fin 4) (Fin 4) F).map h.bar)ᵀ *
    (x.left : Matrix (Fin 4) (Fin 4) F) = 1}
  mul_mem' {x y} hx hy := by
    show RIsom h (((x * y).left : GL (Fin 4) F) : Matrix (Fin 4) (Fin 4) F)
    rw [SemidirectProduct.mul_left, Units.val_mul]
    exact risom_mul h hx (risom_glAut h hy x.right)
  one_mem' := by
    show RIsom h (((1 : GL (Fin 4) F ⋊[glAut] (F ≃+* F)).left : GL (Fin 4) F) :
      Matrix (Fin 4) (Fin 4) F)
    rw [SemidirectProduct.one_left, Units.val_one]
    exact risom_one h
  inv_mem' {x} hx := by
    show RIsom h (((x⁻¹).left : GL (Fin 4) F) : Matrix (Fin 4) (Fin 4) F)
    rw [SemidirectProduct.inv_left]
    exact risom_glAut h (risom_inv h hx) x.right⁻¹


@[expose] noncomputable def uniPsi (F : Type) [Field F] : GL (Fin 4) F ⋊[glAut] (F ≃+* F) →*
    MulAut (GL (Fin 4) F) :=
  SemidirectProduct.lift (MulAut.conj : GL (Fin 4) F →* MulAut (GL (Fin 4) F))
    (glAut : (F ≃+* F) →* MulAut (GL (Fin 4) F)) (by
      intro σ
      ext N X : 3
      simp [MulAut.conj_apply])

theorem uniPsi_apply (x : GL (Fin 4) F ⋊[glAut] (F ≃+* F)) (g : GL (Fin 4) F) :
    uniPsi F x g = x.left * glAut x.right g * x.left⁻¹ := rfl


theorem uniPsi_mem (h : UnitaryFieldData p f F) (x : UniPair h) {k : GL (Fin 4) F}
    (hk : k ∈ StatedSU 4 (p ^ f) F) : uniPsi F x.1 k ∈ StatedSU 4 (p ^ f) F := by
  obtain ⟨hdet, hiso⟩ := (rmem_statedSU h).1 hk
  rw [rmem_statedSU h, uniPsi_apply]
  refine ⟨?_, ?_⟩
  · have h1 : Matrix.GeneralLinearGroup.det (x.1.left * glAut x.1.right k * x.1.left⁻¹) =
        Matrix.GeneralLinearGroup.det (glAut x.1.right k) := by
      rw [map_mul, map_mul, map_inv, mul_comm (Matrix.GeneralLinearGroup.det x.1.left),
        mul_assoc, mul_inv_cancel, mul_one]
    have h2 := congrArg (fun u : Fˣ => (u : F)) h1
    simp only [Matrix.GeneralLinearGroup.val_det_apply] at h2
    rw [h2, coe_glAut]
    have h3 : ((k : Matrix (Fin 4) (Fin 4) F).map (x.1.right : F → F)).det =
        x.1.right (k : Matrix (Fin 4) (Fin 4) F).det := by
      have := RingHom.map_det (x.1.right : F →+* F) (k : Matrix (Fin 4) (Fin 4) F)
      exact this.symm
    rw [h3, hdet, map_one]
  · have hN : RIsom h (x.1.left : Matrix (Fin 4) (Fin 4) F) := x.2
    have h1 := risom_mul h (risom_mul h hN (risom_glAut h hiso x.1.right)) (risom_inv h hN)
    show RIsom h ((x.1.left * glAut x.1.right k * x.1.left⁻¹ : GL (Fin 4) F) :
      Matrix (Fin 4) (Fin 4) F)
    rw [Units.val_mul, Units.val_mul]
    exact h1


@[expose] noncomputable def uniAct (h : UnitaryFieldData p f F) :
    UniPair h →* MulAut ↥(StatedSU 4 (p ^ f) F) where
  toFun x :=
    { toFun := fun k => ⟨uniPsi F x.1 k, uniPsi_mem h x k.2⟩
      invFun := fun k => ⟨uniPsi F (x⁻¹).1 k, uniPsi_mem h x⁻¹ k.2⟩
      left_inv := fun k => by
        apply Subtype.ext
        show uniPsi F (x⁻¹).1 (uniPsi F x.1 k) = k
        rw [← MulAut.mul_apply, ← map_mul]
        have : (x⁻¹).1 * x.1 = 1 := inv_mul_cancel x.1
        rw [this, map_one]
        rfl
      right_inv := fun k => by
        apply Subtype.ext
        show uniPsi F x.1 (uniPsi F (x⁻¹).1 k) = k
        rw [← MulAut.mul_apply, ← map_mul]
        have : x.1 * (x⁻¹).1 = 1 := mul_inv_cancel x.1
        rw [this, map_one]
        rfl
      map_mul' := fun k k' => by
        apply Subtype.ext
        show uniPsi F x.1 ((k : GL (Fin 4) F) * k') = _
        rw [map_mul]
        rfl }
  map_one' := by
    refine MulEquiv.ext fun k => Subtype.ext ?_
    show uniPsi F (1 : UniPair h).1 k = k
    rw [show ((1 : UniPair h).1 : GL (Fin 4) F ⋊[glAut] (F ≃+* F)) = 1 from rfl, map_one]
    rfl
  map_mul' := fun x y => by
    refine MulEquiv.ext fun k => Subtype.ext ?_
    show uniPsi F (x * y).1 k = uniPsi F x.1 (uniPsi F y.1 k)
    rw [show ((x * y).1 : GL (Fin 4) F ⋊[glAut] (F ≃+* F)) = x.1 * y.1 from rfl, map_mul]
    rfl

theorem uniAct_apply (h : UnitaryFieldData p f F) (x : UniPair h) (k : ↥(StatedSU 4 (p ^ f) F)) :
    ((uniAct h x k : ↥(StatedSU 4 (p ^ f) F)) : GL (Fin 4) F) =
      x.1.left * glAut x.1.right (k : GL (Fin 4) F) * x.1.left⁻¹ := rfl

end CFSG.GH74.Generic.S1.Uni
