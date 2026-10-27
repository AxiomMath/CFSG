module

public import CFSG.HardMathSupport.Malle.E27Lie.Outer.ClassicalDiagU2Block

public section

open Matrix CFSG.LocalAnalysis.ComponentInitial CFSG.LocalAnalysis.ComponentInitial.UnitaryHigher
  CFSG.ClassicalGroups.UnitaryFlag CFSG.RankThree.PartOne.KCUnitaryModel

namespace CFSG.HardMathSupport.Malle.E27Lie

@[expose] noncomputable def diagGL (n : ℕ) (F : Type) [Field F] : (Fin n → Fˣ) →* GL (Fin n) F :=
  (Units.map (Matrix.diagonalRingHom (Fin n) F : (Fin n → F) →* Matrix (Fin n) (Fin n) F)).comp
    (MulEquiv.piUnits.symm : (∀ _ : Fin n, Fˣ) ≃* (∀ _ : Fin n, F)ˣ).toMonoidHom

variable {ℓ f n : ℕ} {F : Type} [Field F]

@[expose] def torusFun (a : Fin 3 → Fˣ) (j : ℕ) : Fˣ :=
  if h : j < 3 then a ⟨j, h⟩ else if j = 3 then (a 0 * a 1 * a 2)⁻¹ else 1

@[expose] def torusHom (n : ℕ) : (Fin 3 → Fˣ) →* (Fin n → Fˣ) where
  toFun a i := torusFun a i
  map_one' := by
    funext i
    simp only [torusFun]
    split_ifs <;> simp
  map_mul' a b := by
    funext i
    simp only [torusFun, Pi.mul_apply]
    split_ifs
    all_goals first | rfl |
      (rw [← mul_inv]; congr 1; simp only [mul_assoc, mul_comm, mul_left_comm]) | simp

theorem torusHom_apply (a : Fin 3 → Fˣ) (i : Fin n) : torusHom n a i = torusFun a i := rfl

theorem prod_torusFun (a : Fin 3 → Fˣ) (hn : 4 ≤ n) : ∏ i : Fin n, torusHom n a i = 1 := by
  obtain ⟨m, rfl⟩ : ∃ m, n = 4 + m := ⟨n - 4, by omega⟩
  simp only [torusHom_apply]
  rw [Fin.prod_univ_eq_prod_range (fun j => torusFun a j) (4 + m), Finset.prod_range_add]
  have h1 : ∏ x ∈ Finset.range m, torusFun a (4 + x) = 1 :=
    Finset.prod_eq_one fun x _ => by
      unfold torusFun
      rw [dite_eq_right_iff.2 fun h => by omega, ite_eq_right_iff.2 fun h => by omega]
  rw [h1, mul_one]
  simp [Finset.prod_range_succ, torusFun]

theorem torusHom_pow_three (h : UnitaryFieldData ℓ f F) (hq : ℓ ^ f = 2) (a : Fin 3 → Fˣ)
    (i : Fin n) : (torusHom n a i : F) ^ 3 = 1 := by
  have := pow_card_eq_one' (G := Fˣ) (x := torusHom n a i)
  rw [card_units_eq_three_of_pow_eq_two h hq] at this
  have h1 := congrArg Units.val this
  rwa [Units.val_pow_eq_pow_val, Units.val_one] at h1

theorem diagGL_torus_mem (h : UnitaryFieldData ℓ f F) (hq : ℓ ^ f = 2) (hn : 4 ≤ n)
    (a : Fin 3 → Fˣ) : diagGL n F (torusHom n a) ∈ gramSU h (idGram F n) := by
  refine ⟨?_, ?_⟩
  · change ((diagonal (fun i => (torusHom n a i : F))).map h.bar)ᵀ * (idGram F n : Matrix _ _ F) *
      diagonal (fun i => (torusHom n a i : F)) = (idGram F n : Matrix _ _ F)
    simp only [idGram, Units.val_one, Matrix.mul_one]
    rw [Matrix.diagonal_map (map_zero h.bar), Matrix.diagonal_transpose,
      Matrix.diagonal_mul_diagonal, ← Matrix.diagonal_one]
    congr 1
    funext i
    rw [UnitaryFieldData.bar_apply, hq, ← pow_succ]
    exact torusHom_pow_three h hq a i
  · change Matrix.det (diagonal (fun i => (torusHom n a i : F))) = 1
    rw [det_diagonal, ← Units.coe_prod, prod_torusFun a hn, Units.val_one]

@[expose] noncomputable def torusSU (h : UnitaryFieldData ℓ f F) (hq : ℓ ^ f = 2) (hn : 4 ≤ n) :
    (Fin 3 → Fˣ) →* gramSU h (idGram F n) :=
  ((diagGL n F).comp (torusHom n)).codRestrict _ (diagGL_torus_mem h hq hn)

theorem coe_torusSU (h : UnitaryFieldData ℓ f F) (hq : ℓ ^ f = 2) (hn : 4 ≤ n)
    (a : Fin 3 → Fˣ) :
    (((torusSU h hq hn a : gramSU h (idGram F n)) : GL (Fin n) F) : Matrix (Fin n) (Fin n) F) =
      diagonal fun i => (torusHom n a i : F) := rfl

theorem torus_injective (h : UnitaryFieldData ℓ f F) (hq : ℓ ^ f = 2) (hn : 5 ≤ n) :
    Function.Injective ((QuotientGroup.mk' (normOneScalars h (gramSU h (idGram F n)) n)).comp
      (torusSU (n := n) h hq (by omega))) := by
  rw [injective_iff_map_eq_one]
  intro a ha
  rw [MonoidHom.comp_apply, QuotientGroup.mk'_apply, QuotientGroup.eq_one_iff] at ha
  obtain ⟨c, -, -, hc⟩ := ha
  have key : ∀ i : Fin n, (torusHom n a i : F) = c := by
    intro i
    have h2 := congrArg (fun g : GL (Fin n) F => (g : Matrix (Fin n) (Fin n) F) i i) hc
    simp only [coe_torusSU, Matrix.GeneralLinearGroup.coe_scalar] at h2
    simpa using h2
  have h4 : torusHom n a ⟨4, by omega⟩ = 1 := by
    simp [torusHom_apply, torusFun]
  have hc1 : c = 1 := by
    have := key ⟨4, by omega⟩
    rw [h4] at this
    exact (Units.ext this).symm
  funext j
  have := key ⟨j, by omega⟩
  rw [hc1] at this
  have h5 : torusHom n a ⟨j, by omega⟩ = a j := by
    simp [torusHom_apply, torusFun]
  rw [h5] at this
  exact Units.ext this

end CFSG.HardMathSupport.Malle.E27Lie
