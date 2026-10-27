module

public import CFSG.Assembly.RankThreeEvenDefs
public import CFSG.ClassicalGroups.UnitaryFlag.GroupData
public import CFSG.Fischer.Classification.Recognition.PSU6
public import CFSG.LocalAnalysis.ComponentClassification.ClassicalModelStatedBridge
public import CFSG.LocalAnalysis.RankTwoShapes.UnitaryFour.Bridge
public import CFSG.ThirdParty.QiuzhenCFSG.BenderSuzuki.MatrixGroups.PSL2

public section

namespace CFSG.HardMathSupport.Malle.Coordinator.CoverThreeNoInner

open CFSG.BenderSuzuki.MatrixGroups CFSG.LocalAnalysis.ComponentInitial
  CFSG.ClassicalGroups.UnitaryFlag
open scoped MatrixGroups

theorem exists_proj_of_sl2 {G : Type*} [Group G] {F : Type} [Field F] [Finite F]
    (e : SL(2, F) ≃* G) :
    ∃ π : G →* PSL2MatrixGroup F, Function.Surjective π ∧ Finite π.ker ∧ Nat.card π.ker ≤ 2 ∧
      π.ker ≤ Subgroup.center G := by
  let π : G →* PSL2MatrixGroup F :=
    (QuotientGroup.mk' (Subgroup.center SL(2, F))).comp e.symm.toMonoidHom
  have hker : ∀ z, z ∈ π.ker ↔ e.symm z ∈ Subgroup.center SL(2, F) := by
    intro z
    simp only [π, MonoidHom.mem_ker, MonoidHom.comp_apply, QuotientGroup.mk'_apply,
      QuotientGroup.eq_one_iff]
    rfl
  have hequiv : π.ker ≃ Subgroup.center SL(2, F) :=
    { toFun := fun z => ⟨e.symm z.1, (hker z.1).mp z.2⟩
      invFun := fun w => ⟨e w.1, (hker _).mpr (by simp)⟩
      left_inv := fun z => Subtype.ext (by simp)
      right_inv := fun w => Subtype.ext (by simp) }
  have hcard : Nat.card (Subgroup.center SL(2, F)) ≤ 2 := by
    have := Nat.card_congr (Matrix.SpecialLinearGroup.center_equiv_rootsOfUnity (n := Fin 2) (R := F)).toEquiv
    rw [this]
    simpa using card_rootsOfUnity F 2
  refine ⟨π, QuotientGroup.mk'_surjective _ |>.comp e.symm.surjective, ?_, ?_, ?_⟩
  · have : Finite (Subgroup.center SL(2, F)) := inferInstance
    exact Finite.of_equiv _ hequiv.symm
  · rw [Nat.card_congr hequiv]; exact hcard
  · intro z hz
    rw [hker] at hz
    have := (MulEquivClass.apply_mem_center_iff e).2 hz
    have h2 : z ∈ Set.center G := by simpa using this
    exact Subgroup.mem_center_iff.mpr (Semigroup.mem_center_iff.mp h2)

namespace SU2Gen

section Diag

variable {ℓ f : ℕ} {K : Type} [Field K]

@[expose] def diag2 (u : Kˣ) : GL (Fin 2) K where
  val := Matrix.diagonal ![(u : K), ((u⁻¹ : Kˣ) : K)]
  inv := Matrix.diagonal ![((u⁻¹ : Kˣ) : K), (u : K)]
  val_inv := by
    rw [Matrix.diagonal_mul_diagonal, ← Matrix.diagonal_one]
    congr 1
    ext k
    fin_cases k <;> simp
  inv_val := by
    rw [Matrix.diagonal_mul_diagonal, ← Matrix.diagonal_one]
    congr 1
    ext k
    fin_cases k <;> simp

theorem diag2_mul (u v : Kˣ) : diag2 u * diag2 v = diag2 (u * v) := by
  apply Units.ext
  simp only [diag2, Units.val_mul, Matrix.diagonal_mul_diagonal]
  congr 1
  ext k
  fin_cases k <;> simp [mul_comm]

theorem diag2_one : diag2 (1 : Kˣ) = 1 := by
  apply Units.ext
  simp only [diag2, Units.val_one]
  rw [← Matrix.diagonal_one]
  congr 1
  ext k
  fin_cases k <;> simp

theorem diag2_mem (h : UnitaryFieldData ℓ f K) (u : (Units.map h.normHom).ker) :
    diag2 (u : Kˣ) ∈ unitarySU ℓ f K 2 := by
  have hu : h.norm (u : Kˣ) = 1 := (UnitaryFieldData.mem_ker_normUnits h).mp u.2
  have hu' : (u : Kˣ).1 * h.bar (u : Kˣ).1 = 1 := hu
  have hu'' : h.bar (u : Kˣ).1 * (u : Kˣ).1 = 1 := by rw [mul_comm]; exact hu'
  have hinv : h.bar ((u⁻¹ : Kˣ) : K) * ((u⁻¹ : Kˣ) : K) = 1 := by
    rw [Units.val_inv_eq_inv_val, map_inv₀, ← mul_inv, hu'', inv_one]
  rw [mem_unitarySU_iff h]
  constructor
  · simp [diag2, Matrix.det_diagonal, Fin.prod_univ_two]
  · simp only [diag2, Matrix.diagonal_map (map_zero h.bar), Matrix.diagonal_transpose,
      Matrix.diagonal_mul_diagonal]
    rw [← Matrix.diagonal_one]
    congr 1
    ext k
    fin_cases k
    · simpa using hu''
    · simpa using hinv

@[expose] noncomputable def diagHom (h : UnitaryFieldData ℓ f K) :
    (Units.map h.normHom).ker →* unitarySU ℓ f K 2 where
  toFun u := ⟨diag2 (u : Kˣ), diag2_mem h u⟩
  map_one' := Subtype.ext diag2_one
  map_mul' _ _ := Subtype.ext (diag2_mul _ _).symm

theorem diagHom_injective (h : UnitaryFieldData ℓ f K) : Function.Injective (diagHom h) := by
  intro u v huv
  have := congrArg (fun A : unitarySU ℓ f K 2 =>
    ((A : GL (Fin 2) K) : Matrix (Fin 2) (Fin 2) K) 0 0) huv
  simp [diagHom, diag2] at this
  exact Subtype.ext (Units.ext this)

end Diag

section Sub

variable {ℓ f : ℕ} {K : Type} [Field K]

theorem bar_subfield (h : UnitaryFieldData ℓ f K) (f₀ : ℕ) (hf : f = 3 * f₀) (K₀ : Subfield K)
    (hK₀ : Nat.card K₀ = (ℓ ^ f₀) ^ 2) (h₀ : UnitaryFieldData ℓ f₀ K₀) (c : K₀) :
    h.bar (c : K) = ((h₀.bar c : K₀) : K) := by
  have := h.finite
  have : Fintype K₀ := Fintype.ofFinite K₀
  have hc : c ^ (ℓ ^ f₀) ^ 2 = c := by
    rw [← hK₀, Nat.card_eq_fintype_card]
    exact FiniteField.pow_card c
  rw [UnitaryFieldData.bar_apply, UnitaryFieldData.bar_apply, SubmonoidClass.coe_pow]
  have : ℓ ^ f = (ℓ ^ f₀) ^ 2 * ℓ ^ f₀ := by
    rw [hf, ← pow_mul, ← pow_add]; congr 1; ring
  rw [this, pow_mul, ← SubmonoidClass.coe_pow, hc]

@[expose] noncomputable def subfieldSU (h : UnitaryFieldData ℓ f K) (f₀ : ℕ) (hf : f = 3 * f₀)
    (K₀ : Subfield K) (hK₀ : Nat.card K₀ = (ℓ ^ f₀) ^ 2) (h₀ : UnitaryFieldData ℓ f₀ K₀) :
    unitarySU ℓ f₀ K₀ 2 →* unitarySU ℓ f K 2 where
  toFun A := ⟨Matrix.GeneralLinearGroup.map K₀.subtype (A : GL (Fin 2) K₀), by
    obtain ⟨hdet, hu⟩ := (mem_unitarySU_iff h₀).mp A.2
    rw [mem_unitarySU_iff h]
    have hcoe : ((Matrix.GeneralLinearGroup.map K₀.subtype (A : GL (Fin 2) K₀) : GL (Fin 2) K) :
        Matrix (Fin 2) (Fin 2) K) = ((A : GL (Fin 2) K₀) : Matrix (Fin 2) (Fin 2) K₀).map
          K₀.subtype := rfl
    rw [hcoe]
    constructor
    · rw [← RingHom.mapMatrix_apply, ← RingHom.map_det, hdet, map_one]
    · have hb : (((A : GL (Fin 2) K₀) : Matrix (Fin 2) (Fin 2) K₀).map K₀.subtype).map h.bar =
          (((A : GL (Fin 2) K₀) : Matrix (Fin 2) (Fin 2) K₀).map h₀.bar).map K₀.subtype := by
        ext i j
        simp [bar_subfield h f₀ hf K₀ hK₀ h₀]
      rw [hb, ← Matrix.transpose_map, ← Matrix.map_mul, hu, Matrix.map_one _ (map_zero _) (map_one _)]⟩
  map_one' := Subtype.ext (Units.ext (by simp [Matrix.GeneralLinearGroup.map]))
  map_mul' A B := Subtype.ext (by simp)

theorem subfieldSU_injective (h : UnitaryFieldData ℓ f K) (f₀ : ℕ) (hf : f = 3 * f₀)
    (K₀ : Subfield K) (hK₀ : Nat.card K₀ = (ℓ ^ f₀) ^ 2) (h₀ : UnitaryFieldData ℓ f₀ K₀) :
    Function.Injective (subfieldSU h f₀ hf K₀ hK₀ h₀) := by
  intro A B hAB
  have := congrArg (fun X : unitarySU ℓ f K 2 => ((X : GL (Fin 2) K) : Matrix (Fin 2) (Fin 2) K))
    hAB
  apply Subtype.ext
  apply Units.ext
  exact Matrix.map_injective Subtype.val_injective this

end Sub

section Final

variable {ℓ f : ℕ} {K : Type} [Field K]

theorem comm_mul_central {G : Type*} [Group G] (a b u v : G) (hu : u ∈ Subgroup.center G)
    (hv : v ∈ Subgroup.center G) :
    (a * u) * (b * v) * (a * u)⁻¹ * (b * v)⁻¹ = a * b * a⁻¹ * b⁻¹ := by
  have hu' : ∀ g, u * g = g * u := fun g => (Subgroup.mem_center_iff.mp hu g).symm
  have hv' : ∀ g, v * g = g * v := fun g => (Subgroup.mem_center_iff.mp hv g).symm
  have c1 : ∀ g, (a * u) * g * (a * u)⁻¹ = a * g * a⁻¹ := by
    intro g
    calc (a * u) * g * (a * u)⁻¹ = a * (u * g) * u⁻¹ * a⁻¹ := by
          simp only [_root_.mul_inv_rev, mul_assoc]
      _ = a * (g * u) * u⁻¹ * a⁻¹ := by rw [hu' g]
      _ = a * g * a⁻¹ := by simp only [mul_assoc, mul_inv_cancel, mul_one]
  rw [c1 (b * v), _root_.mul_inv_rev]
  calc a * (b * v) * a⁻¹ * (v⁻¹ * b⁻¹) = a * b * (v * a⁻¹) * (v⁻¹ * b⁻¹) := by
        simp only [mul_assoc]
    _ = a * b * (a⁻¹ * v) * (v⁻¹ * b⁻¹) := by rw [hv' a⁻¹]
    _ = a * b * a⁻¹ * b⁻¹ := by simp only [mul_assoc, mul_inv_cancel_left]

end Final

end SU2Gen

end CFSG.HardMathSupport.Malle.Coordinator.CoverThreeNoInner
