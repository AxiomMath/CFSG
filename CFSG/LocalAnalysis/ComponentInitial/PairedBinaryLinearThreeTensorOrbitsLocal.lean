module

public import CFSG.LocalAnalysis.ComponentInitial.PairedBinaryLinearThreeTensorOrbitsModels
public import CFSG.LocalAnalysis.ProperTwoGeneratedCore.BinaryThreeSpaceFixedCodimensions
public import CFSG.Open.Defs

public noncomputable section

attribute [-instance] instCommGroupOfIsSimpleGroupOfIsNilpotent
  instAddCommGroupOfIsSimpleAddGroupOfIsNilpotent

namespace CFSG.LocalAnalysis.ComponentInitial.PairedTensorOrbits

open Module Matrix CFSG.ProperTwoGeneratedCore.PairedTensor
open CFSG.ProperTwoGeneratedCore.BinaryThreeSpace (Mat3 unitri unitriGL sylowT)
open scoped Pointwise

section Stab

variable {W : Type*} [AddCommMonoid W] [Module (ZMod 2) W]

@[expose] def vStab (ρ : Representation (ZMod 2) S W) (v : W) : Subgroup S where
  carrier := {g | ρ g v = v}
  mul_mem' {g h} hg hh := by
    change ρ (g * h) v = v
    rw [map_mul, Module.End.mul_apply, show ρ h v = v from hh, show ρ g v = v from hg]
  one_mem' := by
    change ρ 1 v = v
    rw [map_one, Module.End.one_apply]
  inv_mem' {g} hg := by
    change ρ g⁻¹ v = v
    conv_lhs => rw [← show ρ g v = v from hg]
    rw [← Module.End.mul_apply, ← map_mul, inv_mul_cancel, map_one, Module.End.one_apply]

end Stab

abbrev x₀ : N := ![0, 0, 1]

abbrev Ppt : Subgroup S := vStab repN x₀

theorem repN_eq_iff (g : S) (v : N) : repN g v = v ↔ v ᵥ* (g : Mat3) = v := by
  rw [repN_apply]
  constructor
  · intro h
    conv_lhs => rw [← h]
    rw [Matrix.vecMul_vecMul, ← Units.val_mul, inv_mul_cancel, Units.val_one, Matrix.vecMul_one]
  · intro h
    conv_lhs => rw [← h]
    rw [Matrix.vecMul_vecMul, ← Units.val_mul, mul_inv_cancel, Units.val_one, Matrix.vecMul_one]

theorem mem_Ppt_iff (g : S) : g ∈ Ppt ↔ x₀ ᵥ* (g : Mat3) = x₀ := repN_eq_iff g x₀

theorem mem_Ppt_iff' (g : S) : g ∈ Ppt ↔
    (g : Mat3) 2 0 = 0 ∧ (g : Mat3) 2 1 = 0 ∧ (g : Mat3) 2 2 = 1 := by
  rw [mem_Ppt_iff]
  constructor
  · intro h
    refine ⟨?_, ?_, ?_⟩
    · have := congrFun h 0
      simpa [Matrix.vecMul, dotProduct, Fin.sum_univ_three] using this
    · have := congrFun h 1
      simpa [Matrix.vecMul, dotProduct, Fin.sum_univ_three] using this
    · have := congrFun h 2
      simpa [Matrix.vecMul, dotProduct, Fin.sum_univ_three] using this
  · rintro ⟨h0, h1, h2⟩
    funext j
    fin_cases j <;> simp [Matrix.vecMul, dotProduct, Fin.sum_univ_three, h0, h1, h2]

theorem det_eq_one (g : S) : (g : Mat3).det = 1 := by
  have h1 : Matrix.GeneralLinearGroup.det g = 1 := Subsingleton.elim _ _
  have h2 := congrArg (fun u : (ZMod 2)ˣ => (u : ZMod 2)) h1
  simpa using h2

@[expose] def sgn2 (a b d e : ZMod 2) : ZMod 2 :=
  if (a = 1 ∧ b = 0 ∧ d = 0 ∧ e = 1) ∨ (a = 0 ∧ b = 1 ∧ d = 1 ∧ e = 1) ∨
    (a = 1 ∧ b = 1 ∧ d = 1 ∧ e = 0) then 0 else 1

theorem sgn2_mul : ∀ a b d e a' b' d' e' : ZMod 2, a * e + b * d = 1 → a' * e' + b' * d' = 1 →
    sgn2 (a * a' + b * d') (a * b' + b * e') (d * a' + e * d') (d * b' + e * e') =
      sgn2 a b d e + sgn2 a' b' d' e' := by
  decide

theorem sub_eq_add_zmod2 (x y : ZMod 2) : x - y = x + y := by
  revert x y
  decide

theorem mul_apply_three (M M' : Mat3) (i j : Fin 3) :
    (M * M') i j = M i 0 * M' 0 j + M i 1 * M' 1 j + M i 2 * M' 2 j := by
  rw [Matrix.mul_apply, Fin.sum_univ_three]

theorem ppt_entries {g : S} (hg : g ∈ Ppt) :
    (g : Mat3) 2 0 = 0 ∧ (g : Mat3) 2 1 = 0 ∧ (g : Mat3) 2 2 = 1 := (mem_Ppt_iff' g).1 hg

theorem ppt_det {g : S} (hg : g ∈ Ppt) :
    (g : Mat3) 0 0 * (g : Mat3) 1 1 + (g : Mat3) 0 1 * (g : Mat3) 1 0 = 1 := by
  obtain ⟨h0, h1, h2⟩ := ppt_entries hg
  have h := det_eq_one g
  rw [Matrix.det_fin_three, h0, h1, h2] at h
  have h' : (g : Mat3) 0 0 * (g : Mat3) 1 1 - (g : Mat3) 0 1 * (g : Mat3) 1 0 = 1 := by
    rw [← h]
    ring
  rwa [sub_eq_add_zmod2] at h'

theorem sgnPt_mul_aux {g h : S} (hg : g ∈ Ppt) (hh : h ∈ Ppt) :
    sgn2 (((g * h : S) : Mat3) 0 0) (((g * h : S) : Mat3) 0 1) (((g * h : S) : Mat3) 1 0)
        (((g * h : S) : Mat3) 1 1) =
      sgn2 ((g : Mat3) 0 0) ((g : Mat3) 0 1) ((g : Mat3) 1 0) ((g : Mat3) 1 1) +
        sgn2 ((h : Mat3) 0 0) ((h : Mat3) 0 1) ((h : Mat3) 1 0) ((h : Mat3) 1 1) := by
  rw [Units.val_mul, mul_apply_three, mul_apply_three, mul_apply_three, mul_apply_three,
    (ppt_entries hh).1, (ppt_entries hh).2.1]
  simp only [mul_zero, add_zero]
  exact sgn2_mul _ _ _ _ _ _ _ _ (ppt_det hg) (ppt_det hh)

@[expose] def sgnPt : Ppt →* Multiplicative (ZMod 2) where
  toFun g := Multiplicative.ofAdd (sgn2 (((g : S) : Mat3) 0 0) (((g : S) : Mat3) 0 1)
    (((g : S) : Mat3) 1 0) (((g : S) : Mat3) 1 1))
  map_one' := by
    change Multiplicative.ofAdd (sgn2 ((1 : Mat3) 0 0) ((1 : Mat3) 0 1) ((1 : Mat3) 1 0)
      ((1 : Mat3) 1 1)) = 1
    decide
  map_mul' g h := by
    rw [← ofAdd_add]
    exact congrArg Multiplicative.ofAdd (sgnPt_mul_aux g.2 h.2)

@[expose] def IsUT (X : Mat3) : Prop :=
  X 1 0 = 0 ∧ X 2 0 = 0 ∧ X 2 1 = 0 ∧ X 0 0 = 1 ∧ X 1 1 = 1 ∧ X 2 2 = 1

instance (X : Mat3) : Decidable (IsUT X) := by
  unfold IsUT
  infer_instance

theorem isUT_unitri : ∀ a b c : ZMod 2, IsUT (unitri a b c) := by decide

theorem mem_U3_iff (g : S) : g ∈ U3 ↔ IsUT (g : Mat3) := by
  constructor
  · rintro ⟨a, b, c, rfl⟩
    exact isUT_unitri a b c
  · rintro ⟨h10, h20, h21, h00, h11, h22⟩
    refine ⟨(g : Mat3) 0 1, (g : Mat3) 0 2, (g : Mat3) 1 2, Units.ext ?_⟩
    change (g : Mat3) = unitri _ _ _
    ext i j
    fin_cases i <;> fin_cases j <;> simp [unitri, h10, h20, h21, h00, h11, h22]

theorem card_U3 : Nat.card U3 = 8 := CFSG.ProperTwoGeneratedCore.BinaryThreeSpace.card_sylowT

section Conj

variable (c : S)

theorem mem_map_conj {H : Subgroup S} {g : S} :
    g ∈ H.map (MulAut.conj c).toMonoidHom ↔ c⁻¹ * g * c ∈ H := by
  constructor
  · rintro ⟨h, hh, rfl⟩
    change c⁻¹ * (c * h * c⁻¹) * c ∈ H
    rwa [show c⁻¹ * (c * h * c⁻¹) * c = h by group]
  · intro hg
    refine ⟨c⁻¹ * g * c, hg, ?_⟩
    change c * (c⁻¹ * g * c) * c⁻¹ = g
    group

end Conj

end CFSG.LocalAnalysis.ComponentInitial.PairedTensorOrbits
