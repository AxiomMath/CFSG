module

public import CFSG.Adapters.ProjectiveSpecialLinear
public import CFSG.LocalAnalysis.EvenBN.Common.SL2Module
public import CFSG.LocalAnalysis.QuasithinUnique.Constrained.Setup.SL2ModulesTensor
public import CFSG.ThirdParty.QiuzhenCFSG.BenderSuzuki.PFAppendixIII.Basic

public section

namespace CFSG.LieType.SpecialLinear

open scoped MatrixGroups
open CFSG.LinearGroups CFSG.LocalAnalysis.EvenBN.Common
open CFSG.QuasithinUnique.Setup.SL2Modules

variable {F : Type} [Field F] [Fintype F] [CharP F 2]
variable {Z : Type} [AddCommGroup Z] [Module (ZMod 2) Z] [Finite Z]

omit [Finite Z] in
theorem natCard_fixed_range {D : Type*} [Group D]
    (δ : Representation (ZMod 2) D Z) :
    Nat.card {z : Z // ∀ d, δ d z = z} =
      Nat.card {w : Z // ∀ a ∈ δ.toHomUnits.range, a.val w = w} := by
  refine Nat.card_congr ?_
  refine
    { toFun := fun z => ⟨z.1, fun a ha => ?_⟩
      invFun := fun w => ⟨w.1, fun d => ?_⟩
      left_inv := fun z => Subtype.ext rfl
      right_inv := fun w => Subtype.ext rfl }
  · obtain ⟨d, rfl⟩ := ha
    exact z.2 d
  · exact w.2 (δ.toHomUnits d) ⟨d, rfl⟩

omit [Finite Z] in
theorem natCard_ker_toHomUnits {D : Type*} [Group D]
    (δ : Representation (ZMod 2) D Z) :
    Nat.card δ.toHomUnits.ker = Nat.card δ.ker := by
  have h : δ.toHomUnits.ker = δ.ker := by
    ext d
    rw [MonoidHom.mem_ker, MonoidHom.mem_ker, Units.ext_iff,
      MonoidHom.coe_toHomUnits, Units.val_one]
  rw [h]

omit [Finite Z] in
theorem natCard_range_mul_ker {D : Type*} [Group D] [Finite D]
    (δ : Representation (ZMod 2) D Z) :
    Nat.card δ.toHomUnits.range * Nat.card δ.ker = Nat.card D := by
  have h := Subgroup.card_ker_mul_card_range δ.toHomUnits
  rw [natCard_ker_toHomUnits] at h
  rw [mul_comm]
  exact h

omit [Finite Z] in
theorem offender_image {D : Type*} [Group D] [Finite D]
    (δ : Representation (ZMod 2) D Z)
    (hoff : Nat.card Z * Nat.card δ.ker ≤
      Nat.card D * Nat.card {z : Z // ∀ d, δ d z = z}) :
    Nat.card Z ≤ Nat.card δ.toHomUnits.range *
      Nat.card {w : Z // ∀ a ∈ δ.toHomUnits.range, a.val w = w} := by
  rw [natCard_fixed_range] at hoff
  have hD := natCard_range_mul_ker δ
  have hker : 0 < Nat.card δ.ker := Nat.card_pos
  have hD' : Nat.card D = Nat.card δ.ker * Nat.card δ.toHomUnits.range := by
    rw [← hD, mul_comm]
  rw [hD', mul_assoc] at hoff
  exact Nat.le_of_mul_le_mul_left (by
    calc Nat.card δ.ker * Nat.card Z
        = Nat.card Z * Nat.card δ.ker := mul_comm _ _
      _ ≤ Nat.card δ.ker * (Nat.card δ.toHomUnits.range *
            Nat.card {w : Z // ∀ a ∈ δ.toHomUnits.range, a.val w = w}) := hoff) hker

end CFSG.LieType.SpecialLinear
