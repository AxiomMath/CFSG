module

public import CFSG.LargeExtraspecial.DWTrans
public import CFSG.LargeExtraspecial.DWModelSplit

public section

attribute [-instance] instAddCommGroupOfIsSimpleAddGroupOfIsNilpotent
  instCommGroupOfIsSimpleGroupOfIsNilpotent

namespace CFSG.LargeExtraspecial.DW

open Subgroup Module QuadraticMap CFSG.GroupTheory.GLnTwoSplitting
open scoped IsMulCommutative

variable {G : Type*} [Group G]

abbrev AN (A : Subgroup G) : Subgroup (normalizer (A : Set G)) :=
  A.subgroupOf (normalizer (A : Set G))

variable {A : Subgroup G}

abbrev elt (x : Additive (AN A)) : G := ((Additive.toMul x : AN A) : normalizer (A : Set G))

theorem elt_mem (x : Additive (AN A)) : elt x ∈ A := (Additive.toMul x).2

abbrev vec {a : G} (ha : a ∈ A) : Additive (AN A) :=
  Additive.ofMul ⟨⟨a, le_normalizer ha⟩, ha⟩

@[simp] theorem elt_vec {a : G} (ha : a ∈ A) : elt (vec ha) = a := rfl

theorem elt_add (x y : Additive (AN A)) : elt (x + y) = elt x * elt y := rfl

theorem elt_zero : elt (0 : Additive (AN A)) = 1 := rfl

theorem elt_injective : Function.Injective (elt (A := A)) := fun _ _ h =>
  Additive.toMul.injective (Subtype.ext (Subtype.ext h))

variable [IsElementaryAbelian 2 A]

theorem elt_conjLinear (g : normalizer (A : Set G)) (x : Additive (AN A)) :
    elt (conjLinear (AN A) g x) = (g : G) * elt x * (g : G)⁻¹ := by
  rw [elt, coe_conjLinear_apply]
  rfl

theorem elt_smul (c : ZMod 2) (x : Additive (AN A)) :
    elt (c • x) = if c = 0 then 1 else elt x := by
  rcases zmod_two_eq_zero_or_one c with rfl | rfl
  · simp [elt_zero]
  · simp

theorem conjLinear_eq_transvection_iff (g : normalizer (A : Set G))
    {f : Dual (ZMod 2) (Additive (AN A))} {d : Additive (AN A)} (hf : f d = 0) :
    conjLinear (AN A) g = LinearEquiv.transvection hf ↔
      ∀ x, (g : G) * elt x * (g : G)⁻¹ = if f x = 0 then elt x else elt x * elt d := by
  constructor
  · intro h x
    rw [← elt_conjLinear, h, transvection_apply, elt_add, elt_smul]
    split_ifs <;> simp
  · intro h
    refine LinearEquiv.ext fun x => elt_injective ?_
    rw [elt_conjLinear, h, transvection_apply, elt_add, elt_smul]
    split_ifs <;> simp

namespace MaxEA

variable {S : Setting G} (hA : MaxEA S A)
include hA

@[expose] noncomputable def clMap : Additive (AN A) →ₗ[ZMod 2] S.Qt :=
  AddMonoidHom.toZModLinearMap 2
    { toFun := fun x => S.cl (elt x)
      map_zero' := S.cl_one
      map_add' := fun x y => S.cl_mul (hA.le_QG (elt_mem x)) (hA.le_QG (elt_mem y)) }

theorem clMap_apply (x : Additive (AN A)) : hA.clMap x = S.cl (elt x) := rfl

variable [Finite G]

abbrev zVec : Additive (AN A) := vec hA.z_mem

theorem clMap_eq_zero_iff (x : Additive (AN A)) : hA.clMap x = 0 ↔ x = 0 ∨ x = hA.zVec := by
  rw [clMap_apply, S.cl_eq_zero_iff (hA.le_QG (elt_mem x))]
  constructor
  · rintro (h | h)
    · exact Or.inl (elt_injective h)
    · exact Or.inr (elt_injective h)
  · rintro (rfl | rfl)
    · exact Or.inl rfl
    · exact Or.inr rfl

theorem clMap_zVec : hA.clMap hA.zVec = 0 := (hA.clMap_eq_zero_iff _).mpr (Or.inr rfl)

theorem conjLinear_QG {q : G} (hq : q ∈ S.QG) {f : Dual (ZMod 2) (Additive (AN A))}
    (hfz : f hA.zVec = 0) (hf : ∀ x, f x = polar S.q (hA.clMap x) (S.cl q)) :
    conjLinear (AN A) ⟨q, hA.QG_le_normalizer hq⟩ = LinearEquiv.transvection hfz := by
  rw [conjLinear_eq_transvection_iff]
  intro x
  rw [hA.conj_eq hq (elt_mem x), hf, clMap_apply]
  rfl

theorem exists_conjLinear_eq_transvection {f : Dual (ZMod 2) (Additive (AN A))}
    (hfz : f hA.zVec = 0) :
    ∃ q, ∃ hq : q ∈ S.QG,
      conjLinear (AN A) ⟨q, hA.QG_le_normalizer hq⟩ = LinearEquiv.transvection hfz := by
  have : Finite (Additive S.Q) := inferInstanceAs (Finite S.Q)
  have : FiniteDimensional (ZMod 2) S.Qt := Module.Finite.of_finite
  obtain ⟨w, hw⟩ := exists_eval_of_ker_le (E := S.Qt) (S.q.polarBilin.comp hA.clMap) f
    (fun x hx => by
      have h0 : hA.clMap x = 0 := S.q_nondegenerate.1 _ fun v => by
        have := LinearMap.congr_fun hx v
        simpa using this
      rcases (hA.clMap_eq_zero_iff x).mp h0 with rfl | rfl
      · exact map_zero f
      · exact hfz)
  obtain ⟨q, hq, rfl⟩ := S.exists_cl w
  exact ⟨q, hq, hA.conjLinear_QG hq hfz fun x => by rw [hw x]; rfl⟩

end MaxEA

end CFSG.LargeExtraspecial.DW
