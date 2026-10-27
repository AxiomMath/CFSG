module

public import CFSG.CharacterTheory.PSL2Table.Induced
public import CFSG.CharacterTheory.Wreathed.CentralSL2.InducedStabilizer

public section

namespace CFSG.PSL2Table

open Matrix
open scoped MatrixGroups
open CFSG.TwoRankLowerBound.Helpers

section Linear

variable {K : Type} [Group K] [Fintype K]

theorem sum_mul_conj_units_hom (χ χ' : K →* ℂˣ) :
    ∑ k, (χ k : ℂ) * starRingEnd ℂ (χ' k : ℂ) = if χ = χ' then (Nat.card K : ℂ) else 0 := by
  have h := CFSG.Wreathed.CentralSL2.blocksInnerProduct_units_hom χ χ'
  unfold BlocksInnerProduct at h
  have hK : (Nat.card K : ℂ) ≠ 0 := Nat.cast_ne_zero.mpr Nat.card_pos.ne'
  rw [inv_mul_eq_iff_eq_mul₀ hK] at h
  rw [h]
  split_ifs <;> ring

omit [Fintype K] in
theorem units_hom_apply_inv (χ : K →* ℂˣ) (k : K) : (χ k⁻¹ : ℂ) = (χ⁻¹ k : ℂ) := by
  rw [map_inv, MonoidHom.inv_apply]

theorem sum_units_hom (χ : K →* ℂˣ) : ∑ k, (χ k : ℂ) = if χ = 1 then (Nat.card K : ℂ) else 0 := by
  have h := sum_mul_conj_units_hom χ 1
  simp only [MonoidHom.one_apply, Units.val_one, map_one, mul_one] at h
  exact h

theorem sum_torus_pair (χ χ' : K →* ℂˣ) :
    ∑ k, ((χ k : ℂ) + (χ k⁻¹ : ℂ)) * starRingEnd ℂ ((χ' k : ℂ) + (χ' k⁻¹ : ℂ)) =
      2 * (Nat.card K : ℂ) * ((if χ = χ' then 1 else 0) + (if χ = χ'⁻¹ then 1 else 0)) := by
  simp only [units_hom_apply_inv, map_add, add_mul, mul_add, Finset.sum_add_distrib,
    sum_mul_conj_units_hom]
  have e1 : (χ⁻¹ = χ') ↔ (χ = χ'⁻¹) := by
    constructor
    · intro h
      ext k
      rw [← h, MonoidHom.inv_apply, MonoidHom.inv_apply, inv_inv]
    · intro h
      ext k
      rw [h, MonoidHom.inv_apply, MonoidHom.inv_apply, inv_inv]
  have e2 : (χ⁻¹ = χ'⁻¹) ↔ (χ = χ') := by
    constructor
    · intro h
      ext k
      have := congrArg (fun f : K →* ℂˣ => ((f k)⁻¹ : ℂˣ)) h
      simp only [MonoidHom.inv_apply, inv_inv] at this
      rw [this]
    · rintro rfl
      rfl
  simp only [e1, e2]
  split_ifs <;> ring

theorem sum_torus_single (χ : K →* ℂˣ) :
    ∑ k, ((χ k : ℂ) + (χ k⁻¹ : ℂ)) = 2 * (Nat.card K : ℂ) * (if χ = 1 then 1 else 0) := by
  simp only [units_hom_apply_inv, Finset.sum_add_distrib, sum_units_hom]
  have e : χ⁻¹ = 1 ↔ χ = 1 := by
    constructor
    · intro h
      ext k
      have := congrArg (fun f : K →* ℂˣ => ((f k)⁻¹ : ℂˣ)) h
      simp only [MonoidHom.inv_apply, inv_inv, MonoidHom.one_apply, inv_one] at this
      rw [this, MonoidHom.one_apply]
    · rintro rfl
      ext k
      simp
  simp only [e]
  split_ifs <;> ring

end Linear

variable {F : Type} [Field F] [Fintype F] [DecidableEq F]

@[expose] noncomputable def gammaChar (F : Type) [Field F] [Fintype F] [DecidableEq F] :
    PSL(2, F) → ℂ :=
  indSplit 1 - permChar F

@[expose] noncomputable def steinberg (F : Type) [Field F] [Fintype F] : PSL(2, F) → ℂ :=
  permChar F - 1

@[expose] noncomputable def principal (α : splitTorus F →* ℂˣ) : PSL(2, F) → ℂ :=
  indSplit α - gammaChar F

@[expose] noncomputable def discrete {ν : F} (β : nonsplitTorus ν →* ℂˣ) : PSL(2, F) → ℂ :=
  gammaChar F - indNonsplit β

theorem gammaChar_mem_blocksVChar : gammaChar F ∈ BlocksVChar PSL(2, F) :=
  AddSubgroup.sub_mem _ (indSplit_mem_blocksVChar 1) permChar_mem_blocksVChar

theorem steinberg_mem_blocksVChar : steinberg F ∈ BlocksVChar PSL(2, F) :=
  AddSubgroup.sub_mem _ permChar_mem_blocksVChar (blocksVChar_one _)

theorem principal_mem_blocksVChar (α : splitTorus F →* ℂˣ) :
    principal α ∈ BlocksVChar PSL(2, F) :=
  AddSubgroup.sub_mem _ (indSplit_mem_blocksVChar α) gammaChar_mem_blocksVChar

theorem discrete_mem_blocksVChar {ν : F} (β : nonsplitTorus ν →* ℂˣ) :
    discrete β ∈ BlocksVChar PSL(2, F) :=
  AddSubgroup.sub_mem _ gammaChar_mem_blocksVChar (indNonsplit_mem_blocksVChar β)

section Values

variable (hF : ringChar F ≠ 2) (hq : 5 ≤ Fintype.card F) {ν : F} (hν : ¬ IsSquare ν)
include hF

omit hF [DecidableEq F] in
theorem steinberg_one : steinberg F 1 = Fintype.card F := by
  rw [steinberg, Pi.sub_apply, permChar_one, Pi.one_apply]
  ring

omit [DecidableEq F] in
theorem steinberg_of_mem_unipotent {x : PSL(2, F)} (hx : x ∈ unipotent F) (hx1 : x ≠ 1) :
    steinberg F x = 0 := by
  rw [steinberg, Pi.sub_apply, permChar_of_mem_unipotent (Ring.two_ne_zero hF) hx hx1,
    Pi.one_apply, sub_self]

omit hF [DecidableEq F] in
theorem steinberg_of_mem_splitTorus {x : PSL(2, F)} (hx : x ∈ splitTorus F) (hx1 : x ≠ 1) :
    steinberg F x = 1 := by
  rw [steinberg, Pi.sub_apply, permChar_of_mem_splitTorus hx hx1, Pi.one_apply]
  norm_num

omit hF [DecidableEq F] in
include hν in
theorem steinberg_of_mem_nonsplitTorus {x : PSL(2, F)} (hx : x ∈ nonsplitTorus ν)
    (hx1 : x ≠ 1) : steinberg F x = -1 := by
  rw [steinberg, Pi.sub_apply, permChar_of_mem_nonsplitTorus hν hx hx1, Pi.one_apply]
  norm_num

theorem gammaChar_one : gammaChar F 1 = (Fintype.card F : ℂ) ^ 2 - 1 := by
  rw [gammaChar, Pi.sub_apply, indSplit_one hF, permChar_one]
  ring

theorem gammaChar_of_mem_unipotent {x : PSL(2, F)} (hx : x ∈ unipotent F) (hx1 : x ≠ 1) :
    gammaChar F x = -1 := by
  rw [gammaChar, Pi.sub_apply, indSplit_of_mem_conjSet_unipotent hF _
    (mem_conjSet_of_mem hx hx1), permChar_of_mem_unipotent (Ring.two_ne_zero hF) hx hx1]
  ring

omit hF in
theorem gammaChar_of_mem_splitTorus {x : PSL(2, F)} (hx : x ∈ splitTorus F) (hx1 : x ≠ 1) :
    gammaChar F x = 0 := by
  rw [gammaChar, Pi.sub_apply, indSplit_apply_of_mem hx hx1, permChar_of_mem_splitTorus hx hx1]
  simp only [MonoidHom.one_apply, Units.val_one]
  norm_num

include hν in
theorem gammaChar_of_mem_nonsplitTorus {x : PSL(2, F)} (hx : x ∈ nonsplitTorus ν)
    (hx1 : x ≠ 1) : gammaChar F x = 0 := by
  rw [gammaChar, Pi.sub_apply, indSplit_of_mem_conjSet_nonsplit hF _ hν
    (mem_conjSet_of_mem hx hx1), permChar_of_mem_nonsplitTorus hν hx hx1, sub_zero]

theorem principal_one (α : splitTorus F →* ℂˣ) : principal α 1 = Fintype.card F + 1 := by
  rw [principal, Pi.sub_apply, indSplit_one hF, gammaChar_one hF]
  ring

theorem principal_of_mem_unipotent (α : splitTorus F →* ℂˣ) {x : PSL(2, F)}
    (hx : x ∈ unipotent F) (hx1 : x ≠ 1) : principal α x = 1 := by
  rw [principal, Pi.sub_apply, indSplit_of_mem_conjSet_unipotent hF _
    (mem_conjSet_of_mem hx hx1), gammaChar_of_mem_unipotent hF hx hx1]
  ring

omit hF in
theorem principal_of_mem_splitTorus (α : splitTorus F →* ℂˣ) {x : PSL(2, F)}
    (hx : x ∈ splitTorus F) (hx1 : x ≠ 1) :
    principal α x = (α ⟨x, hx⟩ : ℂ) + (α ⟨x, hx⟩⁻¹ : ℂ) := by
  rw [principal, Pi.sub_apply, indSplit_apply_of_mem hx hx1, gammaChar_of_mem_splitTorus hx hx1,
    sub_zero]

include hν in
theorem principal_of_mem_nonsplitTorus (α : splitTorus F →* ℂˣ) {x : PSL(2, F)}
    (hx : x ∈ nonsplitTorus ν) (hx1 : x ≠ 1) : principal α x = 0 := by
  rw [principal, Pi.sub_apply, indSplit_of_mem_conjSet_nonsplit hF _ hν
    (mem_conjSet_of_mem hx hx1), gammaChar_of_mem_nonsplitTorus hF hν hx hx1, sub_zero]

include hν in
theorem discrete_one (β : nonsplitTorus ν →* ℂˣ) : discrete β 1 = Fintype.card F - 1 := by
  rw [discrete, Pi.sub_apply, indNonsplit_one hF hν, gammaChar_one hF]
  ring

include hν in
theorem discrete_of_mem_unipotent (β : nonsplitTorus ν →* ℂˣ) {x : PSL(2, F)}
    (hx : x ∈ unipotent F) (hx1 : x ≠ 1) : discrete β x = -1 := by
  rw [discrete, Pi.sub_apply, indNonsplit_of_mem_conjSet_unipotent hF hν _
    (mem_conjSet_of_mem hx hx1), gammaChar_of_mem_unipotent hF hx hx1, sub_zero]

include hν in
theorem discrete_of_mem_splitTorus (β : nonsplitTorus ν →* ℂˣ) {x : PSL(2, F)}
    (hx : x ∈ splitTorus F) (hx1 : x ≠ 1) : discrete β x = 0 := by
  rw [discrete, Pi.sub_apply, indNonsplit_of_mem_conjSet_split hF hν _
    (mem_conjSet_of_mem hx hx1), gammaChar_of_mem_splitTorus hx hx1, sub_zero]

include hν in
theorem discrete_of_mem_nonsplitTorus (β : nonsplitTorus ν →* ℂˣ) {x : PSL(2, F)}
    (hx : x ∈ nonsplitTorus ν) (hx1 : x ≠ 1) :
    discrete β x = -((β ⟨x, hx⟩ : ℂ) + (β ⟨x, hx⟩⁻¹ : ℂ)) := by
  rw [discrete, Pi.sub_apply, indNonsplit_apply_of_mem hF hν hx hx1,
    gammaChar_of_mem_nonsplitTorus hF hν hx hx1, zero_sub]

end Values

end CFSG.PSL2Table
