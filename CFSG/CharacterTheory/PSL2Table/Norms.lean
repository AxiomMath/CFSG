module

public import CFSG.CharacterTheory.PSL2Table.Series

public section

namespace CFSG.PSL2Table

open Matrix
open scoped MatrixGroups
open CFSG.TwoRankLowerBound.Helpers

variable {F : Type} [Field F] [Fintype F] [DecidableEq F]

section Sums

variable {G : Type} [Group G]

theorem sum_subgroup_of_const {H : Subgroup G} [Fintype H] {h : G → ℂ} {c : ℂ}
    (hc : ∀ x : H, x ≠ 1 → h x = c) : ∑ x : H, h x - h 1 = ((Nat.card H : ℂ) - 1) * c := by
  classical
  rw [← Finset.add_sum_erase _ _ (Finset.mem_univ (1 : H)),
    Finset.sum_congr rfl (fun x hx => hc x (Finset.ne_of_mem_erase hx)), Finset.sum_const,
    Finset.card_erase_of_mem (Finset.mem_univ _), Finset.card_univ, nsmul_eq_mul,
    Nat.card_eq_fintype_card, Nat.cast_sub Fintype.card_pos]
  push_cast
  ring

theorem sum_subgroup_of_agree {H : Subgroup G} [Fintype H] {h : G → ℂ} {k : H → ℂ}
    (hk : ∀ x : H, x ≠ 1 → h x = k x) : ∑ x : H, h x - h 1 = ∑ x : H, k x - k 1 := by
  classical
  rw [← Finset.add_sum_erase _ _ (Finset.mem_univ (1 : H)),
    ← Finset.add_sum_erase _ (fun x => k x) (Finset.mem_univ (1 : H)),
    Finset.sum_congr rfl (fun x hx => hk x (Finset.ne_of_mem_erase hx))]
  simp

end Sums

theorem card_mul_blocksInnerProduct (hF : ringChar F ≠ 2) (hq : 5 ≤ Fintype.card F) {ν : F}
    (hν : ¬ IsSquare ν) {f g : PSL(2, F) → ℂ} (hf : BlocksIsClassFunction f)
    (hg : BlocksIsClassFunction g) (fP gP : ℂ)
    (hfP : ∀ x ∈ unipotent F, x ≠ 1 → f x = fP) (hgP : ∀ x ∈ unipotent F, x ≠ 1 → g x = gP)
    (fT gT : splitTorus F → ℂ) (hfT : ∀ x : splitTorus F, x ≠ 1 → f x = fT x)
    (hgT : ∀ x : splitTorus F, x ≠ 1 → g x = gT x)
    (fS gS : nonsplitTorus ν → ℂ) (hfS : ∀ x : nonsplitTorus ν, x ≠ 1 → f x = fS x)
    (hgS : ∀ x : nonsplitTorus ν, x ≠ 1 → g x = gS x) :
    (Nat.card PSL(2, F) : ℂ) * BlocksInnerProduct f g =
      f 1 * starRingEnd ℂ (g 1) + ((Fintype.card F : ℂ) ^ 2 - 1) * (fP * starRingEnd ℂ gP) +
      ((Fintype.card F : ℂ) * (Fintype.card F + 1) / 2) *
        (∑ t, fT t * starRingEnd ℂ (gT t) - fT 1 * starRingEnd ℂ (gT 1)) +
      ((Fintype.card F : ℂ) * (Fintype.card F - 1) / 2) *
        (∑ s, fS s * starRingEnd ℂ (gS s) - fS 1 * starRingEnd ℂ (gS 1)) := by
  have hG0 : (Nat.card PSL(2, F) : ℂ) ≠ 0 := Nat.cast_ne_zero.mpr Nat.card_pos.ne'
  unfold BlocksInnerProduct
  rw [← mul_assoc, mul_inv_cancel₀ hG0, one_mul]
  have hclass : ∀ g' x : PSL(2, F),
      f (g' * x * g'⁻¹) * starRingEnd ℂ (g (g' * x * g'⁻¹)) = f x * starRingEnd ℂ (g x) := by
    intro g' x
    rw [hf x g', hg x g']
  rw [sum_classFunction hF hq hν _ hclass]
  have hP : ∑ x : unipotent F, f x * starRingEnd ℂ (g x) - f 1 * starRingEnd ℂ (g 1) =
      ((Fintype.card F : ℂ) - 1) * (fP * starRingEnd ℂ gP) := by
    have := sum_subgroup_of_const (H := unipotent F) (h := fun x => f x * starRingEnd ℂ (g x))
      (c := fP * starRingEnd ℂ gP) (fun x hx => by
        have hx' : (x : PSL(2, F)) ≠ 1 := fun h => hx (Subtype.ext h)
        rw [hfP x x.2 hx', hgP x x.2 hx'])
    rw [this, card_unipotent (Ring.two_ne_zero hF)]
  have hT : ∑ x : splitTorus F, f x * starRingEnd ℂ (g x) - f 1 * starRingEnd ℂ (g 1) =
      ∑ t, fT t * starRingEnd ℂ (gT t) - fT 1 * starRingEnd ℂ (gT 1) :=
    sum_subgroup_of_agree (H := splitTorus F) (h := fun x => f x * starRingEnd ℂ (g x))
      (k := fun t => fT t * starRingEnd ℂ (gT t)) (fun x hx => by
        rw [hfT x hx, hgT x hx])
  have hS : ∑ x : nonsplitTorus ν, f x * starRingEnd ℂ (g x) - f 1 * starRingEnd ℂ (g 1) =
      ∑ s, fS s * starRingEnd ℂ (gS s) - fS 1 * starRingEnd ℂ (gS 1) :=
    sum_subgroup_of_agree (H := nonsplitTorus ν) (h := fun x => f x * starRingEnd ℂ (g x))
      (k := fun s => fS s * starRingEnd ℂ (gS s)) (fun x hx => by
        rw [hfS x hx, hgS x hx])
  rw [hP, hT, hS]
  ring

omit [DecidableEq F] in
theorem card_PSL_complex (hF : ringChar F ≠ 2) :
    (Nat.card PSL(2, F) : ℂ) = Fintype.card F * ((Fintype.card F : ℂ) ^ 2 - 1) / 2 := by
  classical
  have hG := card_PSL (Ring.two_ne_zero hF) (F := F)
  have := congrArg (Nat.cast (R := ℂ)) hG
  push_cast [Nat.cast_sub (by nlinarith [Fintype.card_pos (α := F)] :
    1 ≤ Fintype.card F ^ 2)] at this
  linear_combination this / 2

omit [DecidableEq F] in
theorem card_splitTorus_complex (hF : ringChar F ≠ 2) :
    (Nat.card (splitTorus F) : ℂ) = ((Fintype.card F : ℂ) - 1) / 2 := by
  have hT := card_splitTorus (Ring.two_ne_zero hF) (F := F)
  have := congrArg (Nat.cast (R := ℂ)) hT
  push_cast [Nat.cast_sub (Fintype.card_pos (α := F))] at this
  linear_combination this / 2

omit [DecidableEq F] in
theorem card_nonsplitTorus_complex (hF : ringChar F ≠ 2) {ν : F} (hν : ¬ IsSquare ν) :
    (Nat.card (nonsplitTorus ν) : ℂ) = ((Fintype.card F : ℂ) + 1) / 2 := by
  have hS := card_nonsplitTorus hF hν
  have := congrArg (Nat.cast (R := ℂ)) hS
  push_cast at this
  linear_combination this / 2

omit [DecidableEq F] in
theorem card_PSL_complex_ne_zero : (Nat.card PSL(2, F) : ℂ) ≠ 0 :=
  Nat.cast_ne_zero.mpr Nat.card_pos.ne'

theorem one_isClassFunction {G : Type} [Group G] : BlocksIsClassFunction (1 : G → ℂ) :=
  fun _ _ => rfl

theorem principal_profileT (α : splitTorus F →* ℂˣ) :
    ∀ x : splitTorus F, x ≠ 1 → principal α x = (α x : ℂ) + (α x⁻¹ : ℂ) := by
  intro x hx
  have hx' : (x : PSL(2, F)) ≠ 1 := fun h => hx (Subtype.ext h)
  rw [principal_of_mem_splitTorus α x.2 hx']

theorem discrete_profileS (hF : ringChar F ≠ 2) {ν : F} (hν : ¬ IsSquare ν)
    (β : nonsplitTorus ν →* ℂˣ) :
    ∀ x : nonsplitTorus ν, x ≠ 1 → discrete β x = -((β x : ℂ) + (β x⁻¹ : ℂ)) := by
  intro x hx
  have hx' : (x : PSL(2, F)) ≠ 1 := fun h => hx (Subtype.ext h)
  rw [discrete_of_mem_nonsplitTorus hF hν β x.2 hx']

theorem principal_inner (hF : ringChar F ≠ 2) (hq : 5 ≤ Fintype.card F) {ν : F}
    (hν : ¬ IsSquare ν) (α α' : splitTorus F →* ℂˣ) :
    BlocksInnerProduct (principal α) (principal α') =
      (if α = α' then 1 else 0) + (if α = α'⁻¹ then 1 else 0) := by
  have h := card_mul_blocksInnerProduct hF hq hν
    (blocksVChar_isClassFunction (principal_mem_blocksVChar α))
    (blocksVChar_isClassFunction (principal_mem_blocksVChar α')) 1 1
    (fun x hx hx1 => principal_of_mem_unipotent hF α hx hx1)
    (fun x hx hx1 => principal_of_mem_unipotent hF α' hx hx1)
    _ _ (principal_profileT α) (principal_profileT α') 0 0
    (fun x hx => principal_of_mem_nonsplitTorus hF hν α x.2 (fun h => hx (Subtype.ext h)))
    (fun x hx => principal_of_mem_nonsplitTorus hF hν α' x.2 (fun h => hx (Subtype.ext h)))
  rw [sum_torus_pair, principal_one hF, principal_one hF, card_splitTorus_complex hF,
    card_PSL_complex hF] at h
  simp only [inv_one, map_one, Units.val_one, Pi.zero_apply, map_zero, mul_zero,
    Finset.sum_const_zero, sub_zero, map_add, map_natCast, one_mul] at h
  apply mul_left_cancel₀ (card_PSL_complex_ne_zero (F := F))
  rw [card_PSL_complex hF, h]
  ring

theorem discrete_inner (hF : ringChar F ≠ 2) (hq : 5 ≤ Fintype.card F) {ν : F}
    (hν : ¬ IsSquare ν) (β β' : nonsplitTorus ν →* ℂˣ) :
    BlocksInnerProduct (discrete β) (discrete β') =
      (if β = β' then 1 else 0) + (if β = β'⁻¹ then 1 else 0) := by
  have h := card_mul_blocksInnerProduct hF hq hν
    (blocksVChar_isClassFunction (discrete_mem_blocksVChar β))
    (blocksVChar_isClassFunction (discrete_mem_blocksVChar β')) (-1) (-1)
    (fun x hx hx1 => discrete_of_mem_unipotent hF hν β hx hx1)
    (fun x hx hx1 => discrete_of_mem_unipotent hF hν β' hx hx1)
    0 0
    (fun x hx => discrete_of_mem_splitTorus hF hν β x.2 (fun h => hx (Subtype.ext h)))
    (fun x hx => discrete_of_mem_splitTorus hF hν β' x.2 (fun h => hx (Subtype.ext h)))
    _ _ (discrete_profileS hF hν β) (discrete_profileS hF hν β')
  simp only [map_neg, neg_mul_neg] at h
  rw [sum_torus_pair, discrete_one hF hν, discrete_one hF hν, card_nonsplitTorus_complex hF hν,
    card_PSL_complex hF] at h
  simp only [inv_one, map_one, Units.val_one, Pi.zero_apply, map_zero, mul_zero,
    Finset.sum_const_zero, sub_zero, map_add, map_natCast, map_sub, mul_one] at h
  apply mul_left_cancel₀ (card_PSL_complex_ne_zero (F := F))
  rw [card_PSL_complex hF, h]
  ring

omit [DecidableEq F] in
theorem sum_const_one_subgroup {G : Type} [Group G] (H : Subgroup G) [Fintype H] :
    ∑ _x : H, (1 : ℂ) = Nat.card H := by
  rw [Finset.sum_const, Finset.card_univ, Nat.card_eq_fintype_card, nsmul_eq_mul, mul_one]

theorem steinberg_inner_self (hF : ringChar F ≠ 2) (hq : 5 ≤ Fintype.card F) {ν : F}
    (hν : ¬ IsSquare ν) : BlocksInnerProduct (steinberg F) (steinberg F) = 1 := by
  have h := card_mul_blocksInnerProduct hF hq hν
    (blocksVChar_isClassFunction steinberg_mem_blocksVChar)
    (blocksVChar_isClassFunction steinberg_mem_blocksVChar) 0 0
    (fun x hx hx1 => steinberg_of_mem_unipotent hF hx hx1)
    (fun x hx hx1 => steinberg_of_mem_unipotent hF hx hx1)
    (fun _ => 1) (fun _ => 1)
    (fun x hx => steinberg_of_mem_splitTorus x.2 (fun h => hx (Subtype.ext h)))
    (fun x hx => steinberg_of_mem_splitTorus x.2 (fun h => hx (Subtype.ext h)))
    (fun _ => -1) (fun _ => -1)
    (fun x hx => steinberg_of_mem_nonsplitTorus hν x.2 (fun h => hx (Subtype.ext h)))
    (fun x hx => steinberg_of_mem_nonsplitTorus hν x.2 (fun h => hx (Subtype.ext h)))
  simp only [map_one, map_neg, mul_one, neg_mul_neg, map_zero, mul_zero, sum_const_one_subgroup,
    steinberg_one, map_natCast] at h
  rw [card_splitTorus_complex hF, card_nonsplitTorus_complex hF hν, card_PSL_complex hF] at h
  apply mul_left_cancel₀ (card_PSL_complex_ne_zero (F := F))
  rw [card_PSL_complex hF, h]
  ring

theorem steinberg_inner_one (hF : ringChar F ≠ 2) (hq : 5 ≤ Fintype.card F) {ν : F}
    (hν : ¬ IsSquare ν) : BlocksInnerProduct (steinberg F) 1 = 0 := by
  have h := card_mul_blocksInnerProduct hF hq hν
    (blocksVChar_isClassFunction steinberg_mem_blocksVChar) one_isClassFunction 0 1
    (fun x hx hx1 => steinberg_of_mem_unipotent hF hx hx1) (fun _ _ _ => rfl)
    (fun _ => 1) (fun _ => 1)
    (fun x hx => steinberg_of_mem_splitTorus x.2 (fun h => hx (Subtype.ext h))) (fun _ _ => rfl)
    (fun _ => -1) (fun _ => 1)
    (fun x hx => steinberg_of_mem_nonsplitTorus hν x.2 (fun h => hx (Subtype.ext h)))
    (fun _ _ => rfl)
  simp only [map_one, mul_one, Pi.one_apply, steinberg_one, Finset.sum_neg_distrib,
    sum_const_one_subgroup] at h
  rw [card_splitTorus_complex hF, card_nonsplitTorus_complex hF hν] at h
  apply mul_left_cancel₀ (card_PSL_complex_ne_zero (F := F))
  rw [h, mul_zero]
  ring

theorem principal_inner_discrete (hF : ringChar F ≠ 2) (hq : 5 ≤ Fintype.card F) {ν : F}
    (hν : ¬ IsSquare ν) (α : splitTorus F →* ℂˣ) (β : nonsplitTorus ν →* ℂˣ) :
    BlocksInnerProduct (principal α) (discrete β) = 0 := by
  have h := card_mul_blocksInnerProduct hF hq hν
    (blocksVChar_isClassFunction (principal_mem_blocksVChar α))
    (blocksVChar_isClassFunction (discrete_mem_blocksVChar β)) 1 (-1)
    (fun x hx hx1 => principal_of_mem_unipotent hF α hx hx1)
    (fun x hx hx1 => discrete_of_mem_unipotent hF hν β hx hx1)
    _ 0 (principal_profileT α)
    (fun x hx => discrete_of_mem_splitTorus hF hν β x.2 (fun h => hx (Subtype.ext h)))
    0 _
    (fun x hx => principal_of_mem_nonsplitTorus hF hν α x.2 (fun h => hx (Subtype.ext h)))
    (discrete_profileS hF hν β)
  simp only [Pi.zero_apply, map_zero, mul_zero, zero_mul, neg_zero, sub_zero,
    Finset.sum_const_zero, principal_one hF, discrete_one hF hν, map_neg, map_one, mul_neg,
    mul_one, map_sub, map_add, map_natCast] at h
  apply mul_left_cancel₀ (card_PSL_complex_ne_zero (F := F))
  rw [h, mul_zero]
  ring

theorem principal_inner_one (hF : ringChar F ≠ 2) (hq : 5 ≤ Fintype.card F) {ν : F}
    (hν : ¬ IsSquare ν) (α : splitTorus F →* ℂˣ) :
    BlocksInnerProduct (principal α) 1 = if α = 1 then 1 else 0 := by
  have h := card_mul_blocksInnerProduct hF hq hν
    (blocksVChar_isClassFunction (principal_mem_blocksVChar α)) one_isClassFunction 1 1
    (fun x hx hx1 => principal_of_mem_unipotent hF α hx hx1) (fun _ _ _ => rfl)
    _ (fun _ => 1) (principal_profileT α) (fun _ _ => rfl)
    0 (fun _ => 1)
    (fun x hx => principal_of_mem_nonsplitTorus hF hν α x.2 (fun h => hx (Subtype.ext h)))
    (fun _ _ => rfl)
  simp only [map_one, mul_one, Pi.one_apply, Pi.zero_apply, Finset.sum_const_zero,
    sub_zero, principal_one hF, sum_torus_single, inv_one, Units.val_one] at h
  rw [card_splitTorus_complex hF] at h
  apply mul_left_cancel₀ (card_PSL_complex_ne_zero (F := F))
  rw [h, card_PSL_complex hF]
  split_ifs <;> ring

theorem principal_inner_steinberg (hF : ringChar F ≠ 2) (hq : 5 ≤ Fintype.card F) {ν : F}
    (hν : ¬ IsSquare ν) (α : splitTorus F →* ℂˣ) :
    BlocksInnerProduct (principal α) (steinberg F) = if α = 1 then 1 else 0 := by
  have h := card_mul_blocksInnerProduct hF hq hν
    (blocksVChar_isClassFunction (principal_mem_blocksVChar α))
    (blocksVChar_isClassFunction steinberg_mem_blocksVChar) 1 0
    (fun x hx hx1 => principal_of_mem_unipotent hF α hx hx1)
    (fun x hx hx1 => steinberg_of_mem_unipotent hF hx hx1)
    _ (fun _ => 1) (principal_profileT α)
    (fun x hx => steinberg_of_mem_splitTorus x.2 (fun h => hx (Subtype.ext h)))
    0 (fun _ => -1)
    (fun x hx => principal_of_mem_nonsplitTorus hF hν α x.2 (fun h => hx (Subtype.ext h)))
    (fun x hx => steinberg_of_mem_nonsplitTorus hν x.2 (fun h => hx (Subtype.ext h)))
  simp only [map_one, mul_one, Pi.zero_apply, zero_mul, Finset.sum_const_zero, map_zero,
    mul_zero, sub_zero, principal_one hF, steinberg_one, sum_torus_single, inv_one,
    Units.val_one, map_natCast] at h
  rw [card_splitTorus_complex hF] at h
  apply mul_left_cancel₀ (card_PSL_complex_ne_zero (F := F))
  rw [h, card_PSL_complex hF]
  split_ifs <;> ring

theorem discrete_inner_one (hF : ringChar F ≠ 2) (hq : 5 ≤ Fintype.card F) {ν : F}
    (hν : ¬ IsSquare ν) (β : nonsplitTorus ν →* ℂˣ) :
    BlocksInnerProduct (discrete β) 1 = -(if β = 1 then 1 else 0) := by
  have h := card_mul_blocksInnerProduct hF hq hν
    (blocksVChar_isClassFunction (discrete_mem_blocksVChar β)) one_isClassFunction (-1) 1
    (fun x hx hx1 => discrete_of_mem_unipotent hF hν β hx hx1) (fun _ _ _ => rfl)
    0 (fun _ => 1)
    (fun x hx => discrete_of_mem_splitTorus hF hν β x.2 (fun h => hx (Subtype.ext h)))
    (fun _ _ => rfl)
    _ (fun _ => 1) (discrete_profileS hF hν β) (fun _ _ => rfl)
  simp only [map_one, mul_one, Pi.one_apply, Pi.zero_apply, Finset.sum_const_zero,
    sub_zero, discrete_one hF hν, Finset.sum_neg_distrib, sum_torus_single, inv_one,
    Units.val_one] at h
  rw [card_nonsplitTorus_complex hF hν] at h
  apply mul_left_cancel₀ (card_PSL_complex_ne_zero (F := F))
  rw [h, card_PSL_complex hF]
  split_ifs <;> ring

theorem discrete_inner_steinberg (hF : ringChar F ≠ 2) (hq : 5 ≤ Fintype.card F) {ν : F}
    (hν : ¬ IsSquare ν) (β : nonsplitTorus ν →* ℂˣ) :
    BlocksInnerProduct (discrete β) (steinberg F) = if β = 1 then 1 else 0 := by
  have h := card_mul_blocksInnerProduct hF hq hν
    (blocksVChar_isClassFunction (discrete_mem_blocksVChar β))
    (blocksVChar_isClassFunction steinberg_mem_blocksVChar) (-1) 0
    (fun x hx hx1 => discrete_of_mem_unipotent hF hν β hx hx1)
    (fun x hx hx1 => steinberg_of_mem_unipotent hF hx hx1)
    0 (fun _ => 1)
    (fun x hx => discrete_of_mem_splitTorus hF hν β x.2 (fun h => hx (Subtype.ext h)))
    (fun x hx => steinberg_of_mem_splitTorus x.2 (fun h => hx (Subtype.ext h)))
    _ (fun _ => -1) (discrete_profileS hF hν β)
    (fun x hx => steinberg_of_mem_nonsplitTorus hν x.2 (fun h => hx (Subtype.ext h)))
  simp only [map_one, mul_one, Pi.zero_apply, Finset.sum_const_zero, map_zero,
    mul_zero, sub_zero, discrete_one hF hν, steinberg_one, map_neg,
    sum_torus_single, inv_one, Units.val_one, map_natCast, mul_neg, neg_neg] at h
  rw [card_nonsplitTorus_complex hF hν] at h
  apply mul_left_cancel₀ (card_PSL_complex_ne_zero (F := F))
  rw [h, card_PSL_complex hF]
  split_ifs <;> ring

end CFSG.PSL2Table
