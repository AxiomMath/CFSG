module

public import CFSG.LocalAnalysis.ProperTwoGeneratedCore.LocalCriterionCosetNormalizerIndexOddInvolutions
public import CFSG.LocalAnalysis.ProperTwoGeneratedCore.LocalCriterionOddQuotientLifting
public import CFSG.LocalAnalysis.ShultStronglyClosedTI.MinimalLocalFailureLocalThetaCentralExtension

public noncomputable section

namespace CFSG.ProperTwoGeneratedCore.LocalCriterionNumerator

open CFSG.ShultStronglyClosedTI.LocalTheta
open CFSG.ProperTwoGeneratedCore.LocalCriterionCosetNormalizerIndex
open CFSG.BenderSuzuki.PFAppendixIII
open scoped IsMulCommutative

universe u v

variable {G : Type u} {F : Type v} [Group G] [Finite G] [Group F]

theorem square_one_commutes_of_central_odd_kernel_image
    (f : G →* F) (hodd : Odd (Nat.card f.ker))
    (hcentral : f.ker ≤ Subgroup.center G)
    (x y : G) (hy : y ^ 2 = 1) (hcomm : Commute (f x) (f y)) : Commute x y := by
  have hconj : (x * y * x⁻¹) ^ 2 = 1 := by
    calc
      _ = x * (y ^ 2) * x⁻¹ := by simp only [pow_two]; group
      _ = 1 := by rw [hy]; group
  have hmap : f (x * y * x⁻¹) = f y := by
    rw [map_mul, map_mul, map_inv, hcomm.eq, mul_assoc, mul_inv_cancel, mul_one]
  have heq := square_one_injective_of_central_odd_kernel f hodd hcentral hconj hy hmap
  have hmul := congrArg (fun a : G => a * x) heq
  change x * y = y * x
  simpa only [mul_assoc, inv_mul_cancel, mul_one] using hmul

theorem whole_point_involution_root_of_central_odd_surjection
    (f : G →* F) (_hf : Function.Surjective f)
    (hodd : Odd (Nat.card f.ker)) (hcentral : f.ker ≤ Subgroup.center G)
    (P : Subgroup G) (B U : Subgroup F) (hPB : P.map f = B)
    (hU : IsElementaryAbelian 2 U)
    (hUset : (U : Set F) = {1} ∪ {x : F | x ∈ B ∧ IsInvolution x}) :
    let V := Subgroup.closure {x : G | x ∈ P ∧ IsInvolution x}
    IsElementaryAbelian 2 V ∧ V ≤ P ∧ V.map f = U ∧
      Function.Injective (f.comp V.subtype) ∧
      (V : Set G) = {1} ∪ {x : G | x ∈ P ∧ IsInvolution x} ∧
      Nat.card V = Nat.card U := by
  let s : Set G := {x : G | x ∈ P ∧ IsInvolution x}
  let V := Subgroup.closure s
  have himage (x : G) (hx : x ∈ s) : f x ∈ U := by
    change f x ∈ (U : Set F)
    rw [hUset]
    exact Or.inr ⟨hPB ▸ Subgroup.mem_map_of_mem f hx.1,
      involution_map_of_odd_kernel f hodd hx.2⟩
  have hcomm : s.Pairwise Commute := by
    intro x hx y hy _hne
    let : IsElementaryAbelian 2 U := hU
    have hquot : Commute (f x) (f y) := by
      change f x * f y = f y * f x
      exact congrArg Subtype.val
        (mul_comm (⟨f x, himage x hx⟩ : U) (⟨f y, himage y hy⟩ : U))
    exact square_one_commutes_of_central_odd_kernel_image f hodd hcentral
      x y hy.2.sq_eq_one hquot
  have helem : IsElementaryAbelian 2 V :=
    square_one_commuting_closure_elementary s hcomm (fun x hx => hx.2.sq_eq_one)
  have hVP : V ≤ P := (Subgroup.closure_le _).mpr (fun _ hx => hx.1)
  have hVU : V.map f ≤ U := by
    rw [MonoidHom.map_closure]
    apply (Subgroup.closure_le _).mpr
    rintro y ⟨x, hx, rfl⟩
    exact himage x hx
  have hUV : U ≤ V.map f := by
    intro y hy
    change y ∈ (U : Set F) at hy
    rw [hUset] at hy
    rcases hy with hy | hy
    · have hy1 : y = 1 := Set.mem_singleton_iff.mp hy
      rw [hy1]
      exact (V.map f).one_mem
    · have hpre : y ∈ P.map f := hPB.symm ▸ hy.1
      obtain ⟨x, hxP, hx, hfx⟩ :=
        CFSG.ProperTwoGeneratedCore.involution_lift_in_subgroup_of_odd_kernel
          f hodd P hy.2 hpre
      exact ⟨x, Subgroup.subset_closure ⟨hxP, hx⟩, hfx⟩
  have hmap : V.map f = U := le_antisymm hVU hUV
  let : IsElementaryAbelian 2 V := helem
  have hinj : Function.Injective (f.comp V.subtype) := by
    intro x y hxy
    apply Subtype.ext
    exact square_one_injective_of_central_odd_kernel f hodd hcentral
      (elemPow_eq_one_of_isElementaryAbelian (x : G) x.property)
      (elemPow_eq_one_of_isElementaryAbelian (y : G) y.property) hxy
  have hset : (V : Set G) = {1} ∪ s := by
    ext x
    constructor
    · intro hx
      by_cases hx1 : x = 1
      · exact Or.inl (Set.mem_singleton_iff.mpr hx1)
      · exact Or.inr ⟨hVP hx, hx1, elemPow_eq_one_of_isElementaryAbelian x hx⟩
    · rintro (hx | hx)
      · obtain rfl := Set.mem_singleton_iff.mp hx
        exact V.one_mem
      · exact Subgroup.subset_closure hx
  refine ⟨helem, hVP, hmap, hinj, hset, ?_⟩
  let g : V →* U := (f.comp V.subtype).codRestrict U
    (fun x => hmap ▸ Subgroup.mem_map_of_mem f x.property)
  have hgInj : Function.Injective g := by
    intro x y hxy
    apply hinj
    exact congrArg Subtype.val hxy
  have hgSurj : Function.Surjective g := by
    intro y
    have hy : (y : F) ∈ V.map f := hmap.symm ▸ y.property
    obtain ⟨x, hx, hfx⟩ := hy
    refine ⟨⟨x, hx⟩, ?_⟩
    apply Subtype.ext
    exact hfx
  exact Nat.card_congr (MulEquiv.ofBijective g ⟨hgInj, hgSurj⟩).toEquiv

end CFSG.ProperTwoGeneratedCore.LocalCriterionNumerator
