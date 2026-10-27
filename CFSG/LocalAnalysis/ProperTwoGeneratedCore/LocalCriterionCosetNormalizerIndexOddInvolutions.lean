module

public import CFSG.ThirdParty.QiuzhenCFSG.BenderSuzuki.PFchapter1section1.lemma_a
public import CFSG.ThirdParty.QiuzhenCFSG.BenderSuzuki.PFchapter1section1.proposition_6_b

public noncomputable section

namespace CFSG.ProperTwoGeneratedCore.LocalCriterionCosetNormalizerIndex

open CFSG.BenderSuzuki.PFAppendixIII
open CFSG.BenderSuzuki.PFchapter1section1

universe u v

variable {G : Type u} {F : Type v} [Group G] [Group F]

theorem involution_map_of_odd_kernel [Finite G] (f : G →* F)
    (hodd : Odd (Nat.card f.ker)) {x : G} (hx : IsInvolution x) :
    IsInvolution (f x) := by
  constructor
  · intro hfx
    have hxker : x ∈ f.ker := hfx
    exact hx.ne_one
      (proposition_6_b_eq_one_of_sq_eq_one_mem_odd_subgroup f.ker hodd hxker hx.sq_eq_one)
  · rw [← map_pow, hx.sq_eq_one, map_one]

theorem square_one_injective_of_central_odd_kernel [Finite G] (f : G →* F)
    (hodd : Odd (Nat.card f.ker)) (hcentral : f.ker ≤ Subgroup.center G)
    {x y : G} (hx : x ^ 2 = 1) (hy : y ^ 2 = 1) (hxy : f x = f y) :
    x = y := by
  let d := x * y⁻¹
  have hd : d ∈ f.ker := by
    change f (x * y⁻¹) = 1
    rw [map_mul, map_inv, hxy, mul_inv_cancel]
  have hdy : Commute d y := by
    rw [commute_iff_eq]
    exact (Subgroup.mem_center_iff.mp (hcentral hd) y).symm
  have hproduct : d * y = x := by simp only [d, mul_assoc, inv_mul_cancel, mul_one]
  have hdsquare : d ^ 2 = 1 := by
    calc
      d ^ 2 = d ^ 2 * y ^ 2 := by rw [hy, mul_one]
      _ = (d * y) ^ 2 := (hdy.mul_pow 2).symm
      _ = 1 := by rw [hproduct, hx]
  have hd1 := proposition_6_b_eq_one_of_sq_eq_one_mem_odd_subgroup f.ker hodd hd hdsquare
  exact mul_inv_eq_one.mp hd1

theorem involution_lift_of_central_odd_kernel [Finite G] (f : G →* F)
    (hf : Function.Surjective f) (hodd : Odd (Nat.card f.ker))
    (hcentral : f.ker ≤ Subgroup.center G) {y : F} (hy : IsInvolution y) :
    ∃ x : G, IsInvolution x ∧ f x = y := by
  obtain ⟨x, hfx⟩ := hf y
  have hxsquare : x ^ 2 ∈ f.ker := by
    change f (x ^ 2) = 1
    rw [map_pow, hfx, hy.sq_eq_one]
  obtain ⟨d, hdsquare⟩ := sq_surjective_of_odd_card (X := f.ker) hodd
    ⟨(x ^ 2)⁻¹, f.ker.inv_mem hxsquare⟩
  have hdsquare' : (d : G) ^ 2 = (x ^ 2)⁻¹ := congrArg Subtype.val hdsquare
  have hxd : Commute x (d : G) := by
    rw [commute_iff_eq]
    exact Subgroup.mem_center_iff.mp (hcentral d.property) x
  have hmap : f (x * (d : G)) = y := by
    rw [map_mul, show f (d : G) = 1 from d.property, mul_one, hfx]
  refine ⟨x * (d : G), ⟨?_, ?_⟩, hmap⟩
  · intro hx1
    apply hy.ne_one
    rw [hx1, map_one] at hmap
    exact hmap.symm
  · rw [hxd.mul_pow 2, hdsquare', mul_inv_cancel]

theorem whole_involution_card_comap_of_central_odd_kernel [Finite G]
    (f : G →* F) (hf : Function.Surjective f) (hodd : Odd (Nat.card f.ker))
    (hcentral : f.ker ≤ Subgroup.center G) (B : Subgroup F) :
    Nat.card {x : G // x ∈ B.comap f ∧ IsInvolution x} =
      Nat.card {x : F // x ∈ B ∧ IsInvolution x} := by
  let liftMap : {x : G // x ∈ B.comap f ∧ IsInvolution x} →
      {x : F // x ∈ B ∧ IsInvolution x} := fun x =>
    ⟨f x, x.property.1, involution_map_of_odd_kernel f hodd x.property.2⟩
  have hmap : Function.Bijective liftMap := by
    constructor
    · intro x y hxy
      apply Subtype.ext
      exact square_one_injective_of_central_odd_kernel f hodd hcentral
        x.property.2.sq_eq_one y.property.2.sq_eq_one (congrArg Subtype.val hxy)
    · intro y
      obtain ⟨x, hx, hfx⟩ := involution_lift_of_central_odd_kernel f hf hodd hcentral y.property.2
      refine ⟨⟨x, ?_, hx⟩, Subtype.ext hfx⟩
      change f x ∈ B
      rw [hfx]
      exact y.property.1
  exact Nat.card_congr (Equiv.ofBijective liftMap hmap)

end CFSG.ProperTwoGeneratedCore.LocalCriterionCosetNormalizerIndex
