module

public import CFSG.LocalAnalysis.ProperTwoGeneratedCore.LocalCriterionRecognizedThreePointNormalizer
public import CFSG.LocalAnalysis.ProperTwoGeneratedCore.LocalCriterionOddQuotientLifting

public noncomputable section

namespace CFSG.ProperTwoGeneratedCore.LocalCriterionRecognizedThreePoint

open CFSG.BenderSuzuki.PFAppendixIII

variable {G Q : Type*} [Group G] [Finite G] [Group Q]

theorem surjective_normalizer_image_of_sylow_intersection
    {p : ℕ} (hp : p.Prime) (f : G →* Q) (hf : Function.Surjective f)
    (P : Subgroup G) (hP : IsPGroup p P)
    (hintersection : ∃ T : Sylow p f.ker,
      (T : Subgroup f.ker).map f.ker.subtype = P ⊓ f.ker) :
    (Subgroup.normalizer (P : Set G)).map f =
      Subgroup.normalizer (P.map f : Set Q) := by
  let e := QuotientGroup.quotientKerEquivOfSurjective f hf
  have hcomp : e.toMonoidHom.comp (QuotientGroup.mk' f.ker) = f := by
    ext x
    rfl
  have h := congrArg (Subgroup.map e.toMonoidHom)
    (quotient_normalizer_image_of_sylow_intersection hp f.ker P hP hintersection)
  rw [Subgroup.map_map, hcomp, Subgroup.map_equiv_normalizer_eq,
    Subgroup.map_map, hcomp] at h
  exact h

theorem normalizer_involution_lift_of_sylow_intersection
    {p : ℕ} (hp : p.Prime) (f : G →* Q) (hf : Function.Surjective f)
    (hodd : Odd (Nat.card f.ker)) (P : Subgroup G) (hP : IsPGroup p P)
    (hintersection : ∃ T : Sylow p f.ker,
      (T : Subgroup f.ker).map f.ker.subtype = P ⊓ f.ker)
    {y : Q} (hy : IsInvolution y)
    (hynormalizer : y ∈ Subgroup.normalizer (P.map f : Set Q)) :
    ∃ x : G, x ∈ Subgroup.normalizer (P : Set G) ∧
      IsInvolution x ∧ f x = y := by
  apply involution_lift_in_subgroup_of_odd_kernel f hodd
    (Subgroup.normalizer (P : Set G)) hy
  rw [surjective_normalizer_image_of_sylow_intersection hp f hf P hP hintersection]
  exact hynormalizer

end CFSG.ProperTwoGeneratedCore.LocalCriterionRecognizedThreePoint
