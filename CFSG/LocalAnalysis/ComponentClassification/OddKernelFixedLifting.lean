module

public import CFSG.LocalAnalysis.ComponentClassification.InvolutionFixedPoints

public section

namespace CFSG.ComponentClassification.OddKernelFixedLifting

theorem exists_fixed_lift {G H : Type*} [Group G] [Finite G] [Group H]
    (quotient : G →* H) (hsurjective : Function.Surjective quotient)
    (hoddKernel : Odd (Nat.card quotient.ker)) (source : MulAut G) (target : MulAut H)
    (hinvolutive : Function.Involutive source)
    (hcompatible : ∀ member : G, quotient (source member) = target (quotient member))
    (member : H) (hfixed : target member = member) :
    ∃ lift : G, quotient lift = member ∧ source lift = lift := by
  let fiber := {lift : G // quotient lift = member}
  let permutation : Equiv.Perm fiber := Function.Involutive.toPerm
    (fun lift => ⟨source lift.val, by rw [hcompatible, lift.property, hfixed]⟩)
    (fun lift => Subtype.ext (hinvolutive lift.val))
  have hcard : Nat.card fiber = Nat.card quotient.ker :=
    Nat.card_congr (MonoidHom.fiberEquivKerOfSurjective hsurjective member)
  have hoddFiber : Odd (Nat.card fiber) := hcard ▸ hoddKernel
  have hmod := InvolutionFixedPoints.fixed_card_mod_two permutation
    (fun lift => Subtype.ext (hinvolutive lift.val))
  have hpositive : 0 < Nat.card {lift : fiber // permutation lift = lift} := by
    have hoddMod := Nat.odd_iff.mp hoddFiber
    omega
  obtain ⟨lift⟩ := (Nat.card_pos_iff.mp hpositive).1
  exact ⟨lift.val.val, lift.val.property, congrArg Subtype.val lift.property⟩

theorem fixed_image_eq {G H : Type*} [Group G] [Finite G] [Group H]
    (quotient : G →* H) (hsurjective : Function.Surjective quotient)
    (hoddKernel : Odd (Nat.card quotient.ker)) (source : MulAut G) (target : MulAut H)
    (hinvolutive : Function.Involutive source)
    (hcompatible : ∀ member : G, quotient (source member) = target (quotient member)) :
    (FixedCommutingProduct.fixedSubgroup source).map quotient =
      FixedCommutingProduct.fixedSubgroup target := by
  ext member
  constructor
  · rintro ⟨lift, hlift, rfl⟩
    exact (hcompatible lift).symm.trans (congrArg quotient hlift)
  · intro hfixed
    obtain ⟨lift, hvalue, hlift⟩ := exists_fixed_lift quotient hsurjective hoddKernel source target
      hinvolutive hcompatible member hfixed
    exact ⟨lift, hlift, hvalue⟩

end CFSG.ComponentClassification.OddKernelFixedLifting
