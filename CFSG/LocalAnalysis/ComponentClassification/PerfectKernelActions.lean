module

public import CFSG.LocalAnalysis.ComponentClassification.PerfectAutomorphisms
public import CFSG.Assembly.Defs

public section

namespace CFSG.ComponentClassification.PerfectKernelActions

theorem action_eq_one_of_fixed_kernel {A G H : Type*}
    [Group A] [Group.IsPerfect A] [Group G] [Group H]
    (quotient : G →* H) (action : A →* MulAut G)
    (hquotient : ∀ actor : A, ∀ member : G, quotient ((action actor) member) = quotient member)
    (hfixed : ∀ actor : A, ∀ member ∈ quotient.ker, (action actor) member = member) :
    action = 1 := by
  apply MonoidHom.ext
  intro actor
  apply MulEquiv.ext
  intro member
  let displacement : A →* quotient.ker :=
    { toFun := fun element => ⟨member⁻¹ * (action element) member, by
        apply MonoidHom.mem_ker.mpr
        rw [map_mul, map_inv, hquotient, inv_mul_cancel]⟩
      map_one' := by apply Subtype.ext; simp
      map_mul' := by
        intro left right
        apply Subtype.ext
        have hmem : member⁻¹ * (action right) member ∈ quotient.ker := by
          apply MonoidHom.mem_ker.mpr
          rw [map_mul, map_inv, hquotient, inv_mul_cancel]
        have hdisplacementFixed := hfixed left _ hmem
        have heq : (action left) member⁻¹ * (action left) ((action right) member) =
            member⁻¹ * (action right) member := by
          simpa only [map_mul, map_inv] using hdisplacementFixed
        change member⁻¹ * (action (left * right)) member =
          (member⁻¹ * (action left) member) * (member⁻¹ * (action right) member)
        rw [map_mul, MulAut.mul_apply, ← heq]
        rw [map_inv]
        group }
  have hcentral : ∀ element : A, displacement element ∈ Subgroup.center quotient.ker := by
    intro element
    apply Subgroup.mem_center_iff.mpr
    intro kernelMember
    apply Subtype.ext
    have hconjugate : member * kernelMember.val * member⁻¹ ∈ quotient.ker :=
      (inferInstance : quotient.ker.Normal).conj_mem kernelMember.val kernelMember.property member
    have hconjugateFixed := hfixed element _ hconjugate
    have hmemberFixed := hfixed element kernelMember.val kernelMember.property
    rw [map_mul, map_mul, map_inv, hmemberFixed] at hconjugateFixed
    change kernelMember.val * (member⁻¹ * (action element) member) =
      (member⁻¹ * (action element) member) * kernelMember.val
    have heq := congrArg (fun value : G => member⁻¹ * value * (action element) member)
      hconjugateFixed
    calc
      kernelMember.val * (member⁻¹ * (action element) member) =
          member⁻¹ * (member * kernelMember.val * member⁻¹) * (action element) member := by group
      _ = member⁻¹ * ((action element) member * kernelMember.val *
            ((action element) member)⁻¹) * (action element) member := heq.symm
      _ = (member⁻¹ * (action element) member) * kernelMember.val := by group
  let centralDisplacement := displacement.codRestrict (Subgroup.center quotient.ker) hcentral
  have htrivial := PerfectAutomorphisms.hom_eq_one_of_commutative centralDisplacement
  have hone := congrArg (fun homomorphism : A →* Subgroup.center quotient.ker =>
      ((homomorphism actor).val : G)) htrivial
  change member⁻¹ * (action actor) member = 1 at hone
  exact (inv_mul_eq_one.mp hone).symm

end CFSG.ComponentClassification.PerfectKernelActions
