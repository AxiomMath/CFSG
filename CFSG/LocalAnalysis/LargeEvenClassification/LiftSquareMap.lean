module

public import CFSG.LocalAnalysis.LargeEvenClassification.MaximalAbelian
public import CFSG.LocalAnalysis.LargeEvenClassification.NormalPowers

public section

namespace CFSG.LargeEvenClassification.Helpers

universe sourceUniverse quotientUniverse targetUniverse

noncomputable def descendGroupHom {Source : Type sourceUniverse} [Group Source]
    {Quotient : Type quotientUniverse} [Group Quotient] {Target : Type targetUniverse} [Group Target]
    (quotient : Source →* Quotient) (hsurjective : Function.Surjective quotient)
    (homomorphism : Source →* Target) (hkernel : quotient.ker ≤ homomorphism.ker) :
    Quotient →* Target :=
  (QuotientGroup.lift quotient.ker homomorphism hkernel).comp
    (QuotientGroup.quotientKerEquivOfSurjective quotient hsurjective).symm.toMonoidHom

theorem descendGroupHom_apply {Source : Type sourceUniverse} [Group Source]
    {Quotient : Type quotientUniverse} [Group Quotient] {Target : Type targetUniverse} [Group Target]
    (quotient : Source →* Quotient) (hsurjective : Function.Surjective quotient)
    (homomorphism : Source →* Target) (hkernel : quotient.ker ≤ homomorphism.ker) (element : Source) :
    descendGroupHom quotient hsurjective homomorphism hkernel (quotient element) =
      homomorphism element := by
  let equivalence := QuotientGroup.quotientKerEquivOfSurjective quotient hsurjective
  have hequivalence : equivalence (element : Source ⧸ quotient.ker) = quotient element :=
    QuotientGroup.kerLift_mk quotient element
  change (QuotientGroup.lift quotient.ker homomorphism hkernel)
    (equivalence.symm (quotient element)) = homomorphism element
  rw [← hequivalence, equivalence.symm_apply_apply, QuotientGroup.lift_mk]

def commutative_image_square {Source : Type sourceUniverse} [Group Source]
    {Target : Type targetUniverse} [Group Target] (projection : Source →* Target)
    (hcommutative : ∀ first second : Source, Commute (projection first) (projection second)) :
    Source →* Target := {
  toFun := fun element => projection element ^ 2
  map_one' := by rw [map_one, one_pow]
  map_mul' := by intro first second; rw [map_mul, (hcommutative first second).mul_pow] }

theorem exists_conjugation_lift_square {Ambient : Type sourceUniverse} [Group Ambient]
    (Normal : Subgroup Ambient) [Normal.Normal] (hcommutative : IsMulCommutative Normal)
    (hselfCentralizing : Subgroup.centralizer (Normal : Set Ambient) = Normal)
    (Involutions : Subgroup (MulAut Normal))
    (hlifts : ∀ automorphism : Involutions, ∃ lift : Ambient,
      MulAut.conjNormal (H := Normal) lift = (automorphism : MulAut Normal))
    (hquotientCommute :
      let _ := normalPowerSubgroup_normal Normal hcommutative 2
      ∀ first second : Ambient,
        MulAut.conjNormal (H := Normal) first ∈ Involutions →
        MulAut.conjNormal (H := Normal) second ∈ Involutions →
        Commute ((QuotientGroup.mk' (normalPowerSubgroup Normal hcommutative 2)) first)
          ((QuotientGroup.mk' (normalPowerSubgroup Normal hcommutative 2)) second)) :
    let _ := normalPowerSubgroup_normal Normal hcommutative 2
    ∃ squareMap : Involutions →* (Ambient ⧸ normalPowerSubgroup Normal hcommutative 2),
      ∀ lift : Ambient, ∀ automorphism : Involutions,
        MulAut.conjNormal (H := Normal) lift = (automorphism : MulAut Normal) →
        squareMap automorphism =
          (QuotientGroup.mk' (normalPowerSubgroup Normal hcommutative 2)) (lift ^ 2) := by
  dsimp only at hquotientCommute ⊢
  let Power := normalPowerSubgroup Normal hcommutative 2
  let : Power.Normal := normalPowerSubgroup_normal Normal hcommutative 2
  let action : Ambient →* MulAut Normal := MulAut.conjNormal
  let Preimage := Involutions.comap action
  let quotient := action.subgroupComap Involutions
  have hsurjective : Function.Surjective quotient := by
    intro automorphism
    obtain ⟨lift, hlift⟩ := hlifts automorphism
    refine ⟨⟨lift, ?_⟩, Subtype.ext hlift⟩
    change MulAut.conjNormal (H := Normal) lift ∈ Involutions
    rw [hlift]
    exact automorphism.property
  let projection := (QuotientGroup.mk' Power).comp Preimage.subtype
  have hcommute : ∀ first second : Preimage, Commute (projection first) (projection second) := by
    intro first second
    exact hquotientCommute first second first.property second.property
  let squareHom := commutative_image_square projection hcommute
  have hkernel : quotient.ker ≤ squareHom.ker := by
    intro element helement
    have hactionZero : action element = 1 :=
      congrArg (fun automorphism : Involutions => (automorphism : MulAut Normal)) helement
    have hnormalElement : (element : Ambient) ∈ Normal := by
      have hkernelEq : action.ker = Normal :=
        (conjNormal_ker_eq_centralizer Normal).trans hselfCentralizing
      exact hkernelEq.le hactionZero
    have hsquarePower : (element : Ambient) ^ 2 ∈ Power :=
      (normalPowerSubgroup_mem Normal hcommutative 2 _).mpr ⟨⟨element, hnormalElement⟩, rfl⟩
    change ((QuotientGroup.mk' Power) (element : Ambient)) ^ 2 = 1
    rw [← map_pow]
    exact (QuotientGroup.eq_one_iff _).mpr hsquarePower
  refine ⟨descendGroupHom quotient hsurjective squareHom hkernel, ?_⟩
  intro lift automorphism hlift
  let lifted : Preimage := ⟨lift, by
    change MulAut.conjNormal (H := Normal) lift ∈ Involutions
    rw [hlift]
    exact automorphism.property⟩
  have hlifted : quotient lifted = automorphism := Subtype.ext hlift
  rw [← hlifted, descendGroupHom_apply]
  change ((QuotientGroup.mk' Power) lift) ^ 2 = (QuotientGroup.mk' Power) (lift ^ 2)
  exact (map_pow _ _ _).symm

end CFSG.LargeEvenClassification.Helpers
