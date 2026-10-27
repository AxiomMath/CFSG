module

public import CFSG.LocalAnalysis.LargeEvenClassification.NormObstruction
public import CFSG.LocalAnalysis.LargeEvenClassification.InvariantKernel
public import CFSG.LocalAnalysis.LargeEvenClassification.NormalPowers

public section

open CFSG.Open

namespace CFSG.LargeEvenClassification.Helpers

universe groupUniverse

theorem conjugation_lift_square_injective {Ambient : Type groupUniverse} [Group Ambient]
    [Finite Ambient] (hpgroup : IsPGroup 2 Ambient)
    (Normal : Subgroup Ambient) [Normal.Normal] (hcommutative : IsMulCommutative Normal)
    (hselfCentralizing : Subgroup.centralizer (Normal : Set Ambient) = Normal)
    (hnoEight : ∀ Eight : Subgroup Ambient, Eight.Normal → IsElemAbelian 2 Eight → Nat.card Eight ≠ 8)
    (hcard : Nat.card (normalElementarySquareKernel Normal hcommutative) = 4)
    (Involutions : Subgroup (MulAut Normal))
    (hstable : ∀ conjugator : Ambient, ∀ automorphism : MulAut Normal,
      automorphism ∈ Involutions →
        MulAut.conjNormal (H := Normal) conjugator * automorphism *
          (MulAut.conjNormal (H := Normal) conjugator)⁻¹ ∈ Involutions)
    (helementary : IsElemAbelian 2 Involutions)
    (hlifts : ∀ automorphism : Involutions, ∃ lift : Ambient,
      MulAut.conjNormal (H := Normal) lift = (automorphism : MulAut Normal))
    (hnormKernel : ∀ automorphism : Involutions, ∀ entry : Normal,
      (automorphism : MulAut Normal) entry * entry = 1 ↔ entry ^ 2 = 1)
    (hnormImage : ∀ automorphism : Involutions, ∀ entry : Normal, ∃ source : Normal,
      (automorphism : MulAut Normal) source * source = entry ^ 2) :
    let _ := normalPowerSubgroup_normal Normal hcommutative 2
    ∀ squareMap : Involutions →* (Ambient ⧸ normalPowerSubgroup Normal hcommutative 2),
      (∀ lift : Ambient, ∀ automorphism : Involutions,
        MulAut.conjNormal (H := Normal) lift = (automorphism : MulAut Normal) →
          squareMap automorphism =
            (QuotientGroup.mk' (normalPowerSubgroup Normal hcommutative 2)) (lift ^ 2)) →
      Function.Injective squareMap := by
  dsimp only
  let Power := normalPowerSubgroup Normal hcommutative 2
  let : Power.Normal := normalPowerSubgroup_normal Normal hcommutative 2
  intro squareMap hsquares
  let action : Ambient →* MulAut Normal := MulAut.conjNormal
  let conjugation : Ambient →* MulAut Involutions :=
    invariantSubgroupConjugation action Involutions hstable
  have hpInvolutions : IsPGroup 2 Involutions := by
    intro automorphism
    exact ⟨1, by
      apply Subtype.ext
      exact helementary.2 automorphism automorphism.property⟩
  apply pGroup_invariant_kernel_injective Nat.prime_two hpgroup hpInvolutions
    conjugation squareMap
  · intro conjugator automorphism hkilled
    obtain ⟨lift, hlift⟩ := hlifts automorphism
    have hconjugateLift : action (conjugator * lift * conjugator⁻¹) =
        (conjugation conjugator automorphism : MulAut Normal) := by
      rw [map_mul, map_mul, map_inv, hlift]
      rfl
    rw [hsquares _ _ hconjugateLift]
    have hconjugateSquare : (conjugator * lift * conjugator⁻¹) ^ 2 =
        conjugator * lift ^ 2 * conjugator⁻¹ := by simp only [pow_two]; group
    rw [hconjugateSquare, map_mul, map_mul, map_inv, ← hsquares lift automorphism hlift, hkilled]
    simp
  · intro automorphism hkilled hfixed
    by_contra hnontrivial
    obtain ⟨lift, hlift⟩ := hlifts automorphism
    have hcentral : ∀ element : Ambient, Commute (automorphism : MulAut Normal) (action element) := by
      intro element
      have hfix := congrArg (fun entry : Involutions => (entry : MulAut Normal)) (hfixed element)
      change action element * (automorphism : MulAut Normal) * (action element)⁻¹ =
        (automorphism : MulAut Normal) at hfix
      exact (mul_inv_eq_iff_eq_mul.mp hfix).symm
    have hnontrivialAut : (automorphism : MulAut Normal) ≠ 1 := by
      intro hone
      exact hnontrivial (Subtype.ext hone)
    have hsquare : (automorphism : MulAut Normal) ^ 2 = 1 :=
      helementary.2 automorphism automorphism.property
    have hobstruction := central_action_involution_norm_obstruction Normal hcommutative
      hselfCentralizing hnoEight automorphism hsquare hnontrivialAut hcentral
      (hnormKernel automorphism) hcard lift hlift
    have hliftPower : lift ^ 2 ∈ Power := by
      apply (QuotientGroup.eq_one_iff _).mp
      exact (hsquares lift automorphism hlift).symm.trans hkilled
    obtain ⟨entry, hentry⟩ := (normalPowerSubgroup_mem Normal hcommutative 2 _).mp hliftPower
    obtain ⟨source, hsource⟩ := hnormImage automorphism entry
    apply hobstruction.2 source
    exact hentry.symm.trans (congrArg (fun entry : Normal => (entry : Ambient)) hsource).symm

end CFSG.LargeEvenClassification.Helpers
