module

public import CFSG.RankThree.PerfectCover.HopfCentralCoversFinite
public import CFSG.LieType.SemisimpleCentralizers.HeldLangCoverLift
public import CFSG.CGT.PushingUpLit.Transport
public import CFSG.ClassicalInvolution.SmallCases.UpgradeCoverClassical
public import CFSG.LocalAnalysis.AGLEmbeddingD2.Ambient
public import CFSG.LocalAnalysis.RankTwoShapes.UnitaryFour.Bridge
public import CFSG.LocalAnalysis.SeitzReduction.EPilotPosition
public import CFSG.RankThree.PartTwo.Sec4.Census.Item44TwoCoverModels

public section

namespace CFSG.LocalAnalysis.GLTheoremA.KD264Lie

open CFSG.Open CFSG.RankThree.PerfectCover CFSG.LieType.SemisimpleCentralizers.HeldLang
open scoped commutatorElement

theorem exists_hopf_lift {X K : Type} [Group X] [Group K] [Finite X] [Finite K]
    (hX : Group.IsPerfect X) (hK : Group.IsPerfect K) (ρ : K →* X) (hρ : Function.Surjective ρ)
    (hcen : ρ.ker ≤ Subgroup.center K) (β : MulAut K) (γ : MulAut X) (hcomm : ∀ k, ρ (β k) = γ (ρ k))
    (hγ3 : γ ^ 3 = 1) :
    ∃ (π : HopfCover X →* K) (βL : MulAut (HopfCover X)), Function.Surjective π ∧
      (∀ x, ρ (π x) = hopfCoverMap X x) ∧ (∀ x, π x = 1 → x ∈ hopfMultiplier X) ∧ βL ^ 3 = 1 ∧
      (∀ x, π (βL x) = β (π x)) := by
  haveI := hX
  haveI := hK
  haveI hfin : Finite (HopfCover X) := finite_hopfCover hX
  haveI hperfL : Group.IsPerfect (HopfCover X) := hopfCover_isPerfect
  have hu : Function.Surjective (hopfCoverMap X) := hopfCoverMap_surjective
  have hker : hopfMultiplier X ≤ Subgroup.center (HopfCover X) := hopfMultiplier_le_center
  have hπ : ρ.comp (hopfLift ρ hρ hcen) = hopfCoverMap X := comp_hopfLift ρ hρ hcen
  have hπsurj : Function.Surjective (hopfLift ρ hρ hcen) := hopfLift_surjective ρ hρ hcen
  let q : HopfCover X →* X := γ.symm.toMonoidHom.comp (hopfCoverMap X)
  have hq : Function.Surjective q := γ.symm.surjective.comp hu
  have hqker : q.ker ≤ Subgroup.center (HopfCover X) := by
    intro x hx
    apply hker
    have h1 : γ.symm (hopfCoverMap X x) = 1 := hx
    have h2 : hopfCoverMap X x = 1 := by
      have := congrArg γ h1
      simpa using this
    exact h2
  have hφ : q.comp (hopfLift q hq hqker) = hopfCoverMap X := comp_hopfLift q hq hqker
  have hφsurj : Function.Surjective (hopfLift q hq hqker) := hopfLift_surjective q hq hqker
  have huφ : ∀ x, hopfCoverMap X (hopfLift q hq hqker x) = γ (hopfCoverMap X x) := by
    intro x
    have h1 : γ.symm (hopfCoverMap X (hopfLift q hq hqker x)) = hopfCoverMap X x :=
      congrArg (fun f : HopfCover X →* X => f x) hφ
    calc hopfCoverMap X (hopfLift q hq hqker x) = γ (γ.symm (hopfCoverMap X (hopfLift q hq hqker x))) := by simp
      _ = γ (hopfCoverMap X x) := by rw [h1]
  let βL : MulAut (HopfCover X) :=
    MulEquiv.ofBijective (hopfLift q hq hqker) ⟨Finite.injective_iff_surjective.2 hφsurj, hφsurj⟩
  have hβL : ∀ x, hopfCoverMap X (βL x) = γ (hopfCoverMap X x) := huφ
  have hpow : ∀ n : ℕ, ∀ x, hopfCoverMap X ((βL ^ n) x) = (γ ^ n) (hopfCoverMap X x) := by
    intro n
    induction n with
    | zero => intro x; rfl
    | succ n ih =>
      intro x
      rw [pow_succ, MulAut.mul_apply, ih, hβL, pow_succ, MulAut.mul_apply]
  refine ⟨hopfLift ρ hρ hcen, βL, hπsurj, fun x => by rw [← hπ]; rfl, ?_, ?_, ?_⟩
  · intro x hx
    change hopfCoverMap X x = 1
    rw [← hπ]
    show ρ (hopfLift ρ hρ hcen x) = 1
    rw [hx, map_one]
  · have h3 : (βL ^ 3).toMonoidHom = MonoidHom.id (HopfCover X) := by
      refine eq_of_central_displacement (βL ^ 3).toMonoidHom (MonoidHom.id (HopfCover X)) fun x => ?_
      apply hker
      change hopfCoverMap X (x⁻¹ * (βL ^ 3) x) = 1
      rw [map_mul, map_inv, hpow, hγ3]
      simp
    ext x
    exact congrArg (fun f : HopfCover X →* HopfCover X => f x) h3
  · have hh : (hopfLift ρ hρ hcen).comp βL.toMonoidHom = β.toMonoidHom.comp (hopfLift ρ hρ hcen) := by
      refine eq_of_central_displacement_hom _ _ fun x => ?_
      apply hcen
      rw [MonoidHom.mem_ker, map_mul, map_inv]
      show (ρ (β (hopfLift ρ hρ hcen x)))⁻¹ * ρ (hopfLift ρ hρ hcen (βL x)) = 1
      have e1 : ρ (hopfLift ρ hρ hcen (βL x)) = hopfCoverMap X (βL x) := by rw [← hπ]; rfl
      have e2 : ρ (hopfLift ρ hρ hcen x) = hopfCoverMap X x := by rw [← hπ]; rfl
      rw [hcomm, e1, e2, hβL, inv_mul_cancel]
    intro x
    exact congrArg (fun f : HopfCover X →* K => f x) hh

theorem center_hopfCover_eq {X : Type} [Group X] [Group.IsPerfect X] (hZ : Subgroup.center X = ⊥) :
    Subgroup.center (HopfCover X) = hopfMultiplier X := by
  refine le_antisymm (fun z hz => ?_) hopfMultiplier_le_center
  have hu : Function.Surjective (hopfCoverMap X) := hopfCoverMap_surjective
  have hc : hopfCoverMap X z ∈ Subgroup.center X := by
    rw [Subgroup.mem_center_iff]
    intro x
    obtain ⟨y, rfl⟩ := hu x
    rw [← map_mul, ← map_mul, Subgroup.mem_center_iff.1 hz y]
  rw [hZ, Subgroup.mem_bot] at hc
  exact hc

end CFSG.LocalAnalysis.GLTheoremA.KD264Lie
