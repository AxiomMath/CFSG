module

public import CFSG.HardMathSupport.Timmesfeld.CrossChar.TrialityA2TwoMinus

public section

namespace CFSG.HardMathSupport.Timmesfeld.CrossChar

open CFSG.GH74.BNPair CFSG.GH74.GLS.SP CFSG.GH74.GLS.Stage2.Bender.Thm1
open CFSG.Blueprint.Chevalley CFSG.LieType.Chevalley CFSG.LieType.Steinberg
  CFSG.LieType.Steinberg.Adjoint CFSG.LieType.Steinberg.TwistedD4 CFSG.GH74.GLS.Stage4.Hex
open CFSG.LocalAnalysis.ComponentInitial.FourGroupChevalley (rootDiagUnit)


theorem trialityA2ToralTwoFold_of_a2Core
    (hA2 : ∀ f : ℕ, 1 ≤ f → ∀ (K : Type) [Field K] [Finite K], Nat.card K = (2 ^ f) ^ 3 →
      ∀ σ : K ≃+* K, (∀ c, σ c = c ^ (2 ^ f)) → (2 ^ f) % 3 = 1 → ∀ d : Kˣ,
        Units.map σ.toRingHom.toMonoidHom d = d → d ^ 3 = 1 → d ≠ 1 → A2Core σ d (2 ^ f)) :
    TrialityA2ToralTwoFold := by
  intro f hf K _ _ hK σ hσ hq s d hd hd3 hd1 hs
  have h := hA2 f hf K hK σ hσ hq d hd hd3 hd1
  have hφ := a2_hφ_of_class (σ := σ) (d := d) hs
  set φ : MulAut (graphFixedRootGroup TwistTag.D4 K σ.toRingHom) :=
    MulAut.conj s * fieldActor (t := TwistTag.D4) σ σ with hφdef
  have hconv : ∀ x, x ∈ CFSG.GH74.GLS.Stage2.Signalizer.Odd87.fixSub φ ↔ x ∈ fixSub φ :=
    fun _ => Iff.rfl
  refine ⟨fun N hNT hNn hcop => A2Core.a2_normal_coprime_three_eq_bot h φ hφ N hNT hNn hcop,
    ?_, ?_, A2Core.a2_card_fixSub h φ hφ⟩
  ·
    intro z hz hzc
    have hbot := A2Core.a2_noAbel_fixSub h φ hφ
      (Subgroup.center ↥(CFSG.GH74.GLS.Stage2.Signalizer.Odd87.fixSub φ)) inferInstance
      (fun x y => Subtype.ext ((Subgroup.mem_center_iff.1 y.2) (x : _)))
    have hzc' : (⟨z, (hconv z).2 hz⟩ : ↥(CFSG.GH74.GLS.Stage2.Signalizer.Odd87.fixSub φ)) ∈
        Subgroup.center ↥(CFSG.GH74.GLS.Stage2.Signalizer.Odd87.fixSub φ) := by
      rw [Subgroup.mem_center_iff]
      intro g
      exact Subtype.ext (hzc g ((hconv g).1 g.2)).symm
    rw [hbot, Subgroup.mem_bot] at hzc'
    exact congrArg Subtype.val hzc'
  ·
    obtain ⟨r₁', r₂', -, -, -, -, R'⟩ := (A2Core.a2_foldData h φ hφ).exists_rgd2
    have hcardU := A2Core.a2_card_U_fix h φ hφ R'
    have hcardU₀ : Nat.card ↥(Subgroup.map (A2Core.a2Equiv h).toMonoidHom
        ((posUnipotent (g2Shape (twistedX σ.toRingHom))) ⊓ foldFix (A2Core.a2Phi h φ))) =
          (2 ^ f) ^ 3 := by
      rw [Subgroup.card_map_of_injective (A2Core.a2Equiv h).injective]
      exact hcardU
    have : Finite ↥(Subgroup.map (A2Core.a2Equiv h).toMonoidHom
        ((posUnipotent (g2Shape (twistedX σ.toRingHom))) ⊓ foldFix (A2Core.a2Phi h φ))) :=
      Nat.finite_of_card_ne_zero (by rw [hcardU₀]; positivity)
    refine ⟨Subgroup.map (A2Core.a2Equiv h).toMonoidHom
      ((posUnipotent (g2Shape (twistedX σ.toRingHom))) ⊓ foldFix (A2Core.a2Phi h φ)), ?_, ?_, ?_⟩
    · intro x hx
      have hle : Subgroup.map (A2Core.a2Equiv h).toMonoidHom
          ((posUnipotent (g2Shape (twistedX σ.toRingHom))) ⊓ foldFix (A2Core.a2Phi h φ)) ≤
            CFSG.GH74.GLS.Stage2.Signalizer.Odd87.fixSub φ := by
        rw [← A2Core.a2_foldFix_map h φ hφ]
        exact Subgroup.map_mono inf_le_right
      exact (hconv x).1 (hle hx)
    · exact IsPGroup.of_card (n := 3 * f) (by rw [hcardU₀, ← pow_mul, mul_comm])
    · rw [hcardU₀]

theorem trialityA2ToralTwoFold_holds : TrialityA2ToralTwoFold :=
  trialityA2ToralTwoFold_of_a2Core fun _ hf _ _ _ hK _ hσ hq _ hd hd3 hd1 =>
    a2Core_two hf hK hσ hq hd hd3 hd1

theorem trialityA2CoreFreeTwoToral_holds : TrialityA2CoreFreeTwoToral :=
  trialityA2CoreFreeTwoToral_of_fold trialityA2ToralTwoFold_holds

theorem trialityA2CoreFreeTwo_holds : TrialityA2CoreFreeTwo :=
  trialityA2CoreFreeTwo_of_parts trialityA2CoreFreeTwoToral_holds trialityA2CoreFreeTwoMinus_holds

theorem trialityA2CoreFree_holds : TrialityA2CoreFree :=
  trialityA2CoreFree_of_two trialityA2CoreFreeTwo_holds

end CFSG.HardMathSupport.Timmesfeld.CrossChar
