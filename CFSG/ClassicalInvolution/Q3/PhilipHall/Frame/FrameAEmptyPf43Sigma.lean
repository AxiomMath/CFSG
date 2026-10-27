module

public import CFSG.ClassicalInvolution.Q3.PhilipHall.Frame.FrameAEmptyPf44Dstar

public section

set_option linter.unusedSectionVars false

namespace CFSG.ClassicalInvolution.Q3.PhilipHall.Frame.FrameAEmptyPf

open CFSG.ClassicalInvolution.Q3.PhilipHall.InductionBridge (FrameSimple)

open CFSG.Open CFSG.ClassicalInvolution CFSG.ClassicalInvolution.Generic
  CFSG.ClassicalInvolution.Asc77 CFSG.ClassicalInvolution.Asc77.T3
  CFSG.ClassicalInvolution.Asc77.T3Typed CFSG.ClassicalInvolution.Asc77.T3Core
  CFSG.ClassicalInvolution.Disconnected.AschTight CFSG.ComponentClassification.AS76b
  CFSG.ComponentClassification.AschbacherTightEmbedding
  CFSG.ClassicalInvolution.Q3 CFSG.ClassicalInvolution.Q3.Q3T6D
open scoped commutatorElement

section Setup

variable {T : Type} [Group T] [Finite T]
  {K : Subgroup T} {z : T} {J : Subgroup T} {zJ : T}

theorem frame_dstarComp_ne (hs : FrameStd K z J zJ) :
    sigmaOf K ≠ CoreAssembly.conjClass K :=
  frame_dstarComp_ne_proved hs

theorem frame_hs_stab (hs : FrameStd K z J zJ) (hσ : sigmaOf K ≠ CoreAssembly.conjClass K) :
    sigmaGen K ≤ conjStab (aStar (CoreAssembly.conjClass K) K) :=
  frame_hs_stab_proved hs hσ

theorem frameCfg_exists (hs : FrameStd K z J zJ) : ∃ S : Subgroup T, FrameCfg K z J zJ S := by
  have hσ := frame_dstarComp_ne hs
  have hnorm := frame_hs_stab hs hσ
  have hz := hs.datum.unique
  have hz2 : IsPGroup 2 ↥(Subgroup.zpowers z) :=
    IsPGroup.of_card (n := 1) (by
      rw [Nat.card_zpowers, orderOf_eq_prime (by rw [pow_two]; exact hz.sq) hz.ne_one, pow_one])
  have hzM : Subgroup.zpowers z ≤ sigmaNorm K := by
    rw [Subgroup.zpowers_le]
    exact Subgroup.le_normalizer (le_omegaGen (Relation.ReflTransGen.refl : K ∈ sigmaOf K) hz.mem)
  obtain ⟨S, hS, hzS⟩ := IsSylow2In.exists_ge hz2 hzM
  exact ⟨S, { toFrameStd := hs
              sigma_ne := hσ
              hs_stab := hnorm
              hS := hS
              hzS := hzS (Subgroup.mem_zpowers z) }⟩

end Setup
end CFSG.ClassicalInvolution.Q3.PhilipHall.Frame.FrameAEmptyPf
