module

public import CFSG.HardMathSupport.Timmesfeld.CrossChar.A6Block
public import CFSG.HardMathSupport.Timmesfeld.CrossChar.A6FrameE7
public import CFSG.HardMathSupport.Timmesfeld.CrossChar.A6FrameE8
public import CFSG.HardMathSupport.Timmesfeld.CrossChar.PlanesToralSeven
public import CFSG.HardMathSupport.Timmesfeld.CrossChar.PlanesToralE7
public import CFSG.HardMathSupport.Timmesfeld.CrossChar.PlanesToralE8

public noncomputable section

set_option linter.unusedSectionVars false

namespace CFSG.HardMathSupport.Timmesfeld.CrossChar

open CFSG.Blueprint.Chevalley CFSG.LieType.Chevalley CFSG.LieType.Steinberg.Adjoint
open CFSG.RankThree.PartOne.KE

variable (τ : Tag) in
@[expose] def A6ChainTransitive (nd : Fin 6 → Fin τ.rank) : Prop :=
  ∀ β : Fin 6 → Fin τ.rank → ℤ, IsAChain β →
    ∃ v : WeylGroup τ, ∀ k, v • (Pi.single (nd k) 1 : Fin τ.rank → ℤ) = β k

section E7

theorem chainBlockToral_E7_six_of_transitive (htr : A6ChainTransitive Tag.E7 a6chainE7) :
    ChainBlockToral Tag.E7 6 :=
  chainBlockToral_six_of_transitive a6ChainData_E7 a6ChainFrames_E7
    (fun _ _ => a6Frame_injective a6ChainData_E7 a6ChainFrames_E7 (e7Index 1)
      a6chainE7_cartan_one) htr

theorem planesToralBar_E7_seven_of_stab (htr : A6ChainTransitive Tag.E7 a6chainE7)
    (hstab : ∀ (L : Type) [Field L] (a : Fin Tag.E7.rank → Lˣ), (∀ i, a i ^ 7 = 1) →
      rootCharStabilizerSubgroup a ≤ kernelReflectionGroup a) :
    Torality.PlanesToralBar Tag.E7 7 :=
  planesToralBar_seven_of_chainBlock (fun _ hγ => iform_self_E7 hγ)
    (chainBlockToral_E7_six_of_transitive htr) hstab

end E7

section E8

theorem chainBlockToral_E8_six_of_transitive (htr : A6ChainTransitive Tag.E8 a6chainE8) :
    ChainBlockToral Tag.E8 6 :=
  chainBlockToral_six_of_transitive a6ChainData_E8 a6ChainFrames_E8
    (fun _ _ => a6Frame_injective a6ChainData_E8 a6ChainFrames_E8 (e8Index 1)
      a6chainE8_cartan_one) htr

theorem planesToralBar_E8_seven_of_stab (htr : A6ChainTransitive Tag.E8 a6chainE8)
    (hstab : ∀ (L : Type) [Field L] (a : Fin Tag.E8.rank → Lˣ), (∀ i, a i ^ 7 = 1) →
      rootCharStabilizerSubgroup a ≤ kernelReflectionGroup a) :
    Torality.PlanesToralBar Tag.E8 7 :=
  planesToralBar_seven_of_chainBlock (fun _ hγ => iform_self_E8 hγ)
    (chainBlockToral_E8_six_of_transitive htr) hstab

end E8

end CFSG.HardMathSupport.Timmesfeld.CrossChar
