module

public import CFSG.ClassicalInvolution.Q3.PhilipHall.Frame.TwinPerpPf17Perp

public section

set_option linter.unusedSectionVars false

namespace CFSG.ClassicalInvolution.Q3.PhilipHall.Frame.TwinPerp23

open CFSG CFSG.Open CFSG.ClassicalInvolution CFSG.ClassicalInvolution.Generic
  CFSG.ClassicalInvolution.Asc77 CFSG.ClassicalInvolution.Disconnected.AschTight
  CFSG.ClassicalInvolution.Q3 CFSG.ClassicalInvolution.Q3.PhilipHall.Frame
  CFSG.ClassicalInvolution.Q3.PhilipHall.Frame.TwinPerp
  CFSG.ClassicalInvolution.Q3.PhilipHall.Frame.TwinDisc CFSG.ClassicalInvolution.Uniform
  CFSG.ClassicalInvolution.Q3.Q3NL CFSG.ClassicalInvolution.Balance.Bootstrap
  CFSG.ClassicalInvolution.Q3.PhilipHall.QuaternionBridge CFSG.ClassicalInvolution.Disconnected
open scoped commutatorElement

section G27

open CFSG.ClassicalInvolution.Q8P.P24 CFSG.ClassicalInvolution.Q3.PhilipHall.Frame.TwinVtx
  CFSG.ClassicalInvolution.Q3.PhilipHall.Frame.TwinCentRes
  CFSG.ClassicalInvolution.Q3.PhilipHall.Frame.TwinFrameTgt
  CFSG.ClassicalInvolution.Q3.PhilipHall.Frame.TwinPerpV3
  CFSG.ClassicalInvolution.Q8P.Asc77
  CFSG.ClassicalInvolution.Q3.PhilipHall.Frame.TwinExitPf6
  CFSG.ClassicalInvolution.Q3.PhilipHall.Frame.TwinEdge CFSG.ClassicalInvolution.Q3.Q3CH
  CFSG.ClassicalInvolution.Balance

variable {G : Type} [Group G] [Finite G] {Ω : Set (Subgroup G)} {K₀ K K' : Subgroup G}
  {b d c : G} {B : Subgroup G}

theorem movedOddFreeAt_of_outAt [CoreLike G] (hst : AscStand Ω K₀)
    (hE : CFSG.ClassicalInvolution.Q3.PhilipHall.Frame.TwinThmE.EIHAll (Nat.card G))
    (hq2 : ∀ M ∈ Ω, IsPGroup 2 (↥M ⧸ classicalInvolutionOddCore ↥M))
    (X : TwinInnerHyp Ω K K' b d c B) (hO : TwinInnerOutAt Ω)
    (hbC : b ∈ Subgroup.centralizer ({c} : Set G)) : MovedOddFreeAt c b hbC := by
  classical
  have hΩ : HypOmegaGen Ω := hst.hyp
  have hBelow : CIT3Below (Nat.card G) := hE.1
  have hZ : Subgroup.center G = ⊥ := CoreLike.center_eq_bot
  have hcc : c * c = 1 := by rw [← pow_two]; exact X.hB.2 c X.hcB
  have hc2 : IsPGroup 2 (Subgroup.zpowers c) :=
    CFSG.ClassicalInvolution.Asc77.ExactLayer.isPGroup_zpowers_of_sq_eq_one hcc
  have hcq : TL4.ClassicalOrQuiet c b hbC → MovedOddFreeAt c b hbC := fun h =>
    movedOddFreeAt_of_classicalOrQuiet hBelow hZ X.hc1 h
  have out1 := hO _ hst hE hq2 X hbC
  have out2 := hO _ hst hE hq2 X.swap hbC
  rcases out1 with q | l1 | ⟨e1, m1⟩
  · exact hcq (Or.inr q)
  · rcases out2 with q | l2 | ⟨e2, m2⟩
    · exact hcq (Or.inr q)
    · have hq : ∀ M ∈ Ω, ∀ P : Subgroup G, IsSylow2In P M → Nonempty (↥P ≃* QuaternionGroup 2) :=
        fun M hM => forall_sylow_iso_of_exists (exists_sylow_q8 hst hM)
      have hS := q8Section_secFam hΩ hc2 hq2 hq (fun M hM => hst.aEmpty M hM)
      have hlt := card_sec_lt (Ω := Ω) X.hc1
      have h1 : (1 : G) ∈ Subgroup.centralizer ({c} : Set G) := Subgroup.one_mem _
      obtain ⟨M, M', hM, hM', hne, hcomm, -, -, hmM, hmM'⟩ :=
        liftPair_tf hΩ hc2 hBelow hlt hS X.htq X.htq' X.hne X.hb X.hb' hbC l1 l2 h1
          (Subgroup.one_mem _) (Subgroup.one_mem _)
      exact hcq (Or.inl ⟨M, hM⟩)
    · exact m2
  · exact m1

end G27

end CFSG.ClassicalInvolution.Q3.PhilipHall.Frame.TwinPerp23
