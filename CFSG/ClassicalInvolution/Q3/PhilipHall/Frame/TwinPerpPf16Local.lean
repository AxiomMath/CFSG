module

public import CFSG.ClassicalInvolution.Q3.PhilipHall.Frame.TwinPerpPf6Main
public import CFSG.ClassicalInvolution.Q3.PhilipHall.Frame.TwinPerpPf5Std
public import CFSG.ClassicalInvolution.Q3.PhilipHall.Frame.TwinPerpPf6Stmt
public import CFSG.ClassicalInvolution.Q3.PhilipHall.Frame.TwinPerpPf9A04
public import CFSG.ClassicalInvolution.Q3.PhilipHall.Frame.TwinPerpPfMain

public section

set_option autoImplicit false
set_option linter.unusedSectionVars false

namespace CFSG.ClassicalInvolution.Q8P

namespace Asc77

open CFSG.Open CFSG.ClassicalInvolution CFSG.ClassicalInvolution.Generic
  CFSG.ClassicalInvolution.Disconnected CFSG.ClassicalInvolution.Asc77
  CFSG.ClassicalInvolution.Disconnected.AschTight

section SetUp

variable {G : Type} [Group G] [Finite G] {Ω : Set (Subgroup G)} {K K' : Subgroup G} {z : G}

theorem c24_1_of_9coreL [CoreLike G] [Fact (P24.Hyp51TwinInnerAt Ω)] (h9 : C24_9_core)
    (hs : Hyp23 Ω K K' z)
    {W : Subgroup G} (hW : W ∈ WSet Ω) (hzW : z ∈ W) (hS4 : MuIsoS4 Ω W)
    (hZ : W ⊓ Asc77.centerIn (Subgroup.normalizer (W : Set G)) = ⊥) :
    TwoSubgroupsFourGenerated G := by
  obtain ⟨S, R, R', b, b', -, -, -, -, hyp⟩ := c24_setup hs hW hzW hS4 hZ
  obtain ⟨J, hJ, hRJ⟩ := exists_isSylow2In_of_mem_RSet hyp.hR.1
  have h8 : Nat.card ↥R = 8 := hs.1.stand.card8 J hJ R hRJ
  rcases c24_5_proved G Ω K K' W S R R' z (b * b') hyp h8 with hnot | hconc
  · exact (h9 G Ω K K' W S R R' z (b * b') hyp h8 hnot).elim
  · exact hconc

end SetUp

end Asc77

end CFSG.ClassicalInvolution.Q8P

namespace CFSG.ClassicalInvolution.Q3.PhilipHall.Frame.TwinPerp

open CFSG CFSG.Open CFSG.ClassicalInvolution CFSG.ClassicalInvolution.Generic
  CFSG.ClassicalInvolution.Asc77 CFSG.ClassicalInvolution.Disconnected.AschTight
  CFSG.ClassicalInvolution.Q3 CFSG.ClassicalInvolution.Q3.PhilipHall.Frame

theorem twinPerp24S_of_9coreL {n : ℕ} (hE : TwinThmE.EIHAll n) (hY : Q8P.P24.Hyp51TwinInnerPerp n)
    (h9 : Q8P.Asc77.C24_9_core) : TwinPerp24S n := by
  intro Y _ _ R S t hP h2 W hW htW hS4 hnc
  have hC := CoreData.of_S hP.core
  have := Q8P.coreLike_of_core hC
  obtain ⟨K', hK', hne⟩ := hC.twin
  have hs := Q8P.hyp23_of_core hC hE hP.disc hP.perp h2 hK' hne
  have : Fact (Q8P.P24.Hyp51TwinInnerAt (CoreAssembly.conjClass (tightCore R))) := ⟨hY Y R S t hP⟩
  exact Q8P.tf4_of_le (genFittingFStar Y)
    (Q8P.Asc77.c24_1_of_9coreL h9 hs hW htW hS4
      (inf_centerIn_eq_bot_of_not_wCentralNontrivial hnc))

end CFSG.ClassicalInvolution.Q3.PhilipHall.Frame.TwinPerp
