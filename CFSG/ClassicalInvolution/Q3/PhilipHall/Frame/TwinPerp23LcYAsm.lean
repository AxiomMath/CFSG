module

public import CFSG.ClassicalInvolution.Q3.PhilipHall.Frame.TwinPerp23LcMain
public import CFSG.ClassicalInvolution.Q3.PhilipHall.Frame.TwinPerp23LcYHull
public import CFSG.ClassicalInvolution.Q3.PhilipHall.Frame.TwinPerp23LcYL
public import CFSG.ClassicalInvolution.Q3.PhilipHall.Frame.TwinPerp23LcOutFact
public import CFSG.ClassicalInvolution.Q3.PhilipHall.Frame.TwinPerp23LcA6Fact

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
  CFSG.ClassicalInvolution.Balance
open scoped commutatorElement

section YAsm

variable {n : ℕ}

theorem p23YLu_proved : P23YLu n := by
  intro hcit hP Y _ _ R S t K' W u e g hc hα hno hnoU hEo hYo hodd hOu hOus M M' hM hM' hJM hJ'M'
    hcomm
  have hd := hc.data
  have hC := CoreData.of_S hc.std.perp.core
  have hΩ : HypOmegaGen (Om R) := hC.hyp
  have hz : IsUniqueInvolution (tightCore R) t := Inner.isUniqueInvolution_core hC.datum
  have hz' : IsUniqueInvolution K' t := isUniqueInvolution_of_mem_twinSet hz hc.std.hK'
  have hc2 : IsPGroup 2 (Subgroup.zpowers u) :=
    CFSG.ClassicalInvolution.Asc77.ExactLayer.isPGroup_zpowers_of_sq_eq_one hd.hu2
  obtain ⟨M₀, M₀', hM₀, hM₀', hJM₀, hJ'M₀', -, hM₀L, hM₀'L⟩ :=
    p23_sectionLifts_hull hP hc hno hnoU hα hOu
  have hOC : classicalInvolutionOddCore ↥(Subgroup.centralizer ({u} : Set Y) ⊓
      Subgroup.centralizer ({u * e} : Set Y)) = ⊥ :=
    TwinConnT.classicalOddCore_eq_bot_of_oddCoreIn hOus
  have hJΩ : conjSub g (tightCore R) ∈ Om R :=
    hΩ.conjInvariant g _ (CoreAssembly.mem_conjClass_self _)
  have hJ'Ω : conjSub g K' ∈ Om R := hΩ.conjInvariant g _ hc.std.hK'.1
  have hJz : IsUniqueInvolution (conjSub g (tightCore R)) (u * e) := by
    have := hz.conj g
    rwa [hd.hgt] at this
  have hJ'z : IsUniqueInvolution (conjSub g K') (u * e) := by
    have := hz'.conj g
    rwa [hd.hgt] at this
  have hMM₀ : M = M₀ :=
    TwinConnT.liftUnique_on hΩ hJΩ hJz hJM hJM₀ hM.le hM₀.le hM.toIn hM₀.toIn hOC
  have hM'M₀' : M' = M₀' :=
    TwinConnT.liftUnique_on hΩ hJ'Ω hJ'z hJ'M' hJ'M₀' hM'.le hM₀'.le hM'.toIn hM₀'.toIn hOC
  exact ⟨lcL R u, lcL_le_cu R u, lcL_normal hΩ hc2, lcL_luGroup hP hc hnoU hYo hOu,
    hMM₀ ▸ hM₀L, hM'M₀' ▸ hM₀'L⟩

theorem p23LiftCentF_of_facts (hE : TwinThmE.TwinThmEP n) (hT : TwinThmE.T4Supply)
    (hD4 : TwinCentRes.ModelFactD42) (hM12 : TwinCentRes.ModelFactM12)
    (hRes : Lc.LuResFact) : P23LiftCentF n :=
  p23LiftCentF_of hE hT hD4 hM12 p23YLu_proved Lc.luOutFact hRes Lc.a6AutFact

end YAsm

end CFSG.ClassicalInvolution.Q3.PhilipHall.Frame.TwinPerp23
