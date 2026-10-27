module

public import CFSG.GH74.GLS.Stage2.Bender.Thm1.P67D4A2Defs
public import CFSG.RankThree.Chevalley.SteinbergCBTrialityOpposition
public import CFSG.GH74.GLS.Stage2.Bender.Thm1.P67Core
public import CFSG.GH74.GLS.Stage2.Bender.Thm1.P67CoreTools
public import CFSG.GH74.GLS.Stage2.Bender.Thm1.P67D4Field
public import CFSG.GH74.GLS.Stage2.Bender.Thm1.P67D4OutStage

public noncomputable section

namespace CFSG.GH74.GLS.Stage2.Bender.Thm1

open CFSG.Blueprint.Chevalley CFSG.LieType.Chevalley CFSG.RankThree.Chevalley

@[expose] def unZ (K : Type) [Field K] (σ : K →+* K) : graphFixedRootGroup TwistTag.D4 K σ :=
  ⟨trialityOpposition K, trialityOpposition_mem_graphFixedRootGroup σ⟩

theorem coe_unZ (K : Type) [Field K] (σ : K →+* K) :
    ((unZ K σ : graphFixedRootGroup TwistTag.D4 K σ) : ModGL TwistTag.D4.tag K) =
      trialityOpposition K := rfl

@[expose] def unTau {K : Type} [Field K] [Finite K] (σ ε : K ≃+* K) :
    MulAut (graphFixedRootGroup TwistTag.D4 K σ.toRingHom) :=
  MulAut.conj (unZ K σ.toRingHom) * fieldActor (t := TwistTag.D4) σ ε

theorem unTau_apply {K : Type} [Field K] [Finite K] (σ ε : K ≃+* K)
    (y : graphFixedRootGroup TwistTag.D4 K σ.toRingHom) :
    unTau σ ε y = unZ K σ.toRingHom * fieldActor (t := TwistTag.D4) σ ε y *
      (unZ K σ.toRingHom)⁻¹ := rfl

end CFSG.GH74.GLS.Stage2.Bender.Thm1
