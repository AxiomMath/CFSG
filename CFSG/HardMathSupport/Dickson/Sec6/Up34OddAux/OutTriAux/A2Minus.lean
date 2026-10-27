module

public import CFSG.HardMathSupport.Dickson.Sec6.Up34OddAux.OutTriAux.A2
public import CFSG.HardMathSupport.Dickson.Sec6.I923Fam.TriD4A2Aux.UnCore

public section

namespace CFSG.HardMathSupport.Dickson.Sec6.OutTri

open CFSG.Blueprint.Chevalley CFSG.LieType.Chevalley CFSG.LieType.Steinberg
  CFSG.LieType.Steinberg.Adjoint CFSG.LieType.Steinberg.TwistedD4 CFSG.Timmesfeld.RankTwo
  CFSG.GH74.GLS.SP CFSG.GH74.GLS.Stage4.Hex CFSG.GH74.GLS.Stage2.OddAut
  CFSG.LocalAnalysis.ComponentInitial.FourGroupChevalley
  CFSG.LieType.Steinberg.CentralExt.TrialityClosed CFSG.GH74.GLS.Stage2.Signalizer.Odd87
  CFSG.LocalAnalysis.ComponentInitial CFSG.RankThree.Chevalley CFSG.GH74.BNPair
  CFSG.GH74.GLS.Stage2.Bender.Thm1 CFSG.HardMathSupport.Solomon.Coordinator
  CFSG.HardMathSupport.Solomon.Coordinator.LieSemisimple
  CFSG.HardMathSupport.Solomon.Coordinator.LieSemisimple.D4Dual
  CFSG.HardMathSupport.Solomon.UniquenessMaximal
open CFSG.HardMathSupport.Dickson.Sec6 CFSG.HardMathSupport.Dickson.Sec6.I923

set_option linter.unusedSectionVars false


theorem simpleCore_a2_minus {p f : ℕ} (hp : p.Prime) (hp5 : 5 ≤ p) (hf : 1 ≤ f)
    (hq : (p ^ f) % 3 = 2) {K : Type} [Field K] [Finite K] (hK : Nat.card K = (p ^ f) ^ 3)
    (σ : K ≃+* K) (hσ : ∀ c, σ c = c ^ (p ^ f))
    (s : graphFixedRootGroup TwistTag.D4 K σ.toRingHom) (hs : D4MinusToral p f hp K σ s) :
    TriD4A2.SimpleCore
      ↥(fixSubgroup (MulAut.conj s * fieldActor (t := TwistTag.D4) σ σ))
      ((p ^ f) ^ 3) ((p ^ f) ^ 5) := by
  have : Fact p.Prime := ⟨hp⟩
  obtain ⟨K₄, hF, hfin, hCh, hK₄, σ₄, ε, hσ₄, hε, b, hb3, hb1, s₄, hs₄, ψ₄, hinj, hint, hfix⟩ :=
    un_frame hp hf hq K hK σ hσ s hs
  have hSC := TriD4A2.un_polarity_R hp5 hf hq hK₄ σ₄ ε hσ₄ hε b hb3 hb1 s₄ hs₄
  obtain ⟨e, -⟩ := un_fixSub_equiv (MulAut.conj s * fieldActor (t := TwistTag.D4) σ σ)
    (MulAut.conj s₄ * fieldActor (t := TwistTag.D4) σ₄ σ₄) (unTau σ₄ ε) ψ₄ hinj hint hfix
  have ef : ↥(fixSubgroup (MulAut.conj s * fieldActor (t := TwistTag.D4) σ σ)) ≃*
      ↥(fixSub (MulAut.conj s * fieldActor (t := TwistTag.D4) σ σ)) :=
    (MulEquiv.subgroupCongr (fixSub_eq_fixSubgroup _)).symm
  exact TriD4A2.SimpleCore.of_equiv (ef.trans e).symm hSC

theorem noL34Layer_a2_minus {p f : ℕ} (hp : p.Prime) (hp5 : 5 ≤ p) (hf : 1 ≤ f)
    (hq : (p ^ f) % 3 = 2) {K : Type} [Field K] [Finite K] (hK : Nat.card K = (p ^ f) ^ 3)
    (σ : K ≃+* K) (hσ : ∀ c, σ c = c ^ (p ^ f))
    (s : graphFixedRootGroup TwistTag.D4 K σ.toRingHom) (hs : D4MinusToral p f hp K σ s) :
    NoL34Layer (MulAut.conj s * fieldActor (t := TwistTag.D4) σ σ) := by
  haveI := TriD4Aux.finite_graphFixedRootGroup_D4 σ
  obtain ⟨S, hSn, hsol, hsimple, hnab, hxS, -⟩ := simpleCore_a2_minus hp hp5 hf hq hK σ hσ s hs
  haveI := hSn
  have hq5 : 5 ≤ p ^ f := le_trans hp5 (Nat.le_self_pow (by omega) p)
  refine noL34Layer_of_equiv_normal_simple _ (MulEquiv.refl _) S hsol hsimple hnab fun hT => ?_
  have h1 := card_eq_of_isLThreeFour hT
  rw [h1] at hxS
  exact not_cube_dvd_card_L34 hq5 hxS

end CFSG.HardMathSupport.Dickson.Sec6.OutTri

namespace CFSG.HardMathSupport.Dickson.Sec6

set_option linter.unusedSectionVars false


theorem triD4A2Minus34_holds : TriD4A2Minus34 := by
  intro ℓ f hℓ hℓ5 hf hq K _ _ hK σ hσ s hs
  exact OutTri.noL34Layer_a2_minus hℓ hℓ5 hf hq hK σ hσ s hs

end CFSG.HardMathSupport.Dickson.Sec6
