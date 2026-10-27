module

public import CFSG.LocalAnalysis.GLTheoremA.CatA.S265QCfg
public import CFSG.LocalAnalysis.GLTheoremA.CatA.D4YCDefs
import CFSG.LocalAnalysis.GLTheoremA.CatA.S265FAut
import CFSG.LocalAnalysis.GLTheoremA.CatA.D4XFIso
import CFSG.LocalAnalysis.AGLEmbedding.KFactProofs.CenterHopf
import CFSG.LieType.Steinberg.CentralExt.POmegaPlusMultiplier
import CFSG.HardMathSupport.Solomon.Coordinator.ChevQ.KS.ExactD
import CFSG.HardMathSupport.Timmesfeld.CrossChar.OrthD4Field
public import CFSG.Blueprint.MultiplierDefs

public section

namespace CFSG.LocalAnalysis.GLTheoremA.S265

open CFSG.Open CFSG.Yardstones.Md0ec50421ce4 CFSG.LocalAnalysis.GLTheoremB
open CFSG.LocalAnalysis.GLTheoremA

variable {Ω : Type} [Group Ω] [Finite Ω] {S B T : Subgroup Ω} {x b : Ω}

theorem QUCfg.center_eq_bot_of_d4eight (cfg : QUCfg 3 S B T x b)
    (hS8 : StatedClassicalModel (PSimple 3 S) .POmegaPlus 4 2 3) : Subgroup.center ↥S = ⊥ := by
  obtain ⟨-, K, _, _, hK, ⟨θ⟩⟩ := hS8
  obtain ⟨-, ⟨eM⟩⟩ := CFSG.LieType.Steinberg.CentralExt.SpinPlusClosed.pomegaPlus_hopfMultiplier
    (n := 4) (K := K) (by norm_num) hK (by rw [hK]; norm_num)
  have hdvd := CFSG.AGLEmbedding.card_center_dvd_card_griessHopfMultiplier ⟨cfg.quasi.1⟩
    ((qu_pSimpleEquiv cfg.core).symm.trans θ)
  have h1 : Nat.card (CFSG.Blueprint.Multiplier.generic .POmegaPlus 4 2 3) = 1 := by
    simp [CFSG.Blueprint.Multiplier.genericOrders, show Even 8 from ⟨4, rfl⟩]
  rw [Nat.card_congr eM.toEquiv, h1, Nat.dvd_one] at hdvd
  exact Subgroup.eq_bot_of_card_eq _ hdvd

private noncomputable def selfEquiv (cfg : QUCfg 3 S B T x b) (hZ : Subgroup.center ↥S = ⊥) :
    PSimple 3 S ≃* ↥S :=
  (qu_pSimpleEquiv cfg.core).trans
    ((QuotientGroup.quotientMulEquivOfEq hZ).trans QuotientGroup.quotientBot)

open CFSG.HardMathSupport.Solomon.Coordinator.ChevQ.KSExact in
private theorem catalogIs_isD4any {G : Type} [Group G]
    (h : StatedClassicalModel G .POmegaPlus 4 2 3) : catalogIs G isD4any := by
  obtain ⟨q, hv, hq, -, ⟨e⟩⟩ := exists_D_of_statedClassicalModel_POmegaPlus h
  exact ⟨TauCeti.CFSGIndex.lie ⟨.D 4 q, hv⟩, hq, ⟨e⟩⟩

private theorem not_catalogIs_isD4two {G : Type} [Group G]
    (h : StatedClassicalModel G .POmegaPlus 4 2 3) : ¬ catalogIs G S9.isD4two := fun h2 => by
  have e1 := CFSG.HardMathSupport.Timmesfeld.CrossChar.card_model_plus h
  have e2 := CFSG.HardMathSupport.Timmesfeld.CrossChar.card_model_plus
    (D4XF.statedModel_of_d4two h2)
  rw [e1] at e2
  revert e2
  decide

theorem QUCfg.not_notCentralOut (hcore : D4Y.D4BigCoreAt) (cfg : QUCfg 3 S B T x b)
    (hS8 : StatedClassicalModel (PSimple 3 S) .POmegaPlus 4 2 3) {e : Ω} (he : e ∈ B)
    (heS : e ∈ Subgroup.normalizer (S : Set Ω)) :
    ¬ D4Y.NotCentralOut (D4T.conjAut S e heS) := by
  intro hNC
  have hZ := cfg.center_eq_bot_of_d4eight hS8
  have hcatK : catalogIs ↥S isD4any := by
    obtain ⟨i, hi, ⟨f⟩⟩ := catalogIs_isD4any hS8
    exact ⟨i, hi, ⟨(selfEquiv cfg hZ).symm.trans f⟩⟩
  have hnotK : ¬ catalogIs ↥S S9.isD4two := fun ⟨i, hi, ⟨f⟩⟩ =>
    not_catalogIs_isD4two hS8 ⟨i, hi, ⟨(selfEquiv cfg hZ).trans f⟩⟩
  have hKc : ∀ k ∈ S, (∀ y ∈ S, y * k = k * y) → k = 1 := by
    intro k hk hcomm
    have hc : (⟨k, hk⟩ : ↥S) ∈ Subgroup.center ↥S :=
      Subgroup.mem_center_iff.2 fun y => Subtype.ext (hcomm y y.2)
    rw [hZ, Subgroup.mem_bot] at hc
    exact congrArg Subtype.val hc
  have hNS : ∀ g : Ω, g ∈ Subgroup.normalizer (S : Set Ω) := fun g =>
    (Subgroup.normalizer_eq_top_iff.2 cfg.normal).symm ▸ Subgroup.mem_top g
  refine hcore Ω S B hcatK hnotK hKc cfg.elem (fun g _ => hNS g) ⟨e, he, heS, hNC⟩ ?_
  rcases cfg.maxc with hTB | hmax
  · obtain ⟨-, hT2, hBT, -⟩ := S9.l94t_commutator_facts cfg.elem cfg.two cfg.bnorm
    exact Or.inr ⟨fun P W hP hW2 hWne hPW =>
      (card_le_pow_glaTwoLocalRank Nat.prime_three hP hWne hW2 hPW).trans cfg.rank,
      ⁅T, B⁆, hT2, hTB, hBT, fun g _ => hNS g⟩
  · exact Or.inl hmax

end CFSG.LocalAnalysis.GLTheoremA.S265

end
