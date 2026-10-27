module

public import CFSG.HardMathSupport.Dickson.Sec6.I923Fam.R2Aux.TransportTop
public import CFSG.HardMathSupport.Dickson.Sec6.I923Fam.R2Aux.G2NoComp
public import CFSG.HardMathSupport.Dickson.Sec6.Up34OddAux.Layer

public section

namespace CFSG.HardMathSupport.Dickson.Sec6.I923

open CFSG.Blueprint CFSG.Blueprint.Chevalley CFSG.LieType.Chevalley CFSG.Open
open CFSG.HardMathSupport.Dickson.DefCharOuter.TrialityChar3
open CFSG.HardMathSupport.Dickson.Sec6.I923.TriD4Aux
open CFSG.HardMathSupport.Solomon.Coordinator
open CFSG.HardMathSupport.Dickson.Sec6 (NoL34Layer)

set_option linter.unusedSectionVars false

section Final


theorem triD4C3_noGLAP3 {f : ℕ} (hf : 1 ≤ f) {K : Type} [Field K] [Finite K] [CharP K 3]
    (hK : Nat.card K = (3 ^ f) ^ 3) (σ : K ≃+* K) (hσ : ∀ c, σ c = c ^ (3 ^ f)) {c : K}
    (hc : σ c = c) (hc0 : c ≠ 0) :
    ∀ A : Subgroup (graphFixedRootGroup TwistTag.D4 K σ.toRingHom),
      ¬ GLAPComponent 3 (fixSubgroup (MulAut.conj (longElt hf hK σ hσ (Or.inr (Or.inr rfl)) c hc) *
        fieldActor (t := TwistTag.D4) σ σ)) A := by
  haveI := finite_graphFixedRootGroup_D4 σ
  haveI : Finite (adjointGroup Tag.G2 (fixSubfield σ)) := generated_group_finite Tag.G2 _
  rw [fixSubgroup_conj_mul_fieldActor_eq hf hK σ hσ hc hc0]
  have hzJ := R2Aux.longElt_mem_fix hf hK σ hσ (Or.inr (Or.inr rfl)) hc
  refine R2Aux.noGLAP3_of_equiv
    (R2Aux.infCentralizerEquiv (fixSubgroup (fieldActor (t := TwistTag.D4) σ σ))
      (longElt hf hK σ hσ (Or.inr (Or.inr rfl)) c hc) hzJ (R2Aux.fixEquivG2 hf hK σ hσ)) ?_
  obtain ⟨h, c'', hc'', hE⟩ := R2Aux.exists_conj_g2Top hf hK σ hσ hc hc0
  rw [hE]
  refine R2Aux.noGLAP3_centralizer_conj h _ ?_
  have hcard : Nat.card (fixSubfield σ) = 3 ^ f :=
    CFSG.RankThree.PartOne.KGD.card_fixSubfield_cube Nat.prime_three hf hK σ hσ
  haveI : CharP (fixSubfield σ) 3 := inferInstance
  exact R2Aux.noGLAP3_centralizer_g2Top (K := fixSubfield σ)
    (by rw [hcard]; exact Nat.le_self_pow (by omega) 3) hc''

theorem triD4C3NoL34_holds :
    ∀ (f : ℕ) (hf : 1 ≤ f) (K : Type) [Field K] [Finite K] [CharP K 3]
      (hK : Nat.card K = (3 ^ f) ^ 3) (σ : K ≃+* K) (hσ : ∀ c, σ c = c ^ (3 ^ f)) (c : K)
      (hc : σ c = c), c ≠ 0 →
        NoL34Layer (MulAut.conj (longElt hf hK σ hσ (Or.inr (Or.inr rfl)) c hc) *
          fieldActor (t := TwistTag.D4) σ σ) := by
  intro f hf K _ _ _ hK σ hσ c hc hc0 A hA _
  exact triD4C3_noGLAP3 hf hK σ hσ hc hc0 A hA

end Final

end CFSG.HardMathSupport.Dickson.Sec6.I923
