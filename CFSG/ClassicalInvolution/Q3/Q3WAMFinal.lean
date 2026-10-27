module

public import CFSG.ClassicalInvolution.Q3.Q3WAMulti
public import CFSG.ClassicalInvolution.Q3.Q3WAMBase
public import CFSG.ClassicalInvolution.Q3.Q3WAMOrth
public import CFSG.ClassicalInvolution.Q3.Q3WAMExc
public import CFSG.ClassicalInvolution.RouteD.MultiModelFacts
public import CFSG.ClassicalInvolution.RouteD.MultiModelShortU5
public import CFSG.ClassicalInvolution.RouteD.MultiModelShortE6
public import CFSG.LocalAnalysis.ComponentClassification.RankTwoOddLieDefs
public import CFSG.LocalAnalysis.ComponentClassification.RankTwoStandardDefs

public section

namespace CFSG.ClassicalInvolution.Q3.Q3W

open CFSG.ClassicalInvolution CFSG.ClassicalInvolution.Generic CFSG.ClassicalInvolution.RouteD
  CFSG.Assembly.LowTwoRank
open CFSG.ClassicalInvolution.WeakCT (LinearBlockStandardPair)

section Facts

theorem modelConnFactNe3_proved : ModelConnFactNe3 := by
  intro t n hfund hadm hG2 hD4 R hR R₁ hR₁ R₂ hR₂ hne h1 h2 h12
  have hp2 : (3 : ℕ) ≠ 2 := by norm_num
  by_cases hg : ConnGeneric t n
  · exact commFamilyConnected_of_generic hp2 hadm hg
  by_cases hs : ConnShort t n
  · exact commFamilyConnected_of_short hp2 hadm hs
  by_cases hx : ConnExotic t n
  · rcases hx with ⟨rfl, rfl⟩ | rfl
    · exact commFamilyConnected_psu_five hp2 hadm
    · obtain rfl : n = 0 := hadm.2.2
      exact commFamilyConnected_twistedE6 hp2 hadm
  exfalso
  rcases small_model_cases hfund hadm hG2 hD4 hg hs hx with
    ⟨rfl, hn⟩ | ⟨rfl, hn⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩
  · exact hne (eq_of_commutes_commutes_psl_small3 hadm hn hR hR₁ hR₂ h1 h2)
  · exact hne (eq_of_commutes_commutes_psu_small3 hadm hn hR hR₁ hR₂ h1 h2)
  · exact hne (eq_of_commutes_commutes_psp_two3 hadm hR hR₁ hR₂ h1 h2)
  · rcases modelLayer_pOmegaOdd3 R hR R₁ hR₁ R₂ hR₂ h1 h2 with h | h
    · exact hne h
    · exact h12 h
  · rcases modelLayer_pOmegaPlus3 R hR R₁ hR₁ R₂ hR₂ h1 h2 with h | h
    · exact hne h
    · exact h12 h
  · rcases modelLayer_pOmegaMinus3 R hR R₁ hR₁ R₂ hR₂ h1 h2 with h | h
    · exact hne h
    · exact h12 h

theorem modelStarFact3_of_layer (hTw : TwistedE6Layer3) : ModelStarFact3 := by
  intro t n hfund hadm hG2 hD4 R hR R₁ hR₁ R₂ hR₂ R_q hRq h1 h2 h12 hnl hq1 hq2 hq3
  have key : ∃ R_β ∈ ModelFund 3 t n 1,
        (∃ W, LinearBlockStandardPair (GaloisField 3 1) W R R_β) ∧
        (∃ W, LinearBlockStandardPair (GaloisField 3 1) W R₁ R_β) ∧
        (∃ W, LinearBlockStandardPair (GaloisField 3 1) W R₂ R_β) := by
    by_cases hP : t = .POmegaPlus
    · subst hP
      exact modelStar_pOmegaPlus3 hadm.2.2 R hR R₁ hR₁ R₂ hR₂ h1 h2 h12 hnl
    by_cases hO : t = .POmegaOdd
    · subst hO
      exact modelStar_pOmegaOdd3 hadm.2.2.1 R hR R₁ hR₁ R₂ hR₂ h1 h2 h12 hnl
    by_cases hM : t = .POmegaMinus
    · subst hM
      exact modelStar_pOmegaMinus3 hadm R hR R₁ hR₁ R₂ hR₂ h1 h2 h12 hnl
    exfalso
    apply hnl
    by_cases hX : t = .F4 ∨ t = .E6 ∨ t = .E7 ∨ t = .E8 ∨ t = .twistedE6
    · exact linkedIn_modelFund_exceptional3 hX (hasLayer3_exc hTw hX hadm) hadm hR hR₁ hR₂
        h1.symm h2.symm
    have hcl : t = .PSL ∨ t = .PSU ∨ t = .PSp := by
      cases t <;> simp_all [IsFundTag]
    rcases hcl with rfl | rfl | rfl
    · exact linkedIn_modelFund_psl3 hadm hR hR₁ hR₂ h1 h2 h12
    · exact linkedIn_modelFund_psu3 hadm hR hR₁ hR₂ h1 h2 h12
    · exact linkedIn_modelFund_psp3 hadm hR hR₁ hR₂ h1 h2 h12
  obtain ⟨R_β, hRβ, a, b, c⟩ := key
  exact ⟨R_β, hRβ, R₁, hR₁, R₂, hR₂, Relation.ReflTransGen.refl, Relation.ReflTransGen.refl,
    a, b, c⟩

theorem modelStarFact3_proved : ModelStarFact3 :=
  modelStarFact3_of_layer twistedE6Layer3_proved

end Facts

end CFSG.ClassicalInvolution.Q3.Q3W
