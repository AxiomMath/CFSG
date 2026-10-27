module

public import CFSG.HardMathSupport.Timmesfeld.LangTorus.BigAnyE8Six
public import CFSG.HardMathSupport.Timmesfeld.LangTorus.BigAnyClassTriQuad

public section

namespace CFSG.HardMathSupport.Timmesfeld.LangTorus

open CFSG.Open CFSG.HardMathSupport.Solomon.LocalBalance CFSG.HardMathSupport.Timmesfeld.Coordinator
  CFSG.HardMathSupport.Timmesfeld.CrossChar CFSG.HardMathSupport.Timmesfeld.LocalTwo
  CFSG.Blueprint CFSG.Blueprint.Chevalley CFSG.LieType.Chevalley CFSG.LieType.AlgebraicGroups
  CFSG.RankThree.PartOne.KE CFSG.HardMathSupport.Timmesfeld.DefChar
  CFSG.LieType.SeitzGeneration CFSG.TauCetiBridge CFSG.RankThree.Lattice Polynomial

set_option linter.unusedSectionVars false


theorem langTorusAtAlgClass_E8_three (hF : FrobeniusOnRoots) :
    LangTorusAtAlgClass .E8 (fun p c => 7 ≤ p ∧ orderOf ((c : ℕ) : ZMod p) = 3)
      (fun _ _ _ _ S => S.IsWeylClass (wordMat Tag.E8 e8ThreeWord)) :=
  langTorusAtAlgClass_E8_of_adjoint fun K _ _ p hp (h7 : 7 ≤ p) hpK he => by
    obtain ⟨L, hL, hA, S, hq, hAlg, hsyl, hε, hcl⟩ :=
      exists_lang_untw_of_blocks_alg_class hF 1 (Or.inr (Or.inr ⟨rfl, rfl⟩)) K hp (by omega) hpK
        (IsWeylMatrix.of_word Tag.E8 e8ThreeWord) [3, 3, 3, 3] e8Three_charpoly e8Three_pow he
        (not_dvd_of_blocks hp h7 (by decide)) (not_dvd_div_of_720 hp h7 (by decide)) (by decide)
        (CFSG.LieType.Steinberg.Adjoint.isQuasisimple_e8 K).1
    exact ⟨L, hL, hA, S, hq, hAlg, hcl rfl, hsyl, hε⟩

theorem langRigidityForAlgClass_E8_three {R : ℕ → ℕ → Prop} (hR : ∀ p c, R p c → 7 ≤ p ∧ 4 ≤ c)
    (hI : CentralizerTrivialAny .E8) (hF : NoFrobeniusInnerAny .E8) :
    LangRigidityForAlgClass .E8 R
      (fun _ _ _ _ S => S.IsWeylClass (wordMat Tag.E8 e8ThreeWord)) := by
  intro q hv p L _ _ S hRp hSq hAlg hC _
  have h := hR p _ hRp
  exact setupRigid_E8_of_pbig S h.1 hAlg (by rw [hSq]; exact h.2)
    (S.bigAnyPBig_of_weylClass_tri (Or.inr (Or.inr (Or.inr rfl))) h.1 e8ThreeMat_rel hC) hI hF

theorem innerPlaneBalanceAt_E8_three_of_class (hcp : LangComponentPieces)
    (hI : CentralizerTrivialAny .E8) (hF : NoFrobeniusInnerAny .E8)
    (hsmall : InnerPlaneBalanceSmall .E8 3) : InnerPlaneBalanceAt .E8 3 :=
  innerPlaneBalanceAt_of_lang_rigid_alg_split_class trivial
    (langTorusAtAlgClass_E8_three frobeniusOnRoots_proved)
    (langRigidityForAlgClass_E8_three (fun _ _ h => h) hI hF) hsmall hcp center_catT_E8_eq_bot

end CFSG.HardMathSupport.Timmesfeld.LangTorus
