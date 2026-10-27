module

public import CFSG.HardMathSupport.Timmesfeld.LangTorus.AlgSetupUntwClass
public import CFSG.HardMathSupport.Timmesfeld.CrossChar.ExcInnerSylow
public import CFSG.HardMathSupport.Timmesfeld.LangTorus.PlanesE7E8

public section

namespace CFSG.HardMathSupport.Timmesfeld.LangTorus

open CFSG.Open CFSG.HardMathSupport.Solomon.LocalBalance CFSG.HardMathSupport.Timmesfeld.Coordinator
  CFSG.HardMathSupport.Timmesfeld.CrossChar CFSG.HardMathSupport.Timmesfeld.LocalTwo
  CFSG.Blueprint CFSG.Blueprint.Chevalley CFSG.LieType.Chevalley CFSG.LieType.AlgebraicGroups
  CFSG.RankThree.PartOne.KE CFSG.HardMathSupport.Timmesfeld.DefChar
  CFSG.LieType.SeitzGeneration CFSG.TauCetiBridge CFSG.RankThree.Lattice Polynomial

set_option linter.unusedSectionVars false

theorem e8SixMat_rel : wordMat Tag.E8 e8SixWord * wordMat Tag.E8 e8SixWord =
    wordMat Tag.E8 e8SixWord - 1 := by
  rw [e8Six_wordMat]
  decide +kernel

theorem langTorusAtAlgClass_E8_of_adjoint {e : ℕ} {R : ℕ → Prop}
    {C : ∀ (L : Type) [Field L] [IsAlgClosed L] (p : ℕ), LangSetup (excTag .E8) L p → Prop}
    (H : ∀ (K : Type) [Field K] [Finite K] (p : ℕ), p.Prime → R p → ¬ p ∣ Nat.card K →
      orderOf ((Nat.card K : ℕ) : ZMod p) = e →
      ∃ (L : Type) (_ : Field L) (_ : IsAlgClosed L) (S : LangSetup Tag.E8 L p),
        S.D.q = Nat.card K ∧ S.IsAlgebraic ∧ C L p S ∧
        (∃ S₀ : Sylow p S.Γ, (S₀ : Subgroup S.Γ) ≤ S.D.torus.subgroupOf S.Γ) ∧
        Nonempty (adjointGroup Tag.E8 K ≃* S.Γ)) :
    LangTorusAtAlgClass .E8 (fun p c => R p ∧ orderOf ((c : ℕ) : ZMod p) = e) C := by
  intro _ q hv p hp ⟨hR, he⟩ hpq
  obtain ⟨K, _, _, hK, -, ⟨eq⟩⟩ := exists_catEquiv_adjointGroup Even.chevalleyBridgesAll.e8 q hv
  have hpK : ¬ p ∣ Nat.card K := by
    rw [hK]
    exact not_dvd_card_of_ne hp hpq
  rw [← hK] at he
  obtain ⟨L, hF, hA, S, hq, hAlg, hC, hsyl, ⟨f⟩⟩ := H K p hp hR hpK he
  exact ⟨L, hF, hA, S, hq.trans hK, hAlg, hC, hsyl, ⟨eq.trans f⟩⟩

theorem langTorusAtAlgClass_E8_six (hF : FrobeniusOnRoots) :
    LangTorusAtAlgClass .E8 (fun p c => 7 ≤ p ∧ orderOf ((c : ℕ) : ZMod p) = 6)
      (fun _ _ _ _ S => S.IsWeylClass (wordMat Tag.E8 e8SixWord)) :=
  langTorusAtAlgClass_E8_of_adjoint fun K _ _ p hp (h7 : 7 ≤ p) hpK he => by
    obtain ⟨L, hL, hA, S, hq, hAlg, hsyl, hε, hcl⟩ :=
      exists_lang_untw_of_blocks_alg_class hF 1 (Or.inr (Or.inr ⟨rfl, rfl⟩)) K hp (by omega) hpK
        (IsWeylMatrix.of_word Tag.E8 e8SixWord) [6, 6, 6, 6] e8Six_charpoly e8Six_pow he
        (not_dvd_of_blocks hp h7 (by decide)) (not_dvd_div_of_720 hp h7 (by decide)) (by decide)
        (CFSG.LieType.Steinberg.Adjoint.isQuasisimple_e8 K).1
    exact ⟨L, hL, hA, S, hq, hAlg, hcl rfl, hsyl, hε⟩

theorem langRigidityForAlgClass_E8_six (hI : CentralizerTrivialAny .E8)
    (hF : NoFrobeniusInnerAny .E8) :
    LangRigidityForAlgClass .E8 (fun p c => 7 ≤ p ∧ 4 ≤ c)
      (fun _ _ _ _ S => S.IsWeylClass (wordMat Tag.E8 e8SixWord)) := by
  intro q hv p L _ _ S hR hSq hAlg hC _
  exact setupRigid_E8_of_pbig S hR.1 hAlg (by rw [hSq]; exact hR.2)
    (S.bigAnyPBig_of_weylClass_hex (Or.inr (Or.inr (Or.inr rfl))) hR.1 e8SixMat_rel hC) hI hF

theorem innerPlaneBalanceAt_E8_six_of_class (hcp : LangComponentPieces)
    (hI : CentralizerTrivialAny .E8) (hF : NoFrobeniusInnerAny .E8)
    (hsmall : InnerPlaneBalanceSmall .E8 6) : InnerPlaneBalanceAt .E8 6 :=
  innerPlaneBalanceAt_of_lang_rigid_alg_split_class trivial
    (langTorusAtAlgClass_E8_six frobeniusOnRoots_proved) (langRigidityForAlgClass_E8_six hI hF)
    hsmall hcp center_catT_E8_eq_bot

end CFSG.HardMathSupport.Timmesfeld.LangTorus
