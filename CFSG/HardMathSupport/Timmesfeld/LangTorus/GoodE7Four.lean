module

public import CFSG.HardMathSupport.Timmesfeld.LangTorus.GoodWiring

public section

namespace CFSG.HardMathSupport.Timmesfeld.LangTorus

open CFSG.Open CFSG.HardMathSupport.Solomon.LocalBalance CFSG.HardMathSupport.Timmesfeld.Coordinator
  CFSG.HardMathSupport.Timmesfeld.CrossChar CFSG.HardMathSupport.Timmesfeld.LocalTwo
  CFSG.Blueprint CFSG.Blueprint.Chevalley CFSG.LieType.Chevalley CFSG.LieType.AlgebraicGroups
  CFSG.RankThree.PartOne.KE CFSG.HardMathSupport.Timmesfeld.DefChar
  CFSG.LieType.SeitzGeneration CFSG.TauCetiBridge CFSG.RankThree.Lattice Polynomial
open scoped Matrix

set_option linter.unusedSectionVars false



@[expose] def e7FourBWord : List (Fin Tag.E7.rank) :=
  [4, 3, 4, 6, 1, 3, 2]

@[expose] def e7FourBMat : List (List ℤ) :=
  [[1, 0, 0, 0, 0, 0, 0], [1, 0, -1, 0, 1, 0, 0], [1, 0, -1, 1, 0, 0, 0], [2, 0, -2, 1, 0, 1, 0], [1, -1, -1, 1, 0, 1, 0], [0, 0, 0, 0, 0, 1, 0], [0, 0, 0, 0, 0, 1, -1]]

@[expose] def e7FourBBasis : List (List ℤ) :=
  [[-2, -2, 0, -1, -1, 0, 0], [0, -1, 0, 0, -1, 0, 0], [-1, -2, 0, 0, -1, 0, 0], [0, -2, 0, 0, -2, 0, -1], [1, -1, 0, 0, -1, 0, -1], [2, 0, 0, 0, 0, -1, -1], [1, 0, -1, 0, 0, 0, -1]]

@[expose] def e7FourBBasisInv : List (List ℤ) :=
  [[0, 1, 0, -1, 1, 0, 0], [0, 0, -1, 1, -1, 0, 0], [0, -1, 0, 0, 1, 0, -1], [-1, -1, 1, 1, -1, 0, 0], [0, -1, 1, -1, 1, 0, 0], [0, 0, 0, -1, 2, -1, 0], [0, 2, 0, -1, 0, 0, 0]]

theorem e7FourB_wordMat : wordMat Tag.E7 e7FourBWord = toMat Tag.E7.rank e7FourBMat :=
  wordMat_eq_toMat Tag.E7 _ (by decide +kernel)

theorem e7FourB_pow : (wordMat Tag.E7 e7FourBWord) ^ 4 = 1 := by
  rw [e7FourB_wordMat, ← toMat_lpow, ← toMat_lid]
  exact congrArg (toMat Tag.E7.rank) (by decide +kernel)

theorem e7FourB_charpoly :
    (wordMat Tag.E7 e7FourBWord).charpoly = ([1, 1, 2, 4, 4].map fun d => cyclotomic d ℤ).prod := by
  rw [e7FourB_wordMat]
  exact charpoly_of_basis e7FourBMat e7FourBBasis e7FourBBasisInv [1, 1, 2, 4, 4]
    (by decide) (by decide) (by decide +kernel) (by decide +kernel)

@[expose] def e7FourBCert : List (ℕ × ℕ × ℕ) :=
  [(63, 5, 6), (0, 5, 28), (99, 5, 34), (100, 5, 36), (103, 5, 39), (109, 5, 43), (1, 5, 49), (2, 5, 54), (3, 5, 58), (4, 5, 61), (121, 5, 64), (122, 5, 67), (123, 5, 71), (124, 5, 76), (16, 5, 82), (22, 5, 86), (25, 5, 89), (26, 5, 91), (125, 5, 97), (62, 5, 119), (95, 9, 34), (96, 9, 36), (7, 9, 58), (8, 9, 61), (117, 9, 64), (118, 9, 67), (29, 9, 89), (30, 9, 91), (94, 12, 34), (11, 12, 61), (114, 12, 64), (31, 12, 91), (93, 18, 34), (17, 18, 61), (108, 18, 64), (32, 18, 91), (33, 34, 61), (92, 34, 64)]

theorem e7FourB_classCheck :
    classCheck Tag.E7.rank (cartanList Tag.E7) e7FourBMat Tag.E7.artifactRoots 4 e7FourBCert = true := by
  decide +kernel

section Rigid

variable {L : Type} [Field L] [IsAlgClosed L] {p : ℕ}

theorem setupRigid_E7_four (S : LangSetup .E7 L p) (hp7 : 7 ≤ p) (hAlg : S.IsAlgebraic)
    (he : orderOf ((S.D.q : ℕ) : ZMod p) = 4) (hρ : RhoIs S e7FourBMat) : SetupRigid S :=
  setupRigid_E7_of_check S hp7 hAlg
    (three_le_q_of_class S hp7 (Or.inr (Or.inr (Or.inl rfl))) he) he hρ e7FourB_classCheck

end Rigid

theorem langTorusAtAlgM_E7_4 (hF : FrobeniusOnRoots) :
    LangTorusAtAlgM .E7 (fun p c => 7 ≤ p ∧ orderOf ((c : ℕ) : ZMod p) = 4) e7FourBMat :=
  langTorusAtAlgM_E7_of_adjoint e7FourBMat fun K _ _ p hp (h7 : 7 ≤ p) hpK he => by
    obtain ⟨L, hF', hA', S, hq, hAlg, hρ, hsyl, hequiv⟩ :=
      exists_lang_untw_of_blocks_alg_rho hF 2 (Or.inr (Or.inl ⟨rfl, rfl⟩)) K hp (by omega) hpK
      (IsWeylMatrix.of_word Tag.E7 e7FourBWord) [1, 1, 2, 4, 4] e7FourB_charpoly e7FourB_pow he
      (not_dvd_of_blocks hp h7 (by decide)) (not_dvd_div_of_720 hp h7 (by decide)) (by decide)
      (CFSG.LieType.Simplicity.isQuasisimple_adjointGroup_e7 K).1
    refine ⟨L, hF', hA', S, hq, hAlg, fun γ hγ => ?_, hsyl, hequiv⟩
    rw [hρ γ hγ, e7FourB_wordMat]

theorem langRigidityForAlgM_E7_four :
    LangRigidityForAlgM .E7 (fun p c => 7 ≤ p ∧ orderOf ((c : ℕ) : ZMod p) = 4) e7FourBMat :=
  fun _ _ _ _ _ _ S hR hq hAlg hρ _ =>
    setupRigid_E7_four S (by have := hR.1; omega) hAlg (by rw [hq]; exact hR.2) hρ

theorem innerPlaneBalanceAtP_E7_four (hF : FrobeniusOnRoots) (hcp : LangComponentPieces)
    (hZ : ∀ (q : TauCeti.PrimePower) (hv : (excIndex .E7 q).Valid),
      Subgroup.center (CatT ⟨excIndex .E7 q, hv⟩) = ⊥) :
    InnerPlaneBalanceAtP .E7 4 fun p => 7 ≤ p :=
  innerPlaneBalanceAtP_of_lang_rigid_algM (k := .E7) trivial (langTorusAtAlgM_E7_4 hF)
    langRigidityForAlgM_E7_four hcp hZ

end CFSG.HardMathSupport.Timmesfeld.LangTorus
