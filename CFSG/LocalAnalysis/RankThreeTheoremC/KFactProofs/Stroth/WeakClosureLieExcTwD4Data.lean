module

public import CFSG.LocalAnalysis.RankThreeTheoremC.KFactProofs.Stroth.WeakClosureLieExcTwWords
public import CFSG.LocalAnalysis.RankThreeTheoremC.KFactProofs.Stroth.WeakClosureLieExcTwNum
public import CFSG.LocalAnalysis.RankThreeTheoremC.KFactProofs.Stroth.WeakClosureLieExcTwD4Setup
public import CFSG.HardMathSupport.Timmesfeld.LangTorus.TorusAtTriD4Classes

public section

namespace CFSG.LocalAnalysis.RankThreeTheoremC.KFactProofs.Stroth.WeakClosure.ExcCross

open CFSG.Open CFSG.HardMathSupport.Solomon.LocalBalance CFSG.HardMathSupport.Timmesfeld.Coordinator
  CFSG.HardMathSupport.Timmesfeld.CrossChar CFSG.HardMathSupport.Timmesfeld.LocalTwo
  CFSG.Blueprint CFSG.Blueprint.Chevalley CFSG.LieType.Chevalley CFSG.LieType.AlgebraicGroups
  CFSG.RankThree.PartOne.KE CFSG.HardMathSupport.Timmesfeld.DefChar
  CFSG.LieType.SeitzGeneration CFSG.TauCetiBridge CFSG.RankThree.PartOne.KGD CFSG.RankThree.Lattice
  CFSG.HardMathSupport.Timmesfeld.LangTorus Polynomial
open scoped Matrix commutatorElement

set_option linter.unusedSectionVars false


theorem tw_not_dvd_three {p : ℕ} (hp5 : 5 ≤ p) {c : ℤ} (hc : c = 3 ∨ c = -3) : ¬ (p : ℤ) ∣ c := by
  intro h
  have h3 : (p : ℤ) ∣ 3 := by
    rcases hc with rfl | rfl
    · exact h
    · exact (dvd_neg.1 h)
  have : p ∣ 3 := by exact_mod_cast h3
  have := Nat.le_of_dvd (by norm_num) this
  omega

@[expose] def d4OneX : List (Fin Tag.D4.rank) := [2]
@[expose] def d4OneY : List (Fin Tag.D4.rank) := [3, 1, 0]
@[expose] def d4OneMl : List (List ℤ) := [[0, 0, 0, 1], [1, 0, 0, 0], [0, 0, 1, 0], [0, 1, 0, 0]]
theorem d4OneM_eq : d4OneM = toMat Tag.D4.rank d4OneMl := by
  ext i j; fin_cases i <;> fin_cases j <;> rfl
theorem d4OneX_comm : toMat Tag.D4.rank d4OneMl * wordMat Tag.D4 d4OneX =
    wordMat Tag.D4 d4OneX * toMat Tag.D4.rank d4OneMl :=
  tw_wordMat_comm_of_check _ _ (by decide +kernel)
theorem d4OneY_comm : toMat Tag.D4.rank d4OneMl * wordMat Tag.D4 d4OneY =
    wordMat Tag.D4 d4OneY * toMat Tag.D4.rank d4OneMl :=
  tw_wordMat_comm_of_check _ _ (by decide +kernel)
@[expose] def d4OneY1 : List (List ℤ) := [[2, -1, 0, -1], [1, 1, 0, -2], [0, 0, 0, 0], [0, 0, 0, 0]]
@[expose] def d4OneY2 : List (List ℤ) := [[3, 3, -3, 3], [0, 0, 0, 0], [1, 1, 0, 1], [0, 0, 0, 0]]
@[expose] def d4Onec : ℤ := -3
theorem d4One_cert : (toMat Tag.D4.rank d4OneMl - (1 : ℤ) • (1 : Matrix (Fin Tag.D4.rank) (Fin Tag.D4.rank) ℤ)) *
    toMat Tag.D4.rank d4OneY1 + (wordMat Tag.D4 (twCommWord d4OneY d4OneX) - 1) *
    toMat Tag.D4.rank d4OneY2 = d4Onec • (1 : Matrix (Fin Tag.D4.rank) (Fin Tag.D4.rank) ℤ) :=
  tw_cert_of_check _ _ _ _ _ _ (by decide +kernel)

@[expose] def d4TwoX : List (Fin Tag.D4.rank) := [0]
@[expose] def d4TwoY : List (Fin Tag.D4.rank) := [2]
@[expose] def d4TwoMl : List (List ℤ) := [[-1, 1, 0, 0], [0, 1, 0, -1], [0, 2, -1, 0], [0, 1, 0, 0]]
theorem d4TwoM_eq : d4TwoM = toMat Tag.D4.rank d4TwoMl := by
  ext i j; fin_cases i <;> fin_cases j <;> rfl
theorem d4TwoX_comm : toMat Tag.D4.rank d4TwoMl * wordMat Tag.D4 d4TwoX =
    wordMat Tag.D4 d4TwoX * toMat Tag.D4.rank d4TwoMl :=
  tw_wordMat_comm_of_check _ _ (by decide +kernel)
theorem d4TwoY_comm : toMat Tag.D4.rank d4TwoMl * wordMat Tag.D4 d4TwoY =
    wordMat Tag.D4 d4TwoY * toMat Tag.D4.rank d4TwoMl :=
  tw_wordMat_comm_of_check _ _ (by decide +kernel)
@[expose] def d4TwoY1 : List (List ℤ) := [[0, 0, 0, 0], [0, 1, 0, 1], [0, 0, 0, 0], [0, -1, 0, 2]]
@[expose] def d4TwoY2 : List (List ℤ) := [[0, 0, 0, 0], [6, 0, -3, 0], [3, 1, -3, 1], [0, 0, 0, 0]]
@[expose] def d4Twoc : ℤ := 3
theorem d4Two_cert : (toMat Tag.D4.rank d4TwoMl - (-1 : ℤ) • (1 : Matrix (Fin Tag.D4.rank) (Fin Tag.D4.rank) ℤ)) *
    toMat Tag.D4.rank d4TwoY1 + (wordMat Tag.D4 (twCommWord d4TwoY d4TwoX) - 1) *
    toMat Tag.D4.rank d4TwoY2 = d4Twoc • (1 : Matrix (Fin Tag.D4.rank) (Fin Tag.D4.rank) ℤ) :=
  tw_cert_of_check _ _ _ _ _ _ (by decide +kernel)

@[expose] def d4ThreeX : List (Fin Tag.D4.rank) := [2, 3, 0, 2, 1, 0]
@[expose] def d4ThreeY : List (Fin Tag.D4.rank) := [3, 2, 1, 0, 2, 0]
@[expose] def d4ThreeMl : List (List ℤ) := [[-1, 1, 0, 0], [-1, 0, 0, 0], [-1, 1, 0, -1], [-1, 0, 1, -1]]
theorem d4ThreeM_eq : d4ThreeM = toMat Tag.D4.rank d4ThreeMl := by
  ext i j; fin_cases i <;> fin_cases j <;> rfl
theorem d4ThreeX_comm : toMat Tag.D4.rank d4ThreeMl * wordMat Tag.D4 d4ThreeX =
    wordMat Tag.D4 d4ThreeX * toMat Tag.D4.rank d4ThreeMl :=
  tw_wordMat_comm_of_check _ _ (by decide +kernel)
theorem d4ThreeY_comm : toMat Tag.D4.rank d4ThreeMl * wordMat Tag.D4 d4ThreeY =
    wordMat Tag.D4 d4ThreeY * toMat Tag.D4.rank d4ThreeMl :=
  tw_wordMat_comm_of_check _ _ (by decide +kernel)
theorem d4Three_mat : wordMat Tag.D4 (twCommWord d4ThreeY d4ThreeX) =
    (-1 : ℤ) • toMat Tag.D4.rank d4ThreeMl ^ 0 :=
  tw_wordMat_eq_smul_pow_of_check _ _ _ _ (by decide +kernel)

@[expose] def d4SixX : List (Fin Tag.D4.rank) := [2, 3, 1, 2, 1, 0]
@[expose] def d4SixY : List (Fin Tag.D4.rank) := [1, 2, 3, 0, 2, 0]
@[expose] def d4SixMl : List (List ℤ) := [[0, 0, 1, -1], [0, 1, 0, -1], [-1, 1, 1, -1], [0, 1, 0, 0]]
theorem d4SixM_eq : d4SixM = toMat Tag.D4.rank d4SixMl := by
  ext i j; fin_cases i <;> fin_cases j <;> rfl
theorem d4SixX_comm : toMat Tag.D4.rank d4SixMl * wordMat Tag.D4 d4SixX =
    wordMat Tag.D4 d4SixX * toMat Tag.D4.rank d4SixMl :=
  tw_wordMat_comm_of_check _ _ (by decide +kernel)
theorem d4SixY_comm : toMat Tag.D4.rank d4SixMl * wordMat Tag.D4 d4SixY =
    wordMat Tag.D4 d4SixY * toMat Tag.D4.rank d4SixMl :=
  tw_wordMat_comm_of_check _ _ (by decide +kernel)
theorem d4Six_mat : wordMat Tag.D4 (twCommWord d4SixY d4SixX) =
    (-1 : ℤ) • toMat Tag.D4.rank d4SixMl ^ 0 :=
  tw_wordMat_eq_smul_pow_of_check _ _ _ _ (by decide +kernel)


section Moves

variable {L : Type} [Field L] [IsAlgClosed L]

theorem d4One_moves (D : LangDatum TwistTag.D4.tag L) {Fr : L →+* L} {q : ℕ} (hq : 2 ≤ q)
    (hFr : ∀ c, Fr c = c ^ q) (hΦ : D.Φ = twistHom TwistTag.D4 L Fr)
    (hn : D.n = canonicalRep (coxeterSystem TwistTag.D4.tag) L
      ((coxeterSystem TwistTag.D4.tag).wordProd d4OneWord))
    (hMΓ : D.model ≤ D.Γ) {p : ℕ} [Fact p.Prime] (hp2 : p ≠ 2) (hp5 : 5 ≤ p)
    (he : orderOf (q : ZMod p) = 1) (S₀ : Sylow p D.Γ)
    (hS₀ : (S₀ : Subgroup D.Γ) ≤ D.torus.subgroupOf D.Γ) :
    NormalizerMovesLines p (S₀ : Subgroup D.Γ) :=
  tw_moves_of_sc_cert D hq hFr hΦ hn
    (by rw [← d4OneM_eq]; exact tw_hv_of_hw d4One_hw) (N := 3) (by norm_num)
    (by rw [← d4OneM_eq]; exact d4One_pow) hMΓ S₀ hS₀ d4OneX_comm d4OneY_comm
    (e' := 1) (tw_dvd_sub_of_orderOf_one Fact.out he) (Y₁ := toMat Tag.D4.rank d4OneY1) (Y₂ := toMat Tag.D4.rank d4OneY2)
    (c := d4Onec) d4One_cert (tw_not_dvd_three hp5 (by norm_num [d4Onec]))

end Moves


section Moves

variable {L : Type} [Field L] [IsAlgClosed L]

theorem d4Two_moves (D : LangDatum TwistTag.D4.tag L) {Fr : L →+* L} {q : ℕ} (hq : 2 ≤ q)
    (hFr : ∀ c, Fr c = c ^ q) (hΦ : D.Φ = twistHom TwistTag.D4 L Fr)
    (hn : D.n = canonicalRep (coxeterSystem TwistTag.D4.tag) L
      ((coxeterSystem TwistTag.D4.tag).wordProd d4TwoWord))
    (hMΓ : D.model ≤ D.Γ) {p : ℕ} [Fact p.Prime] (hp2 : p ≠ 2) (hp5 : 5 ≤ p)
    (he : orderOf (q : ZMod p) = 2) (S₀ : Sylow p D.Γ)
    (hS₀ : (S₀ : Subgroup D.Γ) ≤ D.torus.subgroupOf D.Γ) :
    NormalizerMovesLines p (S₀ : Subgroup D.Γ) :=
  tw_moves_of_sc_cert D hq hFr hΦ hn
    (by rw [← d4TwoM_eq]; exact tw_hv_of_hw d4Two_hw) (N := 6) (by norm_num)
    (by rw [← d4TwoM_eq]; exact d4Two_pow) hMΓ S₀ hS₀ d4TwoX_comm d4TwoY_comm
    (e' := -1) (tw_dvd_add_of_orderOf_two Fact.out hp2 he) (Y₁ := toMat Tag.D4.rank d4TwoY1) (Y₂ := toMat Tag.D4.rank d4TwoY2)
    (c := d4Twoc) d4Two_cert (tw_not_dvd_three hp5 (by norm_num [d4Twoc]))

end Moves


section Moves

variable {L : Type} [Field L] [IsAlgClosed L]

theorem d4Three_moves (D : LangDatum TwistTag.D4.tag L) {Fr : L →+* L} {q : ℕ} (hq : 2 ≤ q)
    (hFr : ∀ c, Fr c = c ^ q) (hΦ : D.Φ = twistHom TwistTag.D4 L Fr)
    (hn : D.n = canonicalRep (coxeterSystem TwistTag.D4.tag) L
      ((coxeterSystem TwistTag.D4.tag).wordProd d4ThreeWord))
    (hMΓ : D.model ≤ D.Γ) {p : ℕ} [Fact p.Prime] (hp2 : p ≠ 2) 
    (he : orderOf (q : ZMod p) = 3) (S₀ : Sylow p D.Γ)
    (hS₀ : (S₀ : Subgroup D.Γ) ≤ D.torus.subgroupOf D.Γ) :
    NormalizerMovesLines p (S₀ : Subgroup D.Γ) :=
  tw_moves_of_sc_scalar D hq hFr hΦ hn
    (by rw [← d4ThreeM_eq]; exact tw_hv_of_hw d4Three_hw) (N := 3) (by norm_num)
    (by rw [← d4ThreeM_eq]; exact d4Three_pow) hMΓ S₀ hS₀ d4ThreeX_comm d4ThreeY_comm
    d4Three_mat (tw_not_dvd_sign_pow (s := -1) (k := 0) Fact.out hp2 he (Or.inl ⟨rfl, dvd_zero _⟩))

end Moves


section Moves

variable {L : Type} [Field L] [IsAlgClosed L]

theorem d4Six_moves (D : LangDatum TwistTag.D4.tag L) {Fr : L →+* L} {q : ℕ} (hq : 2 ≤ q)
    (hFr : ∀ c, Fr c = c ^ q) (hΦ : D.Φ = twistHom TwistTag.D4 L Fr)
    (hn : D.n = canonicalRep (coxeterSystem TwistTag.D4.tag) L
      ((coxeterSystem TwistTag.D4.tag).wordProd d4SixWord))
    (hMΓ : D.model ≤ D.Γ) {p : ℕ} [Fact p.Prime] (hp2 : p ≠ 2) 
    (he : orderOf (q : ZMod p) = 6) (S₀ : Sylow p D.Γ)
    (hS₀ : (S₀ : Subgroup D.Γ) ≤ D.torus.subgroupOf D.Γ) :
    NormalizerMovesLines p (S₀ : Subgroup D.Γ) :=
  tw_moves_of_sc_scalar D hq hFr hΦ hn
    (by rw [← d4SixM_eq]; exact tw_hv_of_hw d4Six_hw) (N := 6) (by norm_num)
    (by rw [← d4SixM_eq]; exact d4Six_pow) hMΓ S₀ hS₀ d4SixX_comm d4SixY_comm
    d4Six_mat (tw_not_dvd_sign_pow (s := -1) (k := 0) Fact.out hp2 he (Or.inl ⟨rfl, dvd_zero _⟩))

end Moves

end CFSG.LocalAnalysis.RankThreeTheoremC.KFactProofs.Stroth.WeakClosure.ExcCross
