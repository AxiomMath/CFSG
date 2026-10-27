module

public import CFSG.LocalAnalysis.RankThreeTheoremC.KFactProofs.Stroth.WeakClosureLieExcTwD4Data
public import CFSG.ClassicalInvolution.SmallCases.UpgradeCoverClassical
public import CFSG.LieType.SeitzGeneration.ExcTorusTwE6Four
public import CFSG.LieType.SeitzGeneration.ExcTorusTwE6One
public import CFSG.LieType.SeitzGeneration.ExcTorusTwE6Six
public import CFSG.LieType.SeitzGeneration.ExcTorusTwE6Three
public import CFSG.LieType.SeitzGeneration.ExcTorusTwE6Two

public section

namespace CFSG.LocalAnalysis.RankThreeTheoremC.KFactProofs.Stroth.WeakClosure.ExcCross

open CFSG.Open CFSG.HardMathSupport.Solomon.LocalBalance CFSG.HardMathSupport.Timmesfeld.Coordinator
  CFSG.HardMathSupport.Timmesfeld.CrossChar CFSG.HardMathSupport.Timmesfeld.LocalTwo
  CFSG.Blueprint CFSG.Blueprint.Chevalley CFSG.LieType.Chevalley CFSG.LieType.AlgebraicGroups
  CFSG.RankThree.PartOne.KE CFSG.HardMathSupport.Timmesfeld.DefChar
  CFSG.LieType.SeitzGeneration CFSG.TauCetiBridge CFSG.RankThree.Classical2 CFSG.RankThree.Lattice
  CFSG.HardMathSupport.Timmesfeld.LangTorus Polynomial
open scoped Matrix commutatorElement

set_option linter.unusedSectionVars false

theorem e6_perm_symm : TwistTag.E6.perm.symm = TwistTag.E6.perm := by decide


theorem tw_E6_hv {w : WeylGroup TwistTag.E6.tag}
    {M : Matrix (Fin TwistTag.E6.tag.rank) (Fin TwistTag.E6.tag.rank) ℤ}
    (hw : ∀ x, w • x = M *ᵥ permLattice TwistTag.E6.perm x) :
    ∀ x, w • permLattice TwistTag.E6.perm x = M *ᵥ x :=
  tw_hv_of_hw (by rw [e6_perm_symm]; exact hw)

section Moves

variable {L : Type} [Field L] [IsAlgClosed L]

theorem e6One_hv : ∀ x, ((coxeterSystem TwistTag.E6.tag).wordProd twE6OneWord) • x =
    toMat TwistTag.E6.tag.rank twE6OneMat *ᵥ permLattice TwistTag.E6.perm x := fun x => by
  rw [wordProd_smul_eq_wordMat_mulVec, twE6One_wordMat, toMat_lmul, permLattice_E6_eq,
    Matrix.mulVec_mulVec]
@[expose] def e6OneA : List (Fin TwistTag.E6.tag.rank) := [4, 2, 3]
@[expose] def e6OneB : List (Fin TwistTag.E6.tag.rank) := [3]
@[expose] def e6OneC : List (Fin TwistTag.E6.tag.rank) := [1, 3, 1]
@[expose] def e6OneD : List (Fin TwistTag.E6.tag.rank) := [4, 1]
theorem e6OneA_comm : toMat TwistTag.E6.tag.rank twE6OneMat * wordMat TwistTag.E6.tag e6OneA =
    wordMat TwistTag.E6.tag e6OneA * toMat TwistTag.E6.tag.rank twE6OneMat :=
  tw_wordMat_comm_of_check _ _ (by decide +kernel)
theorem e6OneB_comm : toMat TwistTag.E6.tag.rank twE6OneMat * wordMat TwistTag.E6.tag e6OneB =
    wordMat TwistTag.E6.tag e6OneB * toMat TwistTag.E6.tag.rank twE6OneMat :=
  tw_wordMat_comm_of_check _ _ (by decide +kernel)
theorem e6OneC_comm : toMat TwistTag.E6.tag.rank twE6OneMat * wordMat TwistTag.E6.tag e6OneC =
    wordMat TwistTag.E6.tag e6OneC * toMat TwistTag.E6.tag.rank twE6OneMat :=
  tw_wordMat_comm_of_check _ _ (by decide +kernel)
theorem e6OneD_comm : toMat TwistTag.E6.tag.rank twE6OneMat * wordMat TwistTag.E6.tag e6OneD =
    wordMat TwistTag.E6.tag e6OneD * toMat TwistTag.E6.tag.rank twE6OneMat :=
  tw_wordMat_comm_of_check _ _ (by decide +kernel)
theorem e6One_mat : wordMat TwistTag.E6.tag
    (twCommWord (twCommWord e6OneC e6OneD) (twCommWord e6OneA e6OneB)) =
    (-1 : ℤ) • toMat TwistTag.E6.tag.rank twE6OneMat ^ 1 :=
  tw_wordMat_eq_smul_pow_of_check _ _ _ _ (by decide +kernel)
theorem e6One_moves (D : LangDatum TwistTag.E6.tag L) {Fr : L →+* L} {q : ℕ} (hq : 2 ≤ q)
    (hFr : ∀ c, Fr c = c ^ q) (hΦ : D.Φ = twistHom TwistTag.E6 L Fr)
    (hn : D.n = canonicalRep (coxeterSystem TwistTag.E6.tag) L
      ((coxeterSystem TwistTag.E6.tag).wordProd twE6OneWord)) {p : ℕ} [Fact p.Prime]
    (hp2 : p ≠ 2) (he : orderOf (q : ZMod p) = 1) (S₀ : Sylow p D.Γ)
    (hS₀ : (S₀ : Subgroup D.Γ) ≤ D.torus.subgroupOf D.Γ) :
    NormalizerMovesLines p (S₀ : Subgroup D.Γ) :=
  tw_moves_of_dc_scalar D hq hFr hΦ hn (M := toMat TwistTag.E6.tag.rank twE6OneMat) (tw_E6_hv e6One_hv)
    (N := 2) (by norm_num) twE6One_pow S₀ hS₀ e6OneA_comm e6OneB_comm e6OneC_comm
    e6OneD_comm e6One_mat (tw_not_dvd_sign_pow (s := -1) (k := 1) Fact.out hp2 he (Or.inl ⟨rfl, ⟨1, by norm_num⟩⟩))

theorem e6Two_hv : ∀ x, ((coxeterSystem TwistTag.E6.tag).wordProd twE6TwoWord) • x =
    toMat TwistTag.E6.tag.rank twE6TwoMat *ᵥ permLattice TwistTag.E6.perm x := fun x => by
  rw [wordProd_smul_eq_wordMat_mulVec, twE6Two_wordMat, toMat_lmul, permLattice_E6_eq,
    Matrix.mulVec_mulVec]
@[expose] def e6TwoA : List (Fin TwistTag.E6.tag.rank) := [3, 4, 2, 3, 0, 2, 1, 3, 4, 5, 4, 3, 2, 1, 3, 4, 2, 3, 0, 2, 1, 3, 0, 2, 0]
@[expose] def e6TwoB : List (Fin TwistTag.E6.tag.rank) := [4, 5, 3, 4, 2, 3, 0, 2, 1, 3, 4, 5, 3, 4, 2, 3, 2]
@[expose] def e6TwoC : List (Fin TwistTag.E6.tag.rank) := [3, 4, 2, 3, 0, 2, 1, 3, 4, 5, 4, 2, 3, 0, 2, 1, 3, 4, 2, 3, 0, 2, 1, 0]
@[expose] def e6TwoD : List (Fin TwistTag.E6.tag.rank) := [0, 2, 3, 4, 5, 1, 3, 4, 2, 3, 0, 2, 1, 3, 4, 5, 2, 1, 3, 4, 3, 0, 2, 0]
theorem e6TwoA_comm : toMat TwistTag.E6.tag.rank twE6TwoMat * wordMat TwistTag.E6.tag e6TwoA =
    wordMat TwistTag.E6.tag e6TwoA * toMat TwistTag.E6.tag.rank twE6TwoMat :=
  tw_wordMat_comm_of_check _ _ (by decide +kernel)
theorem e6TwoB_comm : toMat TwistTag.E6.tag.rank twE6TwoMat * wordMat TwistTag.E6.tag e6TwoB =
    wordMat TwistTag.E6.tag e6TwoB * toMat TwistTag.E6.tag.rank twE6TwoMat :=
  tw_wordMat_comm_of_check _ _ (by decide +kernel)
theorem e6TwoC_comm : toMat TwistTag.E6.tag.rank twE6TwoMat * wordMat TwistTag.E6.tag e6TwoC =
    wordMat TwistTag.E6.tag e6TwoC * toMat TwistTag.E6.tag.rank twE6TwoMat :=
  tw_wordMat_comm_of_check _ _ (by decide +kernel)
theorem e6TwoD_comm : toMat TwistTag.E6.tag.rank twE6TwoMat * wordMat TwistTag.E6.tag e6TwoD =
    wordMat TwistTag.E6.tag e6TwoD * toMat TwistTag.E6.tag.rank twE6TwoMat :=
  tw_wordMat_comm_of_check _ _ (by decide +kernel)
@[expose] def e6TwoY1 : List (List ℤ) := [[0, 0, 0, 0, 0, 0], [0, 0, 0, 0, 0, 0], [0, 0, 0, 0, 0, 0], [0, 0, 0, 0, 0, 0], [0, 0, 0, 0, 0, 0], [0, 0, 0, 0, 0, 0]]
@[expose] def e6TwoY2 : List (List ℤ) := [[3, 2, -2, -1, 2, -2], [-3, 0, 3, 0, 0, 0], [3, -2, 2, -2, 1, 2], [0, -3, 3, 0, 0, 3], [0, -1, 1, -1, 2, 1], [3, 1, -1, -2, 1, 2]]
@[expose] def e6Twoc : ℤ := -3
theorem e6Two_cert : (toMat TwistTag.E6.tag.rank twE6TwoMat - ((-1 : ℤ)) • (1 : Matrix (Fin TwistTag.E6.tag.rank) (Fin TwistTag.E6.tag.rank) ℤ)) *
    toMat TwistTag.E6.tag.rank e6TwoY1 + (wordMat TwistTag.E6.tag (twCommWord (twCommWord e6TwoC e6TwoD)
      (twCommWord e6TwoA e6TwoB)) - 1) * toMat TwistTag.E6.tag.rank e6TwoY2 =
    e6Twoc • (1 : Matrix (Fin TwistTag.E6.tag.rank) (Fin TwistTag.E6.tag.rank) ℤ) :=
  tw_cert_of_check _ _ _ _ _ _ (by decide +kernel)
theorem e6Two_moves (D : LangDatum TwistTag.E6.tag L) {Fr : L →+* L} {q : ℕ} (hq : 2 ≤ q)
    (hFr : ∀ c, Fr c = c ^ q) (hΦ : D.Φ = twistHom TwistTag.E6 L Fr)
    (hn : D.n = canonicalRep (coxeterSystem TwistTag.E6.tag) L
      ((coxeterSystem TwistTag.E6.tag).wordProd twE6TwoWord)) {p : ℕ} [Fact p.Prime]
    (hp2 : p ≠ 2) (hp5 : 5 ≤ p) (he : orderOf (q : ZMod p) = 2) (S₀ : Sylow p D.Γ)
    (hS₀ : (S₀ : Subgroup D.Γ) ≤ D.torus.subgroupOf D.Γ) :
    NormalizerMovesLines p (S₀ : Subgroup D.Γ) :=
  tw_moves_of_dc_cert D hq hFr hΦ hn (M := toMat TwistTag.E6.tag.rank twE6TwoMat) (tw_E6_hv e6Two_hv)
    (N := 2) (by norm_num) twE6Two_pow S₀ hS₀ e6TwoA_comm e6TwoB_comm e6TwoC_comm
    e6TwoD_comm (e' := -1) (tw_dvd_add_of_orderOf_two Fact.out hp2 he)
    (Y₁ := toMat TwistTag.E6.tag.rank e6TwoY1) (Y₂ := toMat TwistTag.E6.tag.rank e6TwoY2) (c := e6Twoc) e6Two_cert
    (tw_not_dvd_three hp5 (by norm_num [e6Twoc]))

theorem e6Three_hv : ∀ x, ((coxeterSystem TwistTag.E6.tag).wordProd twE6ThreeWord) • x =
    toMat TwistTag.E6.tag.rank twE6ThreeMat *ᵥ permLattice TwistTag.E6.perm x := fun x => by
  rw [wordProd_smul_eq_wordMat_mulVec, twE6Three_wordMat, toMat_lmul, permLattice_E6_eq,
    Matrix.mulVec_mulVec]
@[expose] def e6ThreeA : List (Fin TwistTag.E6.tag.rank) := [4, 5, 1, 3, 4, 2, 3, 0, 2, 1, 3, 4, 5, 1, 3, 4, 2, 3, 0, 2, 1, 3, 4, 2, 3, 2]
@[expose] def e6ThreeB : List (Fin TwistTag.E6.tag.rank) := [5, 4, 2, 3, 0, 2, 1, 3, 4, 5, 3, 4, 2, 3, 0, 2, 1, 3, 4, 3, 0, 2, 1, 0]
@[expose] def e6ThreeC : List (Fin TwistTag.E6.tag.rank) := [4, 5, 3, 4, 2, 3, 0, 2, 1, 3, 4, 5, 2, 3, 4, 3, 0, 2, 1, 3, 0, 2, 1, 0]
@[expose] def e6ThreeD : List (Fin TwistTag.E6.tag.rank) := [2, 1, 3, 4, 5, 0, 2, 3, 4, 2, 1, 3]
theorem e6ThreeA_comm : toMat TwistTag.E6.tag.rank twE6ThreeMat * wordMat TwistTag.E6.tag e6ThreeA =
    wordMat TwistTag.E6.tag e6ThreeA * toMat TwistTag.E6.tag.rank twE6ThreeMat :=
  tw_wordMat_comm_of_check _ _ (by decide +kernel)
theorem e6ThreeB_comm : toMat TwistTag.E6.tag.rank twE6ThreeMat * wordMat TwistTag.E6.tag e6ThreeB =
    wordMat TwistTag.E6.tag e6ThreeB * toMat TwistTag.E6.tag.rank twE6ThreeMat :=
  tw_wordMat_comm_of_check _ _ (by decide +kernel)
theorem e6ThreeC_comm : toMat TwistTag.E6.tag.rank twE6ThreeMat * wordMat TwistTag.E6.tag e6ThreeC =
    wordMat TwistTag.E6.tag e6ThreeC * toMat TwistTag.E6.tag.rank twE6ThreeMat :=
  tw_wordMat_comm_of_check _ _ (by decide +kernel)
theorem e6ThreeD_comm : toMat TwistTag.E6.tag.rank twE6ThreeMat * wordMat TwistTag.E6.tag e6ThreeD =
    wordMat TwistTag.E6.tag e6ThreeD * toMat TwistTag.E6.tag.rank twE6ThreeMat :=
  tw_wordMat_comm_of_check _ _ (by decide +kernel)
theorem e6Three_mat : wordMat TwistTag.E6.tag
    (twCommWord (twCommWord e6ThreeC e6ThreeD) (twCommWord e6ThreeA e6ThreeB)) =
    (-1 : ℤ) • toMat TwistTag.E6.tag.rank twE6ThreeMat ^ 3 :=
  tw_wordMat_eq_smul_pow_of_check _ _ _ _ (by decide +kernel)
theorem e6Three_moves (D : LangDatum TwistTag.E6.tag L) {Fr : L →+* L} {q : ℕ} (hq : 2 ≤ q)
    (hFr : ∀ c, Fr c = c ^ q) (hΦ : D.Φ = twistHom TwistTag.E6 L Fr)
    (hn : D.n = canonicalRep (coxeterSystem TwistTag.E6.tag) L
      ((coxeterSystem TwistTag.E6.tag).wordProd twE6ThreeWord)) {p : ℕ} [Fact p.Prime]
    (hp2 : p ≠ 2) (he : orderOf (q : ZMod p) = 3) (S₀ : Sylow p D.Γ)
    (hS₀ : (S₀ : Subgroup D.Γ) ≤ D.torus.subgroupOf D.Γ) :
    NormalizerMovesLines p (S₀ : Subgroup D.Γ) :=
  tw_moves_of_dc_scalar D hq hFr hΦ hn (M := toMat TwistTag.E6.tag.rank twE6ThreeMat) (tw_E6_hv e6Three_hv)
    (N := 6) (by norm_num) twE6Three_pow S₀ hS₀ e6ThreeA_comm e6ThreeB_comm e6ThreeC_comm
    e6ThreeD_comm e6Three_mat (tw_not_dvd_sign_pow (s := -1) (k := 3) Fact.out hp2 he (Or.inl ⟨rfl, ⟨1, by norm_num⟩⟩))

theorem e6Four_hv : ∀ x, ((coxeterSystem TwistTag.E6.tag).wordProd twE6FourWord) • x =
    toMat TwistTag.E6.tag.rank twE6FourMat *ᵥ permLattice TwistTag.E6.perm x := fun x => by
  rw [wordProd_smul_eq_wordMat_mulVec, twE6Four_wordMat, toMat_lmul, permLattice_E6_eq,
    Matrix.mulVec_mulVec]
@[expose] def e6FourA : List (Fin TwistTag.E6.tag.rank) := [1, 3, 4, 2, 3, 1]
@[expose] def e6FourB : List (Fin TwistTag.E6.tag.rank) := [5, 4, 3, 2, 1, 3, 4, 5, 4, 2, 1, 3, 1]
@[expose] def e6FourC : List (Fin TwistTag.E6.tag.rank) := [0, 2, 3, 4, 5, 1, 3, 4, 2, 3, 0, 2, 1, 3, 4, 5, 4, 1, 3, 1]
@[expose] def e6FourD : List (Fin TwistTag.E6.tag.rank) := [0, 2, 3, 4, 5, 1, 3, 4, 2, 3, 0, 2, 1, 3, 4, 5, 1, 3, 4, 2, 1, 3]
theorem e6FourA_comm : toMat TwistTag.E6.tag.rank twE6FourMat * wordMat TwistTag.E6.tag e6FourA =
    wordMat TwistTag.E6.tag e6FourA * toMat TwistTag.E6.tag.rank twE6FourMat :=
  tw_wordMat_comm_of_check _ _ (by decide +kernel)
theorem e6FourB_comm : toMat TwistTag.E6.tag.rank twE6FourMat * wordMat TwistTag.E6.tag e6FourB =
    wordMat TwistTag.E6.tag e6FourB * toMat TwistTag.E6.tag.rank twE6FourMat :=
  tw_wordMat_comm_of_check _ _ (by decide +kernel)
theorem e6FourC_comm : toMat TwistTag.E6.tag.rank twE6FourMat * wordMat TwistTag.E6.tag e6FourC =
    wordMat TwistTag.E6.tag e6FourC * toMat TwistTag.E6.tag.rank twE6FourMat :=
  tw_wordMat_comm_of_check _ _ (by decide +kernel)
theorem e6FourD_comm : toMat TwistTag.E6.tag.rank twE6FourMat * wordMat TwistTag.E6.tag e6FourD =
    wordMat TwistTag.E6.tag e6FourD * toMat TwistTag.E6.tag.rank twE6FourMat :=
  tw_wordMat_comm_of_check _ _ (by decide +kernel)
theorem e6Four_mat : wordMat TwistTag.E6.tag
    (twCommWord (twCommWord e6FourC e6FourD) (twCommWord e6FourA e6FourB)) =
    (1 : ℤ) • toMat TwistTag.E6.tag.rank twE6FourMat ^ 2 :=
  tw_wordMat_eq_smul_pow_of_check _ _ _ _ (by decide +kernel)
theorem e6Four_moves (D : LangDatum TwistTag.E6.tag L) {Fr : L →+* L} {q : ℕ} (hq : 2 ≤ q)
    (hFr : ∀ c, Fr c = c ^ q) (hΦ : D.Φ = twistHom TwistTag.E6 L Fr)
    (hn : D.n = canonicalRep (coxeterSystem TwistTag.E6.tag) L
      ((coxeterSystem TwistTag.E6.tag).wordProd twE6FourWord)) {p : ℕ} [Fact p.Prime]
    (hp2 : p ≠ 2) (he : orderOf (q : ZMod p) = 4) (S₀ : Sylow p D.Γ)
    (hS₀ : (S₀ : Subgroup D.Γ) ≤ D.torus.subgroupOf D.Γ) :
    NormalizerMovesLines p (S₀ : Subgroup D.Γ) :=
  tw_moves_of_dc_scalar D hq hFr hΦ hn (M := toMat TwistTag.E6.tag.rank twE6FourMat) (tw_E6_hv e6Four_hv)
    (N := 4) (by norm_num) twE6Four_pow S₀ hS₀ e6FourA_comm e6FourB_comm e6FourC_comm
    e6FourD_comm e6Four_mat (tw_not_dvd_sign_pow (s := 1) (k := 2) Fact.out hp2 he (Or.inr ⟨rfl, by omega⟩))

theorem e6Six_hv : ∀ x, ((coxeterSystem TwistTag.E6.tag).wordProd twE6SixWord) • x =
    toMat TwistTag.E6.tag.rank twE6SixMat *ᵥ permLattice TwistTag.E6.perm x := fun x => by
  rw [wordProd_smul_eq_wordMat_mulVec, twE6Six_wordMat, toMat_lmul, permLattice_E6_eq,
    Matrix.mulVec_mulVec]
@[expose] def e6SixA : List (Fin TwistTag.E6.tag.rank) := [2, 3, 4, 5, 4, 2, 3, 0, 2, 1, 3, 4, 0, 2, 1, 3, 1, 0]
@[expose] def e6SixB : List (Fin TwistTag.E6.tag.rank) := [5, 1, 3, 4, 3, 2, 1, 3, 1, 0]
@[expose] def e6SixC : List (Fin TwistTag.E6.tag.rank) := [5, 4, 2, 3, 0, 2, 1, 3, 4, 5, 4, 3, 2, 1, 3, 4, 1, 3, 2, 0]
@[expose] def e6SixD : List (Fin TwistTag.E6.tag.rank) := [2, 1, 3, 4, 5, 2, 3, 4, 2, 1, 3, 0, 2, 0]
theorem e6SixA_comm : toMat TwistTag.E6.tag.rank twE6SixMat * wordMat TwistTag.E6.tag e6SixA =
    wordMat TwistTag.E6.tag e6SixA * toMat TwistTag.E6.tag.rank twE6SixMat :=
  tw_wordMat_comm_of_check _ _ (by decide +kernel)
theorem e6SixB_comm : toMat TwistTag.E6.tag.rank twE6SixMat * wordMat TwistTag.E6.tag e6SixB =
    wordMat TwistTag.E6.tag e6SixB * toMat TwistTag.E6.tag.rank twE6SixMat :=
  tw_wordMat_comm_of_check _ _ (by decide +kernel)
theorem e6SixC_comm : toMat TwistTag.E6.tag.rank twE6SixMat * wordMat TwistTag.E6.tag e6SixC =
    wordMat TwistTag.E6.tag e6SixC * toMat TwistTag.E6.tag.rank twE6SixMat :=
  tw_wordMat_comm_of_check _ _ (by decide +kernel)
theorem e6SixD_comm : toMat TwistTag.E6.tag.rank twE6SixMat * wordMat TwistTag.E6.tag e6SixD =
    wordMat TwistTag.E6.tag e6SixD * toMat TwistTag.E6.tag.rank twE6SixMat :=
  tw_wordMat_comm_of_check _ _ (by decide +kernel)
theorem e6Six_mat : wordMat TwistTag.E6.tag
    (twCommWord (twCommWord e6SixC e6SixD) (twCommWord e6SixA e6SixB)) =
    (1 : ℤ) • toMat TwistTag.E6.tag.rank twE6SixMat ^ 2 :=
  tw_wordMat_eq_smul_pow_of_check _ _ _ _ (by decide +kernel)
theorem e6Six_moves (D : LangDatum TwistTag.E6.tag L) {Fr : L →+* L} {q : ℕ} (hq : 2 ≤ q)
    (hFr : ∀ c, Fr c = c ^ q) (hΦ : D.Φ = twistHom TwistTag.E6 L Fr)
    (hn : D.n = canonicalRep (coxeterSystem TwistTag.E6.tag) L
      ((coxeterSystem TwistTag.E6.tag).wordProd twE6SixWord)) {p : ℕ} [Fact p.Prime]
    (hp2 : p ≠ 2) (he : orderOf (q : ZMod p) = 6) (S₀ : Sylow p D.Γ)
    (hS₀ : (S₀ : Subgroup D.Γ) ≤ D.torus.subgroupOf D.Γ) :
    NormalizerMovesLines p (S₀ : Subgroup D.Γ) :=
  tw_moves_of_dc_scalar D hq hFr hΦ hn (M := toMat TwistTag.E6.tag.rank twE6SixMat) (tw_E6_hv e6Six_hv)
    (N := 6) (by norm_num) twE6Six_pow S₀ hS₀ e6SixA_comm e6SixB_comm e6SixC_comm
    e6SixD_comm e6Six_mat (tw_not_dvd_sign_pow (s := 1) (k := 2) Fact.out hp2 he (Or.inr ⟨rfl, by omega⟩))

end Moves

end CFSG.LocalAnalysis.RankThreeTheoremC.KFactProofs.Stroth.WeakClosure.ExcCross
