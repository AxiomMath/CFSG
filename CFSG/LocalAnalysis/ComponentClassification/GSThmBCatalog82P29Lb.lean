module

public import CFSG.LocalAnalysis.ComponentClassification.CatFactsL4U4DiagLf
public import CFSG.LocalAnalysis.ComponentClassification.BlockTwoProductAction
public import CFSG.LocalAnalysis.ComponentClassification.CatFactsL4U4AZCore
public import CFSG.LocalAnalysis.ComponentClassification.CatalogueSchreierLinearTwo
public import CFSG.LocalAnalysis.ComponentClassification.CatalogueUStatement
public import CFSG.LocalAnalysis.ComponentClassification.GSThmB7Basic
public import CFSG.LocalAnalysis.ComponentClassification.GSThmBCatalog7L2
public import CFSG.LocalAnalysis.ComponentClassification.GSThmBCatalog82L2
public import CFSG.LocalAnalysis.ComponentClassification.NormalizedProductSylow
public import CFSG.LocalAnalysis.ComponentClassification.TwoActionFixedInvolution
public import CFSG.LocalAnalysis.ComponentClassification.TwoActionInvariantSylow
public import CFSG.LocalAnalysis.ComponentClassification.UnbalancedCorrCentralSylowMaximality
public import CFSG.LocalAnalysis.ComponentClassification.UnbalancedGSAContainedSource
public import CFSG.LocalAnalysis.ComponentClassification.UnbalancedLayerOddCoreUnbalancingTriple
public import CFSG.LocalAnalysis.ComponentInitial.LinearInvolutionFixedField
public import CFSG.LocalAnalysis.ProperTwoGeneratedCore.CentralInvolutionStructure
public import CFSG.LocalAnalysis.SectionRank.CentralLift
public import CFSG.LocalAnalysis.ZStar.BrauerSylowFusion
public import CFSG.LocalAnalysis.ZStar.PrincipalBlockTraceApplication
public import CFSG.Open.QuasithinDefs
public import CFSG.Permutation.AlternatingAutomorphism
public import CFSG.Sporadic.Th.F2Spec
public import CFSG.ThirdParty.QiuzhenCFSG.BenderSuzuki.External.Huppert.IV.theorem_3_3
public import CFSG.ThirdParty.QiuzhenCFSG.BenderSuzuki.PFchapter1section3.Basic
public import CFSG.ThirdParty.QiuzhenCFSG.BenderSuzuki.PFchapter2.Basic

public section

namespace CFSG.ComponentClassification.GSThmB.P29

open Matrix CFSG.ComponentClassification.CatFactsL4U4 DiagL

namespace L4M

variable {F : Type} [Field F]

local macro "entry_close" h:ident a:ident b:ident : tactic => `(tactic|
  first
  | ring1
  | linear_combination ($h)
  | linear_combination (-$h)
  | linear_combination ($a) * $h
  | linear_combination (-$a) * $h
  | linear_combination ($b) * $h
  | linear_combination (-$b) * $h)

@[expose] def zM (x y : F) : Matrix (Fin 2) (Fin 2) F := !![x, -y; y, x]

@[expose] def kap : Matrix (Fin 2) (Fin 2) F := !![0, -1; 1, 0]

@[expose] def sM (x y : F) : Matrix (Fin 2) (Fin 2) F := !![x, -y; -y, -x]

local macro "blk_close" : tactic => `(tactic|
  (ext i j
   fin_cases i <;> fin_cases j <;>
     simp [zM, sM, kap, Matrix.mul_apply, Fin.sum_univ_two] <;> ring1))

local macro "blk_close'" h:ident a:ident b:ident : tactic => `(tactic|
  (ext i j
   fin_cases i <;> fin_cases j <;>
     simp [zM, sM, kap, Matrix.mul_apply, Fin.sum_univ_two] <;> entry_close $h $a $b))

theorem zM_mul_zM (a b c d : F) : zM a b * zM c d = zM (a * c - b * d) (a * d + b * c) := by
  blk_close

theorem zM_one_zero : zM (1 : F) 0 = 1 := by
  ext i j
  fin_cases i <;> fin_cases j <;> simp [zM]

theorem zM_zero_one : zM (0 : F) 1 = kap := by
  ext i j
  fin_cases i <;> fin_cases j <;> simp [zM, kap]

theorem zM_zero_neg_one : zM (0 : F) (-1) = -kap := by
  ext i j
  fin_cases i <;> fin_cases j <;> simp [zM, kap]

theorem kap_mul_kap : (kap : Matrix (Fin 2) (Fin 2) F) * kap = -1 := by
  ext i j
  fin_cases i <;> fin_cases j <;> simp [kap, Matrix.mul_apply, Fin.sum_univ_two]

theorem zM_comm (a b c d : F) : zM a b * zM c d = zM c d * zM a b := by
  rw [zM_mul_zM, zM_mul_zM]
  congr 1 <;> ring

variable {x y : F}

theorem zM_neg_mul_zM (hxy : x ^ 2 + y ^ 2 = -1) : zM (-x) y * zM x y = 1 := by
  rw [zM_mul_zM, ← zM_one_zero]
  congr 1
  · linear_combination -hxy
  · ring

theorem det_zM (a b : F) : (zM a b).det = a ^ 2 + b ^ 2 := by
  rw [Matrix.det_fin_two]
  simp [zM]
  ring

@[expose] def bd (P Q : Matrix (Fin 2) (Fin 2) F) : Matrix (Fin 4) (Fin 4) F :=
  !![P 0 0, P 0 1, 0, 0; P 1 0, P 1 1, 0, 0; 0, 0, Q 0 0, Q 0 1; 0, 0, Q 1 0, Q 1 1]

@[expose] def ad (P Q : Matrix (Fin 2) (Fin 2) F) : Matrix (Fin 4) (Fin 4) F :=
  !![0, 0, P 0 0, P 0 1; 0, 0, P 1 0, P 1 1; Q 0 0, Q 0 1, 0, 0; Q 1 0, Q 1 1, 0, 0]

theorem bd_mul_bd (P Q P' Q' : Matrix (Fin 2) (Fin 2) F) :
    bd P Q * bd P' Q' = bd (P * P') (Q * Q') := by
  ext i j
  fin_cases i <;> fin_cases j <;> simp [bd, Matrix.mul_apply, Fin.sum_univ_four, Fin.sum_univ_two]

theorem bd_mul_ad (P Q P' Q' : Matrix (Fin 2) (Fin 2) F) :
    bd P Q * ad P' Q' = ad (P * P') (Q * Q') := by
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [bd, ad, Matrix.mul_apply, Fin.sum_univ_four, Fin.sum_univ_two]

theorem ad_mul_bd (P Q P' Q' : Matrix (Fin 2) (Fin 2) F) :
    ad P Q * bd P' Q' = ad (P * Q') (Q * P') := by
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [bd, ad, Matrix.mul_apply, Fin.sum_univ_four, Fin.sum_univ_two]

theorem ad_mul_ad (P Q P' Q' : Matrix (Fin 2) (Fin 2) F) :
    ad P Q * ad P' Q' = bd (P * Q') (Q * P') := by
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [bd, ad, Matrix.mul_apply, Fin.sum_univ_four, Fin.sum_univ_two]

theorem bd_one : bd (1 : Matrix (Fin 2) (Fin 2) F) 1 = 1 := by
  ext i j
  fin_cases i <;> fin_cases j <;> simp [bd]

theorem bd_neg (P Q : Matrix (Fin 2) (Fin 2) F) : bd (-P) (-Q) = -bd P Q := by
  ext i j
  fin_cases i <;> fin_cases j <;> simp [bd]

theorem ad_neg (P Q : Matrix (Fin 2) (Fin 2) F) : ad (-P) (-Q) = -ad P Q := by
  ext i j
  fin_cases i <;> fin_cases j <;> simp [ad]

theorem bd_pow (P Q : Matrix (Fin 2) (Fin 2) F) (j : ℕ) : bd P Q ^ j = bd (P ^ j) (Q ^ j) := by
  induction j with
  | zero => rw [pow_zero, pow_zero, pow_zero, bd_one]
  | succ j ih => rw [pow_succ, ih, bd_mul_bd, ← pow_succ, ← pow_succ]

theorem det_bd (P Q : Matrix (Fin 2) (Fin 2) F) : (bd P Q).det = P.det * Q.det := by
  rw [Matrix.det_fin_two, Matrix.det_fin_two, bd, Matrix.det_succ_row_zero]
  simp [Fin.sum_univ_succ, Matrix.det_succ_row_zero, Matrix.submatrix, Fin.succAbove]
  ring

theorem ad_apply_zero_zero (P Q : Matrix (Fin 2) (Fin 2) F) : ad P Q 0 0 = 0 := by simp [ad]

theorem bd_apply_zero_zero (P Q : Matrix (Fin 2) (Fin 2) F) : bd P Q 0 0 = P 0 0 := by simp [bd]

theorem wK_eq_ad : (wK : Matrix (Fin 4) (Fin 4) F) = ad 1 (-1) := by
  ext i j
  fin_cases i <;> fin_cases j <;> simp [wK, ad]

theorem kZero_eq_bd : kZero (-1 : F) = bd kap kap := by
  ext i j
  fin_cases i <;> fin_cases j <;> simp [kZero, bd, kap]

theorem eK_eq_bd (a b : F) : eK (-1 : F) a b = bd (zM a b) (zM a b) := by
  ext i j
  fin_cases i <;> fin_cases j <;> simp [eK, bd, zM]

variable (x y) in
@[expose] def aM : Matrix (Fin 4) (Fin 4) F := bd (zM x y) (zM (-x) y)

variable (x y) in
@[expose] def tM : Matrix (Fin 4) (Fin 4) F := bd 1 (sM x y)

variable (x y) in
@[expose] def tiM : Matrix (Fin 4) (Fin 4) F := bd 1 (-sM x y)

variable (x y) in
@[expose] def apM : Matrix (Fin 4) (Fin 4) F := bd (zM x y) (-zM x y)

variable (x y) in
@[expose] def wpM : Matrix (Fin 4) (Fin 4) F := ad (sM x y) (sM x y)

@[expose] def kpM : Matrix (Fin 4) (Fin 4) F := bd kap (-kap)

theorem det_aM (hxy : x ^ 2 + y ^ 2 = -1) : (aM x y).det = 1 := by
  rw [aM, det_bd, det_zM, det_zM]
  linear_combination (x ^ 2 + y ^ 2 - 1) * hxy

theorem det_tM (hxy : x ^ 2 + y ^ 2 = -1) : (tM x y).det = 1 := by
  rw [tM, det_bd, Matrix.det_one, one_mul, Matrix.det_fin_two]
  simp [sM]
  entry_close hxy x y

theorem det_kpM : (kpM : Matrix (Fin 4) (Fin 4) F).det = 1 := by
  rw [kpM, det_bd, Matrix.det_fin_two, Matrix.det_fin_two]
  simp [kap]

theorem tM_mul_tiM (hxy : x ^ 2 + y ^ 2 = -1) : tM x y * tiM x y = 1 := by
  rw [tM, tiM, bd_mul_bd, ← bd_one]
  congr 1 <;> blk_close' hxy x y

theorem tiM_aM_tM (hxy : x ^ 2 + y ^ 2 = -1) : tiM x y * aM x y * tM x y = apM x y := by
  rw [tiM, aM, tM, apM, bd_mul_bd, bd_mul_bd]
  congr 1 <;> blk_close' hxy x y

theorem tiM_wK_tM : tiM x y * wK * tM x y = wpM x y := by
  rw [tiM, wK_eq_ad, tM, wpM, bd_mul_ad, ad_mul_bd]
  congr 1 <;> blk_close

theorem apM_aM : apM x y * aM x y = aM x y * apM x y := by
  rw [apM, aM, bd_mul_bd, bd_mul_bd]
  congr 1
  blk_close

theorem aM_wpM : aM x y * wpM x y = -(wpM x y * aM x y) := by
  rw [aM, wpM, bd_mul_ad, ad_mul_bd, ← ad_neg]
  congr 1 <;> blk_close

theorem wK_apM : wK * apM x y = -(apM x y * wK) := by
  rw [wK_eq_ad, apM, ad_mul_bd, bd_mul_ad, ← ad_neg]
  congr 1 <;> blk_close

theorem wK_wpM : wK * wpM x y = -(wpM x y * wK) := by
  rw [wK_eq_ad, wpM, ad_mul_ad, ad_mul_ad, ← bd_neg]
  congr 1 <;> blk_close

theorem wK_aM_wK_aM (hxy : x ^ 2 + y ^ 2 = -1) : wK * aM x y * wK * aM x y = -1 := by
  rw [wK_eq_ad, aM, ad_mul_bd, ad_mul_ad, bd_mul_bd, ← bd_one, ← bd_neg]
  congr 1 <;> blk_close' hxy x y

theorem tiM_kpM_tM (hxy : x ^ 2 + y ^ 2 = -1) : tiM x y * kpM * tM x y = kZero (-1) := by
  rw [tiM, kpM, tM, bd_mul_bd, bd_mul_bd, kZero_eq_bd]
  congr 1 <;> blk_close' hxy x y

theorem tM_mul_tM (hxy : x ^ 2 + y ^ 2 = -1) : tM x y * tM x y = -(kZero (-1) * kpM) := by
  rw [tM, kZero_eq_bd, kpM, bd_mul_bd, bd_mul_bd, ← bd_neg]
  congr 1 <;> blk_close' hxy x y

theorem kpM_apM : kpM * apM x y = eK (-1 : F) (-y) x := by
  rw [kpM, apM, bd_mul_bd, eK_eq_bd]
  congr 1 <;> blk_close

theorem kZero_wpM : kZero (-1) * wpM x y = -(wpM x y * kZero (-1)) := by
  rw [kZero_eq_bd, wpM, bd_mul_ad, ad_mul_bd, ← ad_neg]
  congr 1 <;> blk_close

theorem kZero_kpM_sq : kZero (-1 : F) * kpM * (kZero (-1) * kpM) = 1 := by
  rw [kZero_eq_bd, kpM, bd_mul_bd, bd_mul_bd, ← bd_one]
  congr 1 <;> blk_close

theorem kpM_mul_kpM : (kpM : Matrix (Fin 4) (Fin 4) F) * kpM = -1 := by
  rw [kpM, bd_mul_bd, ← bd_one, ← bd_neg]
  congr 1 <;> blk_close

theorem kpM_apply_zero_zero : (kpM : Matrix (Fin 4) (Fin 4) F) 0 0 = 0 := by
  rw [kpM, bd_apply_zero_zero]
  simp [kap]

theorem wK_mul_bd_apply (P Q : Matrix (Fin 2) (Fin 2) F) :
    (wK * bd P Q : Matrix (Fin 4) (Fin 4) F) 0 0 = 0 := by
  rw [wK_eq_ad, ad_mul_bd, ad_apply_zero_zero]

theorem aM_wK (hxy : x ^ 2 + y ^ 2 = -1) :
    aM x y * wK = uK (-1) x y * lK (-1) x (-y) * uK (-1) x y := by
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [aM, bd, zM, wK, uK, lK, Matrix.mul_apply, Fin.sum_univ_four] <;> entry_close hxy x y

theorem wpM_kZero_apply (x y : F) :
    (wpM x y * kZero (-1) : Matrix (Fin 4) (Fin 4) F) 0 2 = -y ∧
      (wpM x y * kZero (-1) : Matrix (Fin 4) (Fin 4) F) 0 3 = -x := by
  constructor <;> simp [wpM, ad, sM, kZero, Matrix.mul_apply, Fin.sum_univ_four]

end L4M

end CFSG.ComponentClassification.GSThmB.P29
