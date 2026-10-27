module

public import CFSG.LocalAnalysis.EvenSmallLie.OmegaEight.SpBranchSModelCheck
public import CFSG.LocalAnalysis.EvenSmallLie.OmegaEight.SpBranchCode
public import CFSG.LocalAnalysis.EvenSmallLie.OmegaEight.Stage1Data
public import Mathlib.Algebra.Group.MinimalAxioms
public import Mathlib.Algebra.Order.Ring.Star

public section

namespace CFSG.EvenSmallLie.OmegaEight.SpBranch

open CFSG.EvenSmallLie.OmegaEight.Stage1

attribute [local irreducible] sAct sMt sGinv p9List p9Index

section Codes


theorem sAct_size : sAct.size = 65536 := by
  have h := sRange_check
  simp only [sRangeCheck, Bool.and_eq_true, beq_iff_eq] at h
  exact h.1.1.1.1

theorem sMt_size : sMt.size = 262144 := by
  have h := sRange_check
  simp only [sRangeCheck, Bool.and_eq_true, beq_iff_eq] at h
  exact h.1.1.1.2

theorem sA_lt {g e : ℕ} (hg : g < 512) (he : e < 128) : sA g e < 128 := by
  have h := sRange_check
  simp only [sRangeCheck, Bool.and_eq_true, beq_iff_eq] at h
  have hidx : g * 128 + e < sAct.size := by rw [sAct_size]; omega
  have := (Array.all_eq_true.1 h.1.1.2) _ hidx
  rw [sA, getElem!_pos sAct _ hidx]
  simpa using this

theorem sM_lt {g h : ℕ} (hg : g < 512) (hh : h < 512) : sM g h < 512 := by
  have h' := sRange_check
  simp only [sRangeCheck, Bool.and_eq_true, beq_iff_eq] at h'
  have hidx : g * 512 + h < sMt.size := by rw [sMt_size]; omega
  have := (Array.all_eq_true.1 h'.1.2) _ hidx
  rw [sM, getElem!_pos sMt _ hidx]
  simpa using this

theorem sGinv_lt {g : ℕ} (hg : g < 512) : sGinv[g]! < 512 := by
  have h := sRange_check
  simp only [sRangeCheck, Bool.and_eq_true, beq_iff_eq, List.all_eq_true, List.mem_range,
    decide_eq_true_eq] at h
  exact h.2 g hg

theorem sM_assoc {i j k : ℕ} (hi : i < 512) (hj : j < 512) (hk : k < 512) :
    sM (sM i j) k = sM i (sM j k) := by
  have h := sAssoc_check
  simp only [sAssocCheck, List.all_eq_true, List.mem_range, beq_iff_eq] at h
  exact h i hi j hj k hk

theorem sM_unit {j : ℕ} (hj : j < 512) : sM 0 j = j ∧ sM j 0 = j ∧ sM (sGinv[j]!) j = 0 := by
  have h := sUnit_check
  simp only [sUnitCheck, List.all_eq_true, List.mem_range, Bool.and_eq_true, beq_iff_eq] at h
  exact ⟨(h j hj).1.1, (h j hj).1.2, (h j hj).2⟩

theorem sA_add {g e e' : ℕ} (hg : g < 512) (he : e < 128) (he' : e' < 128) :
    sA g (e ^^^ e') = sA g e ^^^ sA g e' := by
  have h := sAct_check
  simp only [sActCheck, List.all_eq_true, List.mem_range, Bool.and_eq_true, beq_iff_eq] at h
  exact h.1.1 g hg e he e' he'

theorem sA_mul {g h e : ℕ} (hg : g < 512) (hh : h < 512) (he : e < 128) :
    sA (sM g h) e = sA g (sA h e) := by
  have h' := sAct_check
  simp only [sActCheck, List.all_eq_true, List.mem_range, Bool.and_eq_true, beq_iff_eq] at h'
  exact h'.1.2 g hg h hh e he

theorem sA_zero {e : ℕ} (he : e < 128) : sA 0 e = e := by
  have h := sAct_check
  simp only [sActCheck, List.all_eq_true, List.mem_range, Bool.and_eq_true, beq_iff_eq] at h
  exact h.2 e he

@[expose] def eP (c : ℕ) : ℕ := c % 128

@[expose] def gP (c : ℕ) : ℕ := c / 128 % 512

theorem eP_lt (c : ℕ) : eP c < 128 := Nat.mod_lt _ (by norm_num)

theorem gP_lt (c : ℕ) : gP c < 512 := Nat.mod_lt _ (by norm_num)

theorem eq_of_parts {c : ℕ} (hc : c < 65536) : c = eP c + 128 * gP c := by
  unfold eP gP
  have : c / 128 < 512 := by omega
  rw [Nat.mod_eq_of_lt this]
  omega

theorem sMul_eq (c d : ℕ) : sMul c d = (eP c ^^^ sA (gP c) (eP d)) + 128 * sM (gP c) (gP d) := rfl

theorem xor_lt128 {a b : ℕ} (ha : a < 128) (hb : b < 128) : a ^^^ b < 128 :=
  Nat.xor_lt_two_pow (n := 7) ha hb

theorem eP_sMul (c d : ℕ) : eP (sMul c d) = eP c ^^^ sA (gP c) (eP d) := by
  rw [sMul_eq, eP, Nat.add_mul_mod_self_left]
  exact Nat.mod_eq_of_lt (xor_lt128 (eP_lt c) (sA_lt (gP_lt c) (eP_lt d)))

theorem gP_sMul (c d : ℕ) : gP (sMul c d) = sM (gP c) (gP d) := by
  rw [sMul_eq, gP]
  have h1 := xor_lt128 (eP_lt c) (sA_lt (gP_lt c) (eP_lt d))
  have h2 := sM_lt (gP_lt c) (gP_lt d)
  rw [Nat.add_mul_div_left _ _ (by norm_num : 0 < 128), Nat.div_eq_of_lt h1, zero_add,
    Nat.mod_eq_of_lt h2]

theorem sMul_lt (c d : ℕ) : sMul c d < 65536 := by
  rw [sMul_eq]
  have h1 := xor_lt128 (eP_lt c) (sA_lt (gP_lt c) (eP_lt d))
  have h2 := sM_lt (gP_lt c) (gP_lt d)
  omega

theorem ext_parts {c d : ℕ} (hc : c < 65536) (hd : d < 65536) (he : eP c = eP d)
    (hg : gP c = gP d) : c = d := by
  rw [eq_of_parts hc, eq_of_parts hd, he, hg]

theorem sMul_assoc (a b c : ℕ) : sMul (sMul a b) c = sMul a (sMul b c) := by
  refine ext_parts (sMul_lt _ _) (sMul_lt _ _) ?_ ?_
  · rw [eP_sMul, eP_sMul, eP_sMul, eP_sMul, gP_sMul, sA_add (gP_lt a) (eP_lt b)
      (sA_lt (gP_lt b) (eP_lt c)), sA_mul (gP_lt a) (gP_lt b) (eP_lt c), Nat.xor_assoc]
  · rw [gP_sMul, gP_sMul, gP_sMul, gP_sMul, sM_assoc (gP_lt a) (gP_lt b) (gP_lt c)]

theorem sMul_zero_left {c : ℕ} (hc : c < 65536) : sMul 0 c = c := by
  refine ext_parts (sMul_lt _ _) hc ?_ ?_
  · rw [eP_sMul, show eP 0 = 0 from rfl, show gP 0 = 0 from rfl, Nat.zero_xor, sA_zero (eP_lt c)]
  · rw [gP_sMul, show gP 0 = 0 from rfl, (sM_unit (gP_lt c)).1]

theorem sInv_eq (c : ℕ) : sInv c = sA (sGinv[gP c]!) (eP c) + 128 * sGinv[gP c]! := rfl

theorem eP_sInv (c : ℕ) : eP (sInv c) = sA (sGinv[gP c]!) (eP c) := by
  rw [sInv_eq, eP, Nat.add_mul_mod_self_left]
  exact Nat.mod_eq_of_lt (sA_lt (sGinv_lt (gP_lt c)) (eP_lt c))

theorem gP_sInv (c : ℕ) : gP (sInv c) = sGinv[gP c]! := by
  rw [sInv_eq, gP, Nat.add_mul_div_left _ _ (by norm_num : 0 < 128),
    Nat.div_eq_of_lt (sA_lt (sGinv_lt (gP_lt c)) (eP_lt c)), zero_add,
    Nat.mod_eq_of_lt (sGinv_lt (gP_lt c))]

theorem sInv_lt (c : ℕ) : sInv c < 65536 := by
  rw [sInv_eq]
  have h1 := sA_lt (sGinv_lt (gP_lt c)) (eP_lt c)
  have h2 := sGinv_lt (gP_lt c)
  omega

theorem sMul_inv_left (c : ℕ) : sMul (sInv c) c = 0 := by
  refine ext_parts (sMul_lt _ _) (by norm_num) ?_ ?_
  · rw [eP_sMul, eP_sInv, gP_sInv, Nat.xor_self]; rfl
  · rw [gP_sMul, gP_sInv, (sM_unit (gP_lt c)).2.2]; rfl

end Codes

structure SModel where
  code : ℕ
  lt : code < 65536

namespace SModel

@[ext] theorem ext {x y : SModel} (h : x.code = y.code) : x = y := by
  cases x; cases y; cases h; rfl

instance : Mul SModel := ⟨fun x y => ⟨sMul x.code y.code % 65536, Nat.mod_lt _ (by norm_num)⟩⟩

instance : One SModel := ⟨⟨0, by norm_num⟩⟩

instance : Inv SModel := ⟨fun x => ⟨sInv x.code % 65536, Nat.mod_lt _ (by norm_num)⟩⟩


theorem code_mul (x y : SModel) : (x * y).code = sMul x.code y.code :=
  Nat.mod_eq_of_lt (sMul_lt _ _)

theorem code_inv (x : SModel) : x⁻¹.code = sInv x.code := Nat.mod_eq_of_lt (sInv_lt _)

theorem code_one : (1 : SModel).code = 0 := rfl

instance instGroup : Group SModel :=
  Group.ofLeftAxioms (fun a b c => ext (by rw [code_mul, code_mul, code_mul, code_mul, sMul_assoc]))
    (fun a => ext (by rw [code_mul, code_one, sMul_zero_left a.lt]))
    (fun a => ext (by rw [code_mul, code_inv, code_one, sMul_inv_left]))

@[expose] def codeIso : CodeIso SModel 65536 sMul where
  f := code
  lt := lt
  inj _ _ h := ext h
  surj c hc := ⟨⟨c, hc⟩, rfl⟩
  map_mul := code_mul

theorem codeIso_f (x : SModel) : codeIso.f x = x.code := rfl

@[expose] def tM : Eps → SModel
  | .plus => ⟨64, by norm_num⟩
  | .minus => ⟨75, by norm_num⟩

@[expose] def EM : Set SModel := {x | x.code < 128}

theorem code_lt_128_iff (x : SModel) : x.code < 128 ↔ gP x.code = 0 := by
  have h := eq_of_parts x.lt
  constructor
  · intro hx
    unfold gP
    rw [Nat.div_eq_of_lt hx]
  · intro hg
    rw [h, hg]
    have := eP_lt x.code
    omega

theorem conj_mem_EM (g : SModel) {x : SModel} (hx : x ∈ EM) : g * x * g⁻¹ ∈ EM := by
  change (g * x * g⁻¹).code < 128
  rw [code_lt_128_iff]
  have hx' : gP x.code = 0 := (code_lt_128_iff x).1 hx
  have hinv : sM (gP g.code) (gP g⁻¹.code) = 0 := by
    have h1 : (g * g⁻¹).code = 0 := by rw [mul_inv_cancel]; rfl
    rw [code_mul] at h1
    have := congrArg gP h1
    rwa [gP_sMul] at this
  rw [code_mul, code_mul, gP_sMul, gP_sMul, hx', (sM_unit (gP_lt _)).2.1, hinv]

end SModel

end CFSG.EvenSmallLie.OmegaEight.SpBranch
