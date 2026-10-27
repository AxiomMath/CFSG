module

public import CFSG.LocalAnalysis.ComponentClassification.CatFactsL4U4P1LAction
public import Certificates.Data.CatFactsL4U4P1L43Data
public import CFSG.Sporadic.SmallOddCore.CentSpec
public import CFSG.LocalAnalysis.ComponentInitial.LinearFlagOrder
public import CFSG.RankThree.PartOne.KC.LinearSubfieldInclusion

public section

namespace CFSG.ComponentClassification.HarrisLit.P1.L43

open Matrix Subgroup CFSG.Certificates CFSG.Certificates.Native CFSG.Monster.B.Co2
  CFSG.Monster.B.Co2.Native CFSG.Sporadic.SmallOddCore CFSG.Sporadic.SmallOddCore.Native
  CFSG.Sporadic.Th.Native CFSG.LocalAnalysis.ComponentInitial.LinearFlag

theorem mulVec_eq_mv4 (A : Matrix (Fin 4) (Fin 4) (ZMod 3)) (v : V) : A *ᵥ v = mv4 A v := by
  funext i
  simp [mulVec, dotProduct, Fin.sum_univ_four, mv4]

theorem size_ptTab (A : Matrix (Fin 4) (Fin 4) (ZMod 3)) : (ptTab A).size = 40 := by
  simp [ptTab]

theorem ptTab_getElem! (A : Matrix (Fin 4) (Fin 4) (ZMod 3)) {i : ℕ} (hi : i < 40) :
    (ptTab A)[i]! = ptIndex (Matrix.mulVec A (decode i)) := by
  rw [ptTab, getElem!_ofFn_nat _ hi, mulVec_eq_mv4]

theorem tabA80_getElem!_lt {A A' : Matrix (Fin 4) (Fin 4) (ZMod 3)}
    (hd : invTab40 (ptTab Aᵀ) = ptTab A') {i : ℕ} (hi : i < 40) :
    (tabA80 A)[i]! = ptIndex (Matrix.mulVec A (decode i)) := by
  rw [tabA80, hd, getElem!_pos _ i (by simp [size_ptTab]; omega),
    Array.getElem_append_left (by rw [size_ptTab]; exact hi), ← getElem!_pos _ i
    (by rw [size_ptTab]; exact hi), ptTab_getElem! A hi]

theorem tabA80_getElem!_ge {A A' : Matrix (Fin 4) (Fin 4) (ZMod 3)}
    (hd : invTab40 (ptTab Aᵀ) = ptTab A') {i : ℕ} (hi : 40 ≤ i) (hi' : i < 80) :
    (tabA80 A)[i]! = 40 + ptIndex (Matrix.mulVec A' (decode (i - 40))) := by
  rw [tabA80, hd, getElem!_pos _ i (by simp [size_ptTab]; omega),
    Array.getElem_append_right (by rw [size_ptTab]; exact hi)]
  simp only [Array.getElem_map, size_ptTab]
  rw [← getElem!_pos _ (i - 40) (by rw [size_ptTab]; omega), ptTab_getElem! A' (by omega),
    add_comm]

theorem inverseTranspose_eq {A : GL (Fin 4) (ZMod 3)} {B : Matrix (Fin 4) (Fin 4) (ZMod 3)}
    (h : (A : Matrix (Fin 4) (Fin 4) (ZMod 3)) * Bᵀ = 1) :
    ((Matrix.GeneralLinearGroup.inverseTranspose A : GL (Fin 4) (ZMod 3)) :
      Matrix (Fin 4) (Fin 4) (ZMod 3)) = B := by
  rw [Matrix.GeneralLinearGroup.coe_inverseTranspose]
  have h1 : ((A⁻¹ : GL (Fin 4) (ZMod 3)) : Matrix (Fin 4) (Fin 4) (ZMod 3)) = Bᵀ := by
    calc ((A⁻¹ : GL (Fin 4) (ZMod 3)) : Matrix (Fin 4) (Fin 4) (ZMod 3)) =
        ((A⁻¹ : GL (Fin 4) (ZMod 3)) : Matrix (Fin 4) (Fin 4) (ZMod 3)) *
          ((A : Matrix (Fin 4) (Fin 4) (ZMod 3)) * Bᵀ) := by rw [h, Matrix.mul_one]
      _ = Bᵀ := by rw [← Matrix.mul_assoc, ← Units.val_mul, inv_mul_cancel, Units.val_one,
          Matrix.one_mul]
  rw [h1, Matrix.transpose_transpose]

theorem rep_tab80 {A : GL (Fin 4) (ZMod 3)} {k k' : ℕ}
    (hA : (A : Matrix (Fin 4) (Fin 4) (ZMod 3)) = matN k)
    (hA' : (A : Matrix (Fin 4) (Fin 4) (ZMod 3)) * (matN k')ᵀ = 1)
    (hd : invTab40 (ptTab (matN k)ᵀ) = ptTab (matN k')) :
    CFSG.Monster.B.Co2.Rep 80 (tab80 k false) (perm80 A) := by
  intro x
  rw [tab80]
  simp only [Bool.false_eq_true, ite_false]
  by_cases hx : x.val < 40
  · rw [tabA80_getElem!_lt hd hx, perm80_apply_lt A x hx, hA]
  · rw [tabA80_getElem!_ge hd (by omega) x.2, perm80_apply_ge A x (by omega),
      inverseTranspose_eq hA']

theorem rep_tab80_swap {A : GL (Fin 4) (ZMod 3)} {k k' : ℕ}
    (hA : (A : Matrix (Fin 4) (Fin 4) (ZMod 3)) = matN k)
    (hA' : (A : Matrix (Fin 4) (Fin 4) (ZMod 3)) * (matN k')ᵀ = 1)
    (hd : invTab40 (ptTab (matN k)ᵀ) = ptTab (matN k')) :
    CFSG.Monster.B.Co2.Rep 80 (tab80 k true) (perm80 A * swap80) := by
  intro x
  have h1 := rep_tab80 hA hA' hd (swap80 x)
  rw [tab80] at h1
  simp only [Bool.false_eq_true, ite_false] at h1
  rw [tab80]
  simp only [ite_true]
  rw [getElem!_ofFn_nat _ x.2, Equiv.Perm.mul_apply, ← h1]
  congr 1
  rw [swapTab, getElem!_ofFn_nat _ x.2]
  by_cases hx : x.val < 40
  · rw [swap80_apply_lt x hx]
    simp only [hx, ite_true]
  · rw [swap80_apply_ge x (by omega)]
    simp only [hx, ite_false]

theorem rep_tbl {a : Array ℕ} {g : Equiv.Perm (Fin 80)} (h : CFSG.Monster.B.Co2.Rep 80 a g) :
    CFSG.Sporadic.Th.Rep 80 (tbl a) g := by
  rw [← co2Rep_natArr_iff]
  intro x
  rw [← h x]
  unfold natArr tbl
  by_cases hs : x.val < a.size
  · rw [getElem!_pos _ x.val (by simpa using hs), Array.getElem_map, Array.getElem_map,
      UInt32.toNat_ofNat', ← getElem!_pos a x.val hs, Nat.mod_eq_of_lt]
    rw [h x]
    exact (g x).2.trans (by norm_num)
  · rw [getElem!_neg _ x.val (by simpa using hs), getElem!_neg a x.val hs]

theorem tp_tbl {a : Array ℕ} {g : Equiv.Perm (Fin 80)} (h : CFSG.Monster.B.Co2.Rep 80 a g) :
    tp 80 (tbl a) = g := by
  have ht : CFSG.Monster.B.Co2.Rep 80 (natArr (tbl a)) g := co2Rep_natArr_iff.mpr (rep_tbl h)
  have hc : (∀ i < 80, (natArr (tbl a))[i]! < 80) ∧ ∀ i < 80, ∀ j < 80,
      (natArr (tbl a))[i]! = (natArr (tbl a))[j]! → i = j := by
    refine ⟨fun i hi => ht.lt hi, fun i hi j hj hij => ?_⟩
    rw [ht.apply hi, ht.apply hj] at hij
    exact congrArg Fin.val (g.injective (Fin.ext hij))
  refine Equiv.ext fun x => Fin.ext ?_
  rw [tp, permOfArr, dite_eq_left hc]
  exact ht x

theorem det_matA : (matN codeA).det = 1 := by decide +kernel

theorem det_matB : (matN codeB).det = 1 := by decide +kernel

theorem matA_invT : matN codeA * (matN codeAi)ᵀ = 1 := by decide +kernel

theorem matB_invT : matN codeB * (matN codeBi)ᵀ = 1 := by decide +kernel

theorem invTab_A : invTab40 (ptTab (matN codeA)ᵀ) = ptTab (matN codeAi) := by decide +kernel

theorem invTab_B : invTab40 (ptTab (matN codeB)ᵀ) = ptTab (matN codeBi) := by decide +kernel

@[expose] def slA : SpecialLinearGroup (Fin 4) (ZMod 3) := ⟨matN codeA, det_matA⟩

@[expose] def slB : SpecialLinearGroup (Fin 4) (ZMod 3) := ⟨matN codeB, det_matB⟩

@[expose] noncomputable def xElt : projectiveSL 4 (ZMod 3) := proj 4 (ZMod 3) slA

@[expose] noncomputable def yElt : projectiveSL 4 (ZMod 3) := proj 4 (ZMod 3) slB

theorem rep_tabA : CFSG.Monster.B.Co2.Rep 80 (tab80 codeA false) (pi xElt) := by
  rw [xElt, pi_proj]
  exact rep_tab80 rfl matA_invT invTab_A

theorem rep_tabB : CFSG.Monster.B.Co2.Rep 80 (tab80 codeB false) (pi yElt) := by
  rw [yElt, pi_proj]
  exact rep_tab80 rfl matB_invT invTab_B

theorem card_P : Nat.card (projectiveSL 4 (ZMod 3)) = 6065280 := by
  have h := Subgroup.card_eq_card_quotient_mul_card_subgroup (scalars 4 (ZMod 3))
  rw [CFSG.RankThree.PartOne.card_scalars (by norm_num), card_SL_eq (by norm_num),
    Nat.card_zmod] at h
  have h2 : (3 : ℕ) ^ (4 * (4 - 1) / 2) * ∏ j ∈ Finset.Icc 2 4, (3 ^ j - 1) = 12130560 := by
    decide
  have h3 : Nat.gcd 4 (3 - 1) = 2 := by norm_num
  rw [h2, h3] at h
  change 12130560 = Nat.card (projectiveSL 4 (ZMod 3)) * 2 at h
  omega

end CFSG.ComponentClassification.HarrisLit.P1.L43
