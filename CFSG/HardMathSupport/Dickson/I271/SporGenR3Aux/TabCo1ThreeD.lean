module

public import CFSG.HardMathSupport.Dickson.I271.SporGenR3Aux.TabCo1PowBound
public import CFSG.Sporadic.Co1Block.Co1Equiv
public import Certificates.Certificate17590
public import Certificates.Certificate17591
public import CFSG.Sporadic.Co1.Module.InvGroupBase
public import CFSG.Sporadic.Co1.Module.OddBuildBase

public section

namespace CFSG.HardMathSupport.Dickson.I271.TabCo1ThreeD

open CFSG.Sporadic.SmallF2 CFSG.Sporadic.SmallF2.Native CFSG.Sporadic.Co1Schreier
  CFSG.Sporadic.Co1Block CFSG.HardMathSupport.Dickson.I271.TabCo1 CFSG.Blueprint

section GA



theorem threeD_bound :
    boundOK (colsOf (powList (c1Rows ()) 3)) 3 base conds cnts span comb = true ∧
      cnts.prod ≤ 544320 := by
  have h := (Certificates.certificate17591 : threeDCheck () = true)
  simpa only [threeDCheck, Bool.and_eq_true, decide_eq_true_eq] using h

theorem card_cent_threeD_le (x : ↥GA) (hx : MRep (c1Rows ()) (x : GL24)) :
    Nat.card ↥(Subgroup.centralizer ({x} : Set ↥GA)) ≤ 544320 := by
  obtain ⟨hb, hp⟩ := threeD_bound
  have hcard := card_inf_GA_le_of_powBound hx 3 hb
  rw [card_centralizer_GA_eq_inf]
  exact hcard.trans hp

end GA

section Native

open CFSG.Sporadic.Co1.Module.Odd CFSG.Sporadic.Co1.Module CFSG.Sporadic.Co1.OddNative Matrix

attribute [local irreducible] rr regsRows


@[expose] noncomputable def c1 : NativeSporadic.Co1 := rho3 * sRep 1

theorem sRep_one : sRep 1 = reg 73 := rfl

theorem mat_c1 : mat c1 = rowsMatrix 24 (c1Rows ()) := by
  have h1 : mat rho3 = rowsMatrix 24 (rr 27) := mat_reg 27
  have h2 : mat (sRep 1) = rowsMatrix 24 (rr 73) := by
    rw [sRep_one]
    exact mat_reg 73
  rw [c1, map_mul, h1, h2]
  unfold c1Rows
  exact (rowsMatrix_mulRows 24 (rr 27) (rr 73)).symm

theorem mrep_c1 : MRep (c1Rows ()) ((co1MatEquiv c1 : GA) : GL24) := by
  unfold MRep
  rw [co1MatEquiv_val]
  exact mat_c1.symm


theorem card_centralizer_c1_le :
    Nat.card ↥(Subgroup.centralizer ({c1} : Set NativeSporadic.Co1)) ≤ 544320 := by
  rw [card_centralizer_co1]
  exact card_cent_threeD_le _ mrep_c1

theorem card_centralizer_threeD_le {y : NativeSporadic.Co1} (hy : IsConj c1 y) :
    Nat.card ↥(Subgroup.centralizer ({y} : Set NativeSporadic.Co1)) ≤ 544320 := by
  obtain ⟨u, hu⟩ := isConj_iff.1 hy
  rw [← hu, card_centralizer_conj]
  exact card_centralizer_c1_le


theorem ncard_fix_c1 : {v : Fin 24 → ZMod 2 | co1Act c1 v = v}.ncard = 2 ^ 8 := by
  have h : fixCount [transposeRows 24 (c1Rows ())] = 256 := Certificates.certificate17590
  have h2 := ncard_fixedSet [c1Rows ()]
  have h3 : {v : Fin 24 → ZMod 2 | co1Act c1 v = v} =
      {v : Fin 24 → ZMod 2 | ∀ M ∈ [c1Rows ()], rowsMatrix 24 M *ᵥ v = v} := by
    ext v
    simp only [Set.mem_setOf_eq, List.mem_singleton, forall_eq, Odd.co1Act_eq_mulVec, mat_c1]
  rw [h3, h2]
  exact h

theorem ncard_fix_threeD {y : NativeSporadic.Co1} (hy : IsConj c1 y) :
    {v : Fin 24 → ZMod 2 | co1Act y v = v}.ncard = 2 ^ 8 := by
  obtain ⟨u, hu⟩ := isConj_iff.1 hy
  rw [← hu, ncard_fix_conj]
  exact ncard_fix_c1

end Native

end CFSG.HardMathSupport.Dickson.I271.TabCo1ThreeD
