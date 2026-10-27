module

public import CFSG.LocalAnalysis.AGLEmbedding.KFactProofs.Fi22FiveData
public import CFSG.Sporadic.FischerOddCore.ClosureSpec
public import CFSG.Monster.B.Fischer.Fi22CentralizerBase

public section

namespace CFSG.AGLEmbedding.KFactProofs.Fi22Five

open CFSG.Monster.B.Co2 CFSG.Monster.B.Co2.Native CFSG.Monster.B.Fischer
  CFSG.Sporadic.FischerOddCore

theorem evalW_nil : evalW [] = idA 3510 := by simp [evalW, wordA]

theorem evalW_cons (l : Int) (w : List Int) :
    evalW (l :: w) = compA 3510 (letterA fi22OrigArrs gensInv l) (evalW w) := by
  simp [evalW, wordA]

theorem gensInv_get {h : ℕ} (hh : h < 2) : gensInv[h]! = invCand 3510 (fi22ChainGen h) := by
  rw [gensInv, getElem!_pos _ h (by simp [fi22OrigArrs_size, hh]), Array.getElem_map,
    ← getElem!_pos _ h (by simp [fi22OrigArrs_size, hh]), fi22OrigArrs_get hh]

theorem exists_rep_evalW {w : List Int}
    (hw : lettersOK 2 w = true) : ∃ g ∈ fi22P, Rep 3510 (evalW w) g := by
  have hS : ∀ h < 2, Rep 3510 fi22OrigArrs[h]! (fi22GenPerm h) := fun h hh =>
    rep_fi22OrigArrs_nat h (by rw [fi22OrigArrs_size]; exact hh)
  have hSinv : ∀ h < 2, Rep 3510 gensInv[h]! (fi22GenPerm h)⁻¹ := fun h hh => by
    rw [gensInv_get hh]
    exact rep_inv_of_isInvA (rep_fi22Gen hh) (fi22Chain_check.2.1 h hh)
  induction w with
  | nil => exact ⟨1, one_mem _, by rw [evalW_nil]; exact rep_idA⟩
  | cons l w ih =>
    simp only [lettersOK, List.all_cons, Bool.and_eq_true, bne_iff_ne, ne_eq,
      decide_eq_true_eq] at hw
    obtain ⟨⟨hl0, hl2⟩, hw'⟩ := hw
    have hw'' : lettersOK 2 w = true := by
      simpa [lettersOK, List.all_eq_true] using hw'
    obtain ⟨g, hg, hrep⟩ := ih hw''
    have hlet := rep_letterA (gs := fi22GenPerm) (j := 2) hS hSinv (l := l) ⟨hl0, hl2⟩
    refine ⟨_ * g, mul_mem ?_ hg, by rw [evalW_cons]; exact rep_compA hlet hrep⟩
    have hmem : fi22GenPerm (l.natAbs - 1) ∈ fi22P :=
      fi22GenPerm_mem _ (by rw [fi22OrigArrs_size]; omega)
    split_ifs
    · exact hmem
    · exact inv_mem hmem

theorem rep_pw {A : Array Nat} {G : Equiv.Perm (Fin 3510)} (hA : Rep 3510 A G) (k : Nat) :
    Rep 3510 (pw A k) (G ^ k) :=
  rep_powA hA k

theorem rep_planeA {X Y : Equiv.Perm (Fin 3510)} (hX : Rep 3510 xA X) (hY : Rep 3510 yA Y)
    (i j : Nat) : Rep 3510 (planeA i j) (X ^ i * Y ^ j) :=
  rep_compA (rep_pw hX i) (rep_pw hY j)

end CFSG.AGLEmbedding.KFactProofs.Fi22Five
