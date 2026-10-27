module

public import Certificates.Data.CFSGNative.PropA.Check
public import CFSG.Sporadic.Th.TableSpec

public section

namespace CFSG.EvenSporadicStandard.M12Std.PropA

open Equiv Subgroup CFSG.Sporadic CFSG.Sporadic.Th.Native CFSG.Sporadic.Schreier
open CFSG.Sporadic.SmallOddCore CFSG.Sporadic.SmallOddCore.Native
open CFSG.EvenSporadicStandard.M12Std.PropA.Native

variable {n : ℕ}

private lemma toNat_sub_one_lt_natAbs_of_pos {l : ℤ} (h : 0 < l) :
    (l - 1).toNat < l.natAbs := by
  rw [Int.toNat_lt' (Int.natAbs_pos.2 (by omega))]
  rw [Int.natAbs_of_nonneg (le_of_lt h)]
  omega

private lemma toNat_neg_sub_one_lt_natAbs_of_neg {l : ℤ} (h : l < 0) :
    (-l - 1).toNat < l.natAbs := by
  rw [Int.toNat_lt' (Int.natAbs_pos.2 (by omega))]
  rw [← Int.natAbs_neg l, Int.natAbs_of_nonneg (by omega : (0 : ℤ) ≤ -l)]
  omega

@[expose] noncomputable def letterG (gg : ℕ → Perm (Fin n)) (m : ℕ) (l : ℤ) : Perm (Fin n) :=
  if 0 < l ∧ (l - 1).toNat < m then gg (l - 1).toNat
  else if l < 0 ∧ (-l - 1).toNat < m then (gg (-l - 1).toNat)⁻¹ else 1

@[expose] noncomputable def wordP (gg : ℕ → Perm (Fin n)) (m : ℕ) (w : Word) : Perm (Fin n) :=
  Th.wordG (letterG gg m) w

theorem wordP_congr {gg gg' : ℕ → Perm (Fin n)} {m m' : ℕ} (hm : m' ≤ m)
    (hgg : ∀ l < m', gg l = gg' l) {w : Word} (hw : wordsLE m' w = true) :
    wordP gg m w = wordP gg' m' w := by
  unfold wordP Th.wordG
  congr 1
  apply List.map_congr_left
  intro l hl
  unfold wordsLE at hw
  have hl' := List.all_eq_true.mp hw l hl
  rw [Bool.and_eq_true] at hl'
  have hne : l ≠ 0 := bne_iff_ne.mp hl'.1
  have habs : l.natAbs ≤ m' := of_decide_eq_true hl'.2
  unfold letterG
  rcases lt_trichotomy l 0 with hlt | heq | hgt
  · have hltm : (-l - 1).toNat < m' := by
      have := toNat_neg_sub_one_lt_natAbs_of_neg hlt
      omega
    have hltm0 : (-l - 1).toNat < m := by omega
    have h1' : ¬(0 < l ∧ (l - 1).toNat < m) := by omega
    have h1'' : ¬(0 < l ∧ (l - 1).toNat < m') := by omega
    rw [if_neg h1', if_neg h1'', if_pos ⟨hlt, hltm0⟩, if_pos ⟨hlt, hltm⟩]
    rw [hgg _ hltm]
  · exact absurd heq hne
  · have hltm : (l - 1).toNat < m' := by
      have := toNat_sub_one_lt_natAbs_of_pos hgt
      omega
    have hltm0 : (l - 1).toNat < m := by omega
    rw [if_pos ⟨hgt, hltm0⟩, if_pos ⟨hgt, hltm⟩]
    exact hgg _ hltm

end CFSG.EvenSporadicStandard.M12Std.PropA
