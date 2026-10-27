module

public import Certificates.Data.Kernel.Co1Sub.Txt
public import CFSG.Certificates.Kernel.Griess13.SLPTextSound

public section

namespace CFSG.KC.Co1Sub

open CFSG.KC.G13

theorem decZ_eq (c : Nat) :
    decZ c = if c % 2 = 1 then -((c / 2 + 1 : Nat) : Int) else ((c / 2 + 1 : Nat) : Int) := by
  unfold decZ
  by_cases h : c % 2 = 1
  · have hb : Nat.beq (c % 2) 1 = true := Nat.beq_eq_true_eq _ _ ▸ h
    rw [if_pos h]
    change Bool.rec (motive := fun _ => Int) _ _ (Nat.beq (c % 2) 1) = _
    rw [hb]
    rfl
  · have hb : Nat.beq (c % 2) 1 = false := by
      cases h' : Nat.beq (c % 2) 1
      · rfl
      · exact absurd (Nat.eq_of_beq_eq_true h') h
    rw [if_neg h]
    change Bool.rec (motive := fun _ => Int) _ _ (Nat.beq (c % 2) 1) = _
    rw [hb]
    rfl

theorem nonemptyK_spec : ∀ {W : List (List Nat)}, nonemptyK W = true → ∀ w ∈ W, w ≠ []
  | [], _ => fun _ h => absurd h List.not_mem_nil
  | [] :: _, h => absurd h Bool.false_ne_true
  | (c :: w) :: W, h => by
    change nonemptyK W = true at h
    intro v hv
    rcases List.mem_cons.1 hv with rfl | hv
    · exact List.cons_ne_nil _ _
    · exact nonemptyK_spec h v hv

theorem splitOn_comma (cs : List Char) :
    (String.ofList cs).splitOn "," = (cs.splitOn ',').map String.ofList :=
  splitOn_one "," ',' rfl rfl (by decide) rfl (by decide) cs

theorem wordC_ok (w : List Nat) : OkC ['-', ','] (wordC w) :=
  intercalate_ok (sep_ok (by simp)) fun l hl => by
    obtain ⟨c, -, rfl⟩ := List.mem_map.1 hl
    exact intC_ok (by simp) _

theorem read_wordC {w : List Nat} (hw : w ≠ []) :
    ((String.ofList (wordC w)).splitOn ",").map (fun z => z.toInt?.getD 0) = w.map decZ := by
  rw [splitOn_comma, wordC, List.splitOn_intercalate ',' ?_ (by simpa using hw), List.map_map,
    List.map_map]
  · refine List.map_congr_left fun c _ => ?_
    simp only [Function.comp_apply, intC_toInt, Option.getD_some]
  · intro l hl
    obtain ⟨c, -, rfl⟩ := List.mem_map.1 hl
    exact (intC_ok (S := ['-']) (by simp) _).not_mem rfl (by simp)

theorem splitOn_wordsC {W : List (List Nat)} (hW : W ≠ []) (hne : nonemptyK W = true) :
    ((String.ofList (wordsC W)).splitOn ";").map
        (fun w => (w.splitOn ",").map fun z => z.toInt?.getD 0) = W.map (·.map decZ) := by
  rw [splitOn_semi, wordsC, List.splitOn_intercalate ';' ?_ (by simpa using hW), List.map_map,
    List.map_map]
  · exact List.map_congr_left fun w hw => read_wordC (nonemptyK_spec hne w hw)
  · intro l hl
    obtain ⟨w, -, rfl⟩ := List.mem_map.1 hl
    exact (wordC_ok w).not_mem rfl (by simp)

end CFSG.KC.Co1Sub

end
