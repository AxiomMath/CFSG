module

public import CFSG.LocalAnalysis.OddStandard.ONanB2Facts
public import Certificates.Data.ONanB2Mirror

public section

namespace CFSG.OddStandard.ONanRec.CM

theorem lt12_aW : ∀ c ∈ aW, c < 12 := by decide
theorem lt12_bW : ∀ c ∈ bW, c < 12 := by decide
theorem lt12_cW : ∀ c ∈ cW, c < 12 := by decide

theorem lt12_g2W : ∀ c ∈ g2W, c < 12 :=
  lt12_append (lt12_append lt12_gW lt12_fW) (lt12_wpow lt12_yW 3)

@[expose] noncomputable def aP : Equiv.Perm (Fin 480) := wordPerm aW

@[expose] noncomputable def bP : Equiv.Perm (Fin 480) := wordPerm bW

@[expose] noncomputable def cP : Equiv.Perm (Fin 480) := wordPerm cW

@[expose] noncomputable def gen2Perm (i : Fin 6) : Equiv.Perm (Fin 480) :=
  wordPerm (substG2 (2 * i.val))

theorem lt12_substG2 (c : ℕ) (hc : c < 12) : ∀ x ∈ substG2 c, x < 12 := by
  unfold substG2
  split_ifs with h1 h2
  · exact lt12_g2W
  · exact invWord_lt lt12_g2W
  · intro x hx
    simp only [List.mem_singleton] at hx
    omega

theorem wordPerm_substG2_code (h : cmLettersOK = true) (l : Fin 6 × Bool) :
    wordPerm (substG2 (code l)) = cond l.2 (gen2Perm l.1) (gen2Perm l.1)⁻¹ := by
  obtain ⟨i, b⟩ := l
  have hi := i.2
  cases b
  · show wordPerm (substG2 (2 * i.val + 1)) = (wordPerm (substG2 (2 * i.val)))⁻¹
    by_cases h5 : i.val = 5
    · rw [h5]
      have e1 : substG2 (2 * 5 + 1) = invWord g2W := rfl
      have e2 : substG2 (2 * 5) = g2W := rfl
      rw [e1, e2]
      exact wordPerm_inv h lt12_g2W
    · have e1 : substG2 (2 * i.val + 1) = [2 * i.val + 1] := by
        unfold substG2
        split_ifs <;> first | omega | rfl
      have e2 : substG2 (2 * i.val) = [2 * i.val] := by
        unfold substG2
        split_ifs <;> first | omega | rfl
      rw [e1, e2]
      simp only [wordPerm, List.map_cons, List.map_nil, List.prod_cons, List.prod_nil, mul_one]
      exact letterPerm_odd h hi
  · rfl

theorem wordPerm_flatMap {L : List ℕ} (s : ℕ → List ℕ) :
    wordPerm (L.flatMap s) = (L.map fun c => wordPerm (s c)).prod := by
  induction L with
  | nil => simp [wordPerm]
  | cons c L ih => rw [List.flatMap_cons, wordPerm_append, ih, List.map_cons, List.prod_cons]

theorem lift_mk_gen2 (h : cmLettersOK = true) (w : List (Fin 6 × Bool)) :
    FreeGroup.lift gen2Perm (FreeGroup.mk w) = wordPerm ((w.map code).flatMap substG2) := by
  rw [FreeGroup.lift_mk, wordPerm_flatMap, List.map_map]
  refine congrArg List.prod (List.map_congr_left fun l _ => ?_)
  rw [Function.comp_apply, wordPerm_substG2_code h l]

structure MirrorFactsP : Prop where
  y_sq : yP * yP = aP
  comm1 : yP * (r1P * r2P * r2P) * yP⁻¹ * (r1P * r2P * r2P)⁻¹ = r1P
  comm2 : yP * (r1P * r2P) * yP⁻¹ * (r1P * r2P)⁻¹ = r2P
  y_z : yP * zP = zP * yP
  y_d : yP * dP = dP * yP
  x5_pow : (yP * bP * cP) ^ 5 = 1
  x5_ne : yP * bP * cP ≠ 1
  g_z : gP⁻¹ * zP * gP = zP ^ 3
  g_d : gP⁻¹ * dP * gP = zP * dP

@[expose] noncomputable def evalP (u t : Equiv.Perm (Fin 480)) (w : List ℕ) :
    Equiv.Perm (Fin 480) :=
  (w.map fun k => if k = 1 then r1P else if k = 2 then r2P else if k = 3 then u else t).prod

@[expose] def MirrorChainP : Prop :=
  ∀ l < 2, ∀ m ∈ M480, m * m = 1 → m ≠ 1 → m * zP = zP * m →
    m * (yP * fP ^ l) * m = (yP * fP ^ l)⁻¹ →
    (l = 0 ∧ ∃ k < 4, m * (yP * fP ^ l) ^ k = cP ∨ m * (yP * fP ^ l) ^ k = dP * cP * dP) ∨
      ∃ w ∈ badWords,
        ((evalP (yP * fP ^ l) m w) ^ 6 = 1 ∧ (evalP (yP * fP ^ l) m w) ^ 2 ≠ 1 ∧
          (evalP (yP * fP ^ l) m w) ^ 3 ≠ 1) ∨
        ((evalP (yP * fP ^ l) m w) ^ 8 = 1 ∧ (evalP (yP * fP ^ l) m w) ^ 4 ≠ 1)

end CFSG.OddStandard.ONanRec.CM
