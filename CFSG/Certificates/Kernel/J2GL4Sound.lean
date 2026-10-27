module

public import CFSG.Sporadic.Bridge.J2Native
public import CFSG.RankThree.PartTwo.Sec17.J2NotGL4Words

public section

namespace CFSG.KC.J2GL4

open CFSG.Sporadic.Bridge.J2 CFSG.RankThree.PartTwo.Sec17.J2NotGL4

def redM (X : List (List ℕ)) : Prop := wfM X = true ∧ ∀ r ∈ X, ∀ x ∈ r, x < 5

theorem redM_mulL {X : List (List ℕ)} (hX : wfM X = true) (Y : List (List ℕ)) :
    redM (mulL X Y) := by
  refine ⟨wfM_mulL hX, fun r hr x hx => ?_⟩
  simp only [mulL, List.mem_map] at hr
  obtain ⟨_, _, rfl⟩ := hr
  simp only [List.mem_map] at hx
  obtain ⟨_, _, rfl⟩ := hx
  exact Nat.mod_lt _ (by norm_num)

theorem redM_idL : redM idL := by
  refine ⟨wfM_idL, ?_⟩
  decide

theorem lwordL_append (X Xi : ℕ → List (List ℕ)) :
    ∀ (u v : List (ℕ × Bool)) (acc : List (List ℕ)),
      lwordL X Xi (u ++ v) acc = lwordL X Xi v (lwordL X Xi u acc) := by
  intro u
  induction u with
  | nil => intro v acc; rfl
  | cons l u ih => intro v acc; exact ih v _

theorem redM_lwordL : ∀ (w : List (ℕ × Bool)) (acc : List (List ℕ)), redM acc →
    redM (lwordL natX natXi w acc) := by
  intro w
  induction w with
  | nil => intro acc h; exact h
  | cons l w ih => intro acc h; exact ih _ (redM_mulL h.1 _)

noncomputable def wordM (w : List (ℕ × Bool)) : Matrix (Fin 14) (Fin 14) (ZMod 5) :=
  toM (lwordL natX natXi w idL)

theorem toM_lwordL_acc (w : List (ℕ × Bool)) {acc : List (List ℕ)} (hacc : wfM acc = true) :
    toM (lwordL natX natXi w acc) = toM acc * wordM w := by
  have h1 := toM_lwordL natX_wf natXi_wf natU_val natU_inv w acc hacc
  have h2 := toM_lwordL natX_wf natXi_wf natU_val natU_inv w idL wfM_idL
  rw [toM_idL, one_mul] at h2
  rw [← h1, h2, wordM]

theorem wordM_nil : wordM [] = 1 := toM_idL

theorem wordM_append (u v : List (ℕ × Bool)) : wordM (u ++ v) = wordM u * wordM v := by
  unfold wordM
  rw [lwordL_append, toM_lwordL_acc v (redM_lwordL u idL redM_idL).1, wordM]

theorem wordM_pw (w : List (ℕ × Bool)) (k : ℕ) : wordM (pw w k) = wordM w ^ k := by
  induction k with
  | zero => simpa [pw] using wordM_nil
  | succ k ih =>
    have : pw w (k + 1) = w ++ pw w k := by simp [pw, List.replicate_succ]
    rw [this, wordM_append, ih, pow_succ']

theorem wordM_of_lwordL {w : List (ℕ × Bool)} {M : List (List ℕ)}
    (h : (lwordL natX natXi w idL == M) = true) : wordM w = toM M := by
  rw [wordM, eq_of_beq h]

@[expose] noncomputable def termM (B : ℕ → List (List ℕ)) (t : List (ℕ × ℕ)) :
    Matrix (Fin 14) (Fin 14) (ZMod 5) :=
  (t.map fun p => toM (B p.1) ^ p.2).prod

end CFSG.KC.J2GL4

end
