module

public import CFSG.Certificates.Kernel.Ssa3Sound
public import CFSG.RankThree.Asc83Table.MatFacts

public section

namespace CFSG.KC.Ssa3

open CFSG.SectionRank.Native CFSG.RankThree.Asc83Table CFSG.RankThree.Asc83Table.Native

variable {d : ℕ}

theorem ssaOK_two {D : SData} {prog : List Op} {n : ℕ} (hs : ssaOK D prog n = true) : 2 ≤ n := by
  unfold ssaOK at hs
  simp only [Bool.and_eq_true, Nat.ble_eq] at hs
  exact hs.1.1.1

theorem ssaOK_prog {D : SData} {prog : List Op} {n : ℕ} (hs : ssaOK D prog n = true) :
    prog.all (Op.lt n) = true := by
  unfold ssaOK at hs
  simp only [Bool.and_eq_true] at hs
  exact hs.1.1.2

theorem getD_set_of_lt {V : List ℕ} {k r x : ℕ} (hr : r < V.length) :
    (V.set k x).getD r 0 = if k = r then x else V.getD r 0 := by
  rw [List.getD_eq_getElem _ _ (by simpa using hr), List.getD_eq_getElem _ _ hr,
    List.getElem_set]

theorem progS_sound {D : SData} (hs : structS D = true) (A B : Matrix (Fin d) (Fin d) (ZMod 3))
    {n : ℕ} : ∀ (prog : List Op) (xs V : List ℕ) (S : ℕ → Matrix (Fin d) (Fin d) (ZMod 3)),
    V.length = n → (∀ r < n, S r = val A B D (V.getD r 0)) → prog.all (Op.lt n) = true →
    progS D prog xs V = true → ∀ r < n, prog.foldl slpStep S r = val A B D (D.fv.getD r 0)
  | [], [], V, S, _, hS, _, h => by
    have hV : V = D.fv := beq_iff_eq.1 h
    subst hV
    exact hS
  | [], _ :: _, _, _, _, _, _, h => by simp [progS] at h
  | _ :: _, [], _, _, _, _, _, h => by cases ‹Op› <;> simp [progS] at h
  | .mul i j k :: prog, x :: xs, V, S, hV, hS, hp, h => by
    simp only [progS, Bool.and_eq_true] at h
    simp only [List.all_cons, Op.lt, Bool.and_eq_true, decide_eq_true_eq] at hp
    obtain ⟨⟨⟨hi, hj⟩, -⟩, hp⟩ := hp
    refine progS_sound hs A B prog xs (V.set k x) _ (by simpa using hV) (fun r hr => ?_) hp h.2
    rw [slpStep, Function.update_apply, getD_set_of_lt (by omega)]
    by_cases hk : r = k
    · rw [if_pos hk, if_pos hk.symm, hS i hi, hS j hj, ssa3S_mul hs h.1]
    · rw [if_neg hk, if_neg (Ne.symm hk), hS r hr]
  | .pow e i k :: prog, x :: xs, V, S, hV, hS, hp, h => by
    simp only [progS, Bool.and_eq_true] at h
    simp only [List.all_cons, Op.lt, Bool.and_eq_true, decide_eq_true_eq] at hp
    obtain ⟨⟨hi, -⟩, hp⟩ := hp
    refine progS_sound hs A B prog xs (V.set k x) _ (by simpa using hV) (fun r hr => ?_) hp h.2
    rw [slpStep, Function.update_apply, getD_set_of_lt (by omega)]
    by_cases hk : r = k
    · rw [if_pos hk, if_pos hk.symm, hS i hi, ssa3S_pid hs h.1]
    · rw [if_neg hk, if_neg (Ne.symm hk), hS r hr]

theorem slpRegs_of_ssaOK {D : SData} {prog : List Op} {n : ℕ} (hs : ssaOK D prog n = true)
    (A B : Matrix (Fin d) (Fin d) (ZMod 3)) {r : ℕ} (hr : r < n) :
    slpRegs A B prog r = val A B D (D.fv.getD r 0) := by
  have hs' := hs
  unfold ssaOK at hs'
  simp only [Bool.and_eq_true] at hs'
  obtain ⟨⟨⟨-, hp⟩, hst⟩, hprog⟩ := hs'
  refine progS_sound hst A B prog D.opn _ (slpInit A B) (by simp) (fun r hr => ?_) hp hprog r hr
  rw [List.getD_eq_getElem _ _ (by simpa using hr), List.getElem_map, List.getElem_range,
    slpInit]
  rcases Nat.lt_or_ge r 2 with h | h
  · interval_cases r
    · have hm : Nat.min 0 2 = 0 := rfl
      rw [hm, val.eq_1]
      rfl
    · have hm : Nat.min 1 2 = 1 := rfl
      rw [hm, val.eq_2]
      rfl
  · have hm : Nat.min r 2 = 2 := Nat.min_eq_right h
    rw [if_neg (by omega), if_neg (by omega), hm, ssa3S_val_two]

theorem holds_of_factM {D : SData} {prog : List Op} {n : ℕ} (hs : ssaOK D prog n = true)
    {A B : Matrix (Fin d) (Fin d) (ZMod 3)} {f : MFact} (h : factM (val A B D) D n f) :
    f.Holds (slpRegs A B prog) n := by
  have h' : f.Holds (fun r => val A B D (D.fv.getD r 0)) n := by
    cases f <;> exact h
  exact h'.congr fun r hr => (slpRegs_of_ssaOK hs A B hr).symm

end CFSG.KC.Ssa3

end
