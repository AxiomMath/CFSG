module

public import Certificates.Data.Kernel.ThPump.Defs
public import CFSG.Certificates.Kernel.ThCent.PinSoundBase

public section

namespace CFSG.KC.ThPump

open CFSG.KC.Th CFSG.KC.Th.BigS CFSG.KC.ThCent CFSG.KC.Th.Spec

theorem andP_tt {a b : Bool} (h : andP a b = true) : a = true ∧ b = true := by
  cases a <;> cases b <;> simp_all [andP]

theorem beq_false_of_ne {r n : Nat} (h : r ≠ n) : Nat.beq r n = false := by
  cases e : Nat.beq r n
  · rfl
  · exact absurd (Nat.eq_of_beq_eq_true e) h

theorem isLet_sound {r : Nat} (h : isLet r = true) : r = 19 ∨ r = 99 ∨ r = 114 ∨ r = 115 := by
  by_cases h1 : r = 19
  · exact Or.inl h1
  by_cases h2 : r = 99
  · exact Or.inr (Or.inl h2)
  by_cases h3 : r = 114
  · exact Or.inr (Or.inr (Or.inl h3))
  unfold isLet at h
  rw [beq_false_of_ne h1, beq_false_of_ne h2, beq_false_of_ne h3] at h
  exact Or.inr (Or.inr (Or.inr (Nat.eq_of_beq_eq_true h)))

theorem letsOK_sound : ∀ U : List (List Nat), letsOK U = true →
    ∀ w ∈ U, ∀ r ∈ w, r = 19 ∨ r = 99 ∨ r = 114 ∨ r = 115
  | [], _ => by simp
  | w :: U, h => by
    change andP (List.rec (motive := fun _ => Bool) true
      (fun r _ ih' => andP (isLet r) ih') w) (letsOK U) = true at h
    obtain ⟨h1, h2⟩ := andP_tt h
    have key : ∀ w' : List Nat, List.rec (motive := fun _ => Bool) true
        (fun r _ ih' => andP (isLet r) ih') w' = true →
        ∀ r ∈ w', r = 19 ∨ r = 99 ∨ r = 114 ∨ r = 115 := by
      intro w'
      induction w' with
      | nil => simp
      | cons r w' ih =>
        intro hw r' hr'
        obtain ⟨hr1, hr2⟩ := andP_tt hw
        rcases List.mem_cons.1 hr' with rfl | hr'
        · exact isLet_sound hr1
        · exact ih hr2 r' hr'
    intro w' hw'
    rcases List.mem_cons.1 hw' with rfl | hw'
    · exact key _ h1
    · exact letsOK_sound U h2 w' hw'

theorem rowsOK_sound (rm : Nat) (F G : Nat → Nat) (T : Nat) :
    ∀ (U : List (List Nat)) (D : List Nat), rowsOK rm F G T U D = true →
      D = U.map (conjRow rm F G T)
  | [], [], _ => rfl
  | [], _ :: _, h => by
    change false = true at h
    exact Bool.noConfusion h
  | _ :: _, [], h => by
    change false = true at h
    exact Bool.noConfusion h
  | w :: U, d :: D, h => by
    change andP (Nat.beq (conjRow rm F G T w) d) (rowsOK rm F G T U D) = true at h
    obtain ⟨h1, h2⟩ := andP_tt h
    rw [List.map_cons, ← rowsOK_sound rm F G T U D h2, Nat.eq_of_beq_eq_true h1]

variable {c rm tm0 tm1 tm2 tm3 tm4 tm5 tm6 tm7 up dg ONE : ℕ}
  (hk : constsOK c rm tm0 tm1 tm2 tm3 tm4 tm5 tm6 tm7 up dg ONE = true)
include hk

theorem pkVec_vWord (F : ℕ → ℕ) : ∀ (w : List ℕ) (v : ℕ),
    pkVec (vWord rm F w v) = Matrix.vecMul (pkVec v) (w.map fun r => pkMat (F r)).prod
  | [], v => by
    change pkVec v = _
    rw [List.map_nil, List.prod_nil, Matrix.vecMul_one]
  | r :: w, v => by
    change pkVec (strictF (vecB rm v (F r)) (vWord rm F w)) = _
    rw [strictF_eq, pkVec_vWord F w, pkVec_vecB hk, Matrix.vecMul_vecMul, List.map_cons,
      List.prod_cons]

theorem pkVec_vWordRev (G : ℕ → ℕ) : ∀ (w : List ℕ) (v : ℕ),
    pkVec (vWordRev rm G w v) = Matrix.vecMul (pkVec v) (w.reverse.map fun r => pkMat (G r)).prod
  | [], v => by
    change pkVec v = _
    rw [List.reverse_nil, List.map_nil, List.prod_nil, Matrix.vecMul_one]
  | r :: w, v => by
    change pkVec (strictF (vWordRev rm G w v) fun x => vecB rm x (G r)) = _
    rw [strictF_eq, pkVec_vecB hk, pkVec_vWordRev G w, Matrix.vecMul_vecMul, List.reverse_cons,
      List.map_append, List.prod_append, List.map_singleton, List.prod_singleton]

theorem pkVec_conjRow (F G : ℕ → ℕ) (T : ℕ) (w : List ℕ) :
    pkVec (conjRow rm F G T w) = Matrix.vecMul (pkVec 1)
      ((w.map fun r => pkMat (F r)).prod * pkMat T * (w.reverse.map fun r => pkMat (G r)).prod) := by
  unfold conjRow
  rw [strictF_eq, strictF_eq, pkVec_vWordRev hk, pkVec_vecB hk, pkVec_vWord hk,
    Matrix.vecMul_vecMul, Matrix.vecMul_vecMul, Matrix.mul_assoc]

theorem vWordRev_lt (G : ℕ → ℕ) : ∀ (w : List ℕ) (v : ℕ), v < 2 ^ 248 →
    vWordRev rm G w v < 2 ^ 248
  | [], _, h => h
  | r :: w, v, _ => by
    change strictF (vWordRev rm G w v) (fun x => vecB rm x (G r)) < 2 ^ 248
    rw [strictF_eq]
    exact vecB_lt hk _ _

theorem conjRow_lt (F G : ℕ → ℕ) (T : ℕ) (w : List ℕ) : conjRow rm F G T w < 2 ^ 248 := by
  unfold conjRow
  rw [strictF_eq, strictF_eq]
  exact vWordRev_lt hk G w _ (vecB_lt hk _ _)

end CFSG.KC.ThPump

end
