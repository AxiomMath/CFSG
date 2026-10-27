module

public import Certificates.Data.Kernel.ThCent.List
public import CFSG.Certificates.Kernel.ThCent.PinSound
public import CFSG.Certificates.Kernel.ThDemp.OrbCent

public section

namespace CFSG.KC.ThCent

open CFSG.KC.Th CFSG.KC.Th.BigS CFSG.KC.Th.Spec

theorem andB_tt {a b : Bool} (h : andB a b = true) : a = true ∧ b = true := by
  cases a <;> cases b <;> simp_all [andB]

theorem notB_tt {b : Bool} (h : notB b = true) : b = false := by
  cases b <;> simp_all [notB]

theorem all_of_chunkOK {α : Type} (f : α → Bool) (E : List α) (n K : Nat)
    (hK : E.length ≤ K * n) (h : ∀ k < K, chunkOK f E (k * n) n = true) :
    ∀ i (hi : i < E.length), f (E[i]'hi) = true := by
  intro i hi
  have hn : 0 < n := by
    rcases Nat.eq_zero_or_pos n with h0 | h0
    · subst h0
      have : E.length = 0 := by simpa using hK
      omega
    · exact h0
  have hk : i / n < K := by
    rw [Nat.div_lt_iff_lt_mul hn]
    omega
  have hc := h (i / n) hk
  unfold chunkOK at hc
  rw [List.all_eq_true] at hc
  have hlt : i % n < ((E.drop (i / n * n)).take n).length := by
    rw [List.length_take, List.length_drop]
    have := Nat.mod_lt i hn
    have e := Nat.div_add_mod i n
    refine lt_min this ?_
    rw [Nat.mul_comm] at e
    omega
  have := hc _ (List.getElem_mem hlt)
  rw [List.getElem_take, List.getElem_drop] at this
  have e : i / n * n + i % n = i := by
    have := Nat.div_add_mod i n
    rw [Nat.mul_comm] at this
    omega
  simp only [e] at this
  exact this

theorem distinctL_sound : ∀ l : List Nat, distinctL l = true → l.Nodup
  | [], _ => List.nodup_nil
  | x :: t, h => by
    have h' : andB (List.rec (motive := fun _ => Bool) true
        (fun y _ ih' => andB (notB (Nat.beq x y)) ih') t) (distinctL t) = true := h
    obtain ⟨h1, h2⟩ := andB_tt h'
    refine List.nodup_cons.2 ⟨fun hx => ?_, distinctL_sound t h2⟩
    have key : ∀ t' : List Nat, List.rec (motive := fun _ => Bool) true
        (fun y _ ih' => andB (notB (Nat.beq x y)) ih') t' = true → x ∉ t' := by
      intro t'
      induction t' with
      | nil => intro _; simp
      | cons y t' ih =>
        intro hy hmem
        obtain ⟨hy1, hy2⟩ := andB_tt hy
        rcases List.mem_cons.1 hmem with rfl | hmem
        · have := notB_tt hy1
          rw [Nat.beq_refl] at this
          exact Bool.noConfusion this
        · exact ih hy2 hmem
    exact key t h1 hx

variable {c rm tm0 tm1 tm2 tm3 tm4 tm5 tm6 tm7 up dg ONE : ℕ}
  (hk : constsOK c rm tm0 tm1 tm2 tm3 tm4 tm5 tm6 tm7 up dg ONE = true)
include hk

theorem pkMat_wordRFrom (V : ℕ → ℕ) : ∀ (w : List ℕ) (acc : ℕ),
    pkMat (wordRFrom c rm V w acc) = pkMat acc * (w.map fun r => pkMat (V r)).prod
  | [], acc => by simp [wordRFrom]
  | r :: w, acc => by
    change pkMat (strictF (mulB c rm acc (V r)) (wordRFrom c rm V w)) = _
    rw [strictF_eq, pkMat_wordRFrom V w, pkMat_mulB hk, List.map_cons, List.prod_cons,
      Matrix.mul_assoc]

theorem pkMat_wordR (V : ℕ → ℕ) (w : List ℕ) :
    pkMat (wordR c rm ONE V w) = (w.map fun r => pkMat (V r)).prod := by
  rw [wordR, pkMat_wordRFrom hk, pkMat_one hk, Matrix.one_mul]

theorem inLayout_wordRFrom (V : ℕ → ℕ) : ∀ (w : List ℕ) (acc : ℕ), InLayout acc →
    InLayout (wordRFrom c rm V w acc)
  | [], _, h => h
  | r :: w, acc, _ => by
    change InLayout (strictF (mulB c rm acc (V r)) (wordRFrom c rm V w))
    rw [strictF_eq]
    exact inLayout_wordRFrom V w _ (inLayout_mulB hk _ _)

theorem inLayout_wordR (V : ℕ → ℕ) (w : List ℕ) : InLayout (wordR c rm ONE V w) :=
  inLayout_wordRFrom hk V w ONE (inLayout_one hk)

theorem neB_sound {X Y : ℕ} (h : neB c rm ONE X Y = true) : pkMat X ≠ pkMat Y := by
  intro e
  have h1 := notB_tt h
  have e2 : mulB c rm X ONE = mulB c rm Y ONE :=
    pkMat_inj (inLayout_mulB hk _ _) (inLayout_mulB hk _ _)
      (by rw [pkMat_mulB hk, pkMat_mulB hk, e])
  rw [e2, Nat.beq_refl] at h1
  exact Bool.noConfusion h1

theorem pow_ne_one_of {P m : ℕ} (hm : m < 2 ^ 5)
    (h : notB (Nat.beq (powB c rm ONE P m (nat_lit 5)) ONE) = true) : pkMat P ^ m ≠ 1 := by
  intro e
  have h1 := notB_tt h
  have e2 : powB c rm ONE P m 5 = ONE :=
    pkMat_inj (inLayout_powB hk _ _ _) (inLayout_one hk)
      (by rw [pkMat_powB hk _ _ _ hm, e, pkMat_one hk])
  rw [show powB c rm ONE P m (nat_lit 5) = powB c rm ONE P m 5 from rfl, e2, Nat.beq_refl] at h1
  exact Bool.noConfusion h1

theorem ne_of_rowB {A B : ℕ} (h : rowB rm A 0 ≠ rowB rm B 0) : pkMat A ≠ pkMat B := by
  intro e
  apply h
  obtain ⟨-, hrm, -⟩ := consts_spec hk
  have lt : ∀ G, rowB rm G 0 < 2 ^ 248 := fun G => by
    subst hrm
    change Nat.land _ _ < _
    exact lt_of_le_of_lt Nat.and_le_right (by omega)
  refine pkVec_inj (lt A) (lt B) ?_
  have := pkVec_rowB hk A ⟨0, by norm_num⟩
  have h2 := pkVec_rowB hk B ⟨0, by norm_num⟩
  simp only at this h2
  rw [this, h2, e]

theorem witR_sound (V : ℕ → ℕ) (E : ℕ) : ∀ (ws : List (List ℕ × List ℕ)) (acc P : ℕ),
    witR c rm ONE V E ws acc = some P →
      pkMat P = pkMat acc * (ws.map fun p => pkMat (wordR c rm ONE V p.1) * pkMat E *
        pkMat (wordR c rm ONE V p.2)).prod ∧
      ∀ p ∈ ws, pkMat (wordR c rm ONE V p.1) * pkMat (wordR c rm ONE V p.2) = 1
  | [], acc, P, h => by
    have : acc = P := Option.some.inj h
    subst this
    simp
  | p :: ws, acc, P, h => by
    change strictF (wordR c rm ONE V p.1) (fun W => strictF (wordR c rm ONE V p.2)
      fun Wi => Bool.rec (motive := fun _ => Option ℕ) none
        (strictF (mulB c rm (mulB c rm (mulB c rm acc W) E) Wi) (witR c rm ONE V E ws))
        (Nat.beq (mulB c rm W Wi) ONE)) = some P at h
    rw [strictF_eq, strictF_eq] at h
    cases hb : Nat.beq (mulB c rm (wordR c rm ONE V p.1) (wordR c rm ONE V p.2)) ONE
    · rw [hb] at h
      change (none : Option ℕ) = some P at h
      cases h
    · rw [hb] at h
      change strictF _ _ = _ at h
      rw [strictF_eq] at h
      obtain ⟨h1, h2⟩ := witR_sound V E ws _ P h
      have hW : pkMat (wordR c rm ONE V p.1) * pkMat (wordR c rm ONE V p.2) = 1 := by
        rw [← pkMat_mulB hk, Nat.eq_of_beq_eq_true hb, pkMat_one hk]
      refine ⟨?_, ?_⟩
      · rw [h1, pkMat_mulB hk, pkMat_mulB hk, pkMat_mulB hk, List.map_cons, List.prod_cons]
        simp only [Matrix.mul_assoc]
      · intro q hq
        rcases List.mem_cons.1 hq with rfl | hq
        · exact hW
        · exact h2 q hq

theorem eltOK_sound {V : ℕ → ℕ} {Z m : ℕ} {w : List ℕ} {ws : List (List ℕ × List ℕ)} {v : ℕ}
    (hm : m < 2 ^ 5) (h : eltOK c rm ONE V Z m w ws v = true) :
    pkMat (wordR c rm ONE V w) * pkMat Z = pkMat Z * pkMat (wordR c rm ONE V w) ∧
      rowB rm (wordR c rm ONE V w) 0 = v ∧
      (pkMat (wordR c rm ONE V w) = 1 ∨
        ((pkMat (wordR c rm ONE V w) * (ws.map fun p => pkMat (wordR c rm ONE V p.1) *
          pkMat (wordR c rm ONE V w) * pkMat (wordR c rm ONE V p.2)).prod) ^ m ≠ 1 ∧
          ∀ p ∈ ws, pkMat (wordR c rm ONE V p.1) * pkMat (wordR c rm ONE V p.2) = 1)) := by
  unfold eltOK at h
  rw [strictF_eq] at h
  obtain ⟨h1, h⟩ := andB_tt h
  obtain ⟨h2, h3⟩ := andB_tt h
  refine ⟨by rw [← pkMat_mulB hk, ← pkMat_mulB hk, Nat.eq_of_beq_eq_true h1],
    Nat.eq_of_beq_eq_true h2, ?_⟩
  rcases Bool.or_eq_true_iff.1 h3 with h3 | h3
  · left
    rw [Nat.eq_of_beq_eq_true h3, pkMat_one hk]
  · right
    cases hw : witR c rm ONE V (wordR c rm ONE V w) ws (wordR c rm ONE V w) with
    | none => rw [hw] at h3; exact Bool.noConfusion h3
    | some P =>
      rw [hw] at h3
      obtain ⟨e1, e2⟩ := witR_sound hk V _ ws _ P hw
      refine ⟨?_, e2⟩
      rw [← e1]
      exact pow_ne_one_of hk hm h3

theorem pairOK7_sound {X Y : ℕ} (h : pairOK7 c rm ONE X Y = true) :
    pkMat X ^ 7 = 1 ∧ pkMat Y ^ 7 = 1 ∧ pkMat X * pkMat Y = pkMat Y * pkMat X ∧ pkMat X ≠ 1 ∧
      ∀ k < 7, pkMat Y ≠ pkMat X ^ k := by
  unfold pairOK7 at h
  obtain ⟨h1, h⟩ := andB_tt h
  obtain ⟨h2, h⟩ := andB_tt h
  obtain ⟨h3, h⟩ := andB_tt h
  obtain ⟨h4, h5⟩ := andB_tt h
  refine ⟨?_, ?_, ?_, ?_, fun k hk7 => ?_⟩
  · rw [← pkMat_powB hk _ _ 3 (by norm_num), Nat.eq_of_beq_eq_true h1, pkMat_one hk]
  · rw [← pkMat_powB hk _ _ 3 (by norm_num), Nat.eq_of_beq_eq_true h2, pkMat_one hk]
  · rw [← pkMat_mulB hk, ← pkMat_mulB hk, Nat.eq_of_beq_eq_true h3]
  · rw [← pkMat_one hk]
    exact neB_sound hk h4
  · have := List.all_eq_true.1 h5 k (List.mem_range.2 hk7)
    rw [← pkMat_powB hk _ _ 3 (by omega)]
    exact neB_sound hk this

theorem conjOK7_sound {V : ℕ → ℕ} {X Y Z a b : ℕ} {u : List ℕ} (ha : a < 8) (hb : b < 8)
    (h : conjOK7 c rm ONE V X Y Z a b u = true) :
    pkMat (wordR c rm ONE V u) * (pkMat X ^ a * pkMat Y ^ b) =
      pkMat Z * pkMat (wordR c rm ONE V u) := by
  unfold conjOK7 at h
  rw [strictF_eq] at h
  rw [← pkMat_powB hk _ _ 3 (by omega), ← pkMat_powB hk _ _ 3 (by omega), ← pkMat_mulB hk,
    ← pkMat_mulB hk, ← pkMat_mulB hk, Nat.eq_of_beq_eq_true h]

theorem pkMat_cubeP {X Y C i j k : ℕ} (hi : i < 8) (hj : j < 8) (hk' : k < 8) :
    pkMat (cubeP c rm ONE X Y C i j k) = pkMat X ^ i * pkMat Y ^ j * pkMat C ^ k := by
  unfold cubeP
  rw [pkMat_mulB hk, pkMat_mulB hk, pkMat_powB hk _ _ 3 (by omega), pkMat_powB hk _ _ 3 (by omega),
    pkMat_powB hk _ _ 3 (by omega)]

theorem cubeOK5_sound {X Y C : ℕ} (h : cubeOK5 c rm ONE X Y C = true) :
    pkMat X ^ 5 = 1 ∧ pkMat Y ^ 5 = 1 ∧ pkMat C * pkMat X = pkMat X * pkMat C ∧
      pkMat C * pkMat Y = pkMat Y * pkMat C := by
  unfold cubeOK5 at h
  obtain ⟨h1, h⟩ := andB_tt h
  obtain ⟨h2, h⟩ := andB_tt h
  obtain ⟨h3, h4⟩ := andB_tt h
  refine ⟨?_, ?_, ?_, ?_⟩
  · rw [← pkMat_powB hk _ _ 3 (by norm_num), Nat.eq_of_beq_eq_true h1, pkMat_one hk]
  · rw [← pkMat_powB hk _ _ 3 (by norm_num), Nat.eq_of_beq_eq_true h2, pkMat_one hk]
  · rw [← pkMat_mulB hk, ← pkMat_mulB hk, Nat.eq_of_beq_eq_true h3]
  · rw [← pkMat_mulB hk, ← pkMat_mulB hk, Nat.eq_of_beq_eq_true h4]

theorem conjOK5_sound {V : ℕ → ℕ} {X Y C i j k : ℕ} {u : List ℕ} (hi : i < 8) (hj : j < 8)
    (hk' : k < 8) (h : conjOK5 c rm ONE V X Y C i j k u = true) :
    pkMat (wordR c rm ONE V u) * (pkMat X ^ i * pkMat Y ^ j * pkMat C ^ k) =
      pkMat C * pkMat (wordR c rm ONE V u) := by
  unfold conjOK5 at h
  rw [strictF_eq] at h
  rw [← pkMat_cubeP hk hi hj hk', ← pkMat_mulB hk, ← pkMat_mulB hk, Nat.eq_of_beq_eq_true h]

end CFSG.KC.ThCent

end
