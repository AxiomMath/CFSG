module

public import Certificates.Data.Kernel.J4R0

public section

namespace CFSG.KC.J4R0

open CFSG.KC.J4Q (mulJ vecJ getN wordJ)
open CFSG.KC.F2Dot (maskFrom xorL)
open CFSG.Sporadic.J4.ZCent (g0W rW tW)

variable {c rm one : Nat}

theorem relOK_spec {X : List Nat} {CT : List (List Nat)} {SQ : List Nat}
    (h : relOK c rm one X CT SQ = true) :
    (∀ k j, k < j → j < 12 → ent CT k j < 8 ∧
      mulJ c rm (getN one X k) (getN one X j) =
        mulJ c rm (mulJ c rm (getN one X j) (zK c rm one X (ent CT k j))) (getN one X k)) ∧
    (∀ k < 12, SQ.getD k 0 < 8 ∧
      mulJ c rm (getN one X k) (getN one X k) = zK c rm one X (SQ.getD k 0)) ∧
    (∀ i, 12 ≤ i → i < 15 → mulJ c rm (getN one X i) (getN one X i) = one ∧
      ∀ j < 15, mulJ c rm (getN one X i) (getN one X j) = mulJ c rm (getN one X j) (getN one X i)) := by
  simp only [relOK, Bool.and_eq_true, List.all_eq_true, List.mem_range, Bool.or_eq_true,
    Bool.not_eq_true', decide_eq_false_iff_not, Nat.not_lt, Nat.blt_eq, Nat.beq_eq,
    List.mem_cons, List.not_mem_nil, or_false] at h
  obtain ⟨⟨h1, h2⟩, h3⟩ := h
  refine ⟨fun k j hkj hj => ?_, fun k hk => h2 k hk, fun i hi1 hi2 => ?_⟩
  · rcases h1 k (by omega) j hj with h | h
    · omega
    · exact h
  · have : i = 12 ∨ i = 13 ∨ i = 14 := by omega
    exact h3 i this

theorem sep1_spec {X : List Nat} {k : Nat} {O : List Nat} (h : sep1 rm one X k O = true) :
    O ≠ [] ∧ (∀ o ∈ O, o < 2 ^ 112) ∧
      (∀ o ∈ O, ∀ j, k < j → j < 15 → vecJ rm o (getN one X j) ∈ O) ∧
      vecJ rm (O.headD 0) (getN one X k) ∉ O := by
  simp only [sep1, memN, Bool.and_eq_true, Bool.not_eq_true', List.isEmpty_eq_false_iff,
    List.all_eq_true, Nat.blt_eq, List.mem_range, Bool.or_eq_true, decide_eq_false_iff_not,
    Nat.not_lt, List.any_eq_true, Nat.beq_eq, List.any_eq_false] at h
  obtain ⟨⟨⟨h0, h1⟩, h2⟩, h3⟩ := h
  refine ⟨h0, h1, fun o ho j hkj hj => ?_, fun hm => h3 _ hm (by simp)⟩
  rcases h2 o ho j hj with h | ⟨p, hp, hpe⟩
  · omega
  · rw [hpe]; exact hp

theorem sepOK_spec {X : List Nat} {SEP : List (List Nat)} (h : sepOK rm one X SEP = true) :
    ∀ k < 15, sep1 rm one X k (SEP.getD k []) = true := by
  simp only [sepOK, List.all_eq_true, List.mem_range] at h
  exact h

theorem radOK_spec {CT RL : List (List Nat)} (h : radOK CT RL = true) :
    ∀ p < 12, (∀ q ∈ RL.getD p [], q < 36) ∧ xorL ((RL.getD p []).map (colK CT)) = 2 ^ p := by
  simp only [radOK, List.all_eq_true, List.mem_range, Bool.and_eq_true, Nat.blt_eq,
    Nat.beq_eq] at h
  exact h

theorem normOK_spec {X : List Nat} {g : Nat} {N : List Nat} (h : normOK c rm one X g N = true) :
    ∀ j < 15, mulJ c rm g (getN one X j) = mulJ c rm (wK c rm one X (N.getD j 0) 0 15) g := by
  simp only [normOK, List.all_eq_true, List.mem_range, Nat.beq_eq] at h
  exact h

theorem coverOK_spec {X T : List Nat} {g : Nat} {CV : List (Nat × Nat)}
    (h : coverOK c rm one X T g CV = true) :
    ∀ i < 60, (CV.getD i (0, 0)).1 < 60 ∧ mulJ c rm (getN one T i) g =
      mulJ c rm (getN one T (CV.getD i (0, 0)).1) (wK c rm one X (CV.getD i (0, 0)).2 0 15) := by
  simp only [coverOK, List.all_eq_true, List.mem_range, Bool.and_eq_true, Nat.blt_eq,
    Nat.beq_eq] at h
  exact h

theorem gwOK_spec {X B : List Nat} {a b : Nat} {GW : List (List Nat × Nat)}
    (h : gwOK c rm one X B a b GW = true) :
    ∀ j < 16, (∀ l ∈ (GW.getD j ([], 0)).1, l < 2) ∧ getN one B j =
      mulJ c rm (posW c rm one a b (GW.getD j ([], 0)).1) (wK c rm one X (GW.getD j ([], 0)).2 0 15) := by
  simp only [gwOK, List.all_eq_true, List.mem_range, Bool.and_eq_true, Nat.blt_eq,
    Nat.beq_eq] at h
  exact h

theorem zbOK_spec {X B : List Nat} (h : zbOK c rm one X B = true) :
    ∀ i, 12 ≤ i → i < 15 → ∀ j < 16,
      mulJ c rm (getN one X i) (getN one B j) = mulJ c rm (getN one B j) (getN one X i) := by
  simp only [zbOK, List.all_eq_true, List.mem_range, Nat.beq_eq, List.mem_cons,
    List.not_mem_nil, or_false] at h
  intro i hi1 hi2
  have : i = 12 ∨ i = 13 ∨ i = 14 := by omega
  exact h i this

theorem baseOK_spec {GL B X T : List Nat} {B3I B4I : Nat} (h : baseOK c rm one GL B X T B3I B4I = true) :
    (∀ i < 16, getN one B i = wordJ c rm one GL [] (g0W.getD i [])) ∧
    B3I = mulJ c rm (mulJ c rm (getN one B 3) (getN one B 3)) (getN one B 3) ∧
    mulJ c rm (getN one B 3) B3I = one ∧
    B4I = mulJ c rm (getN one B 4) (getN one B 4) ∧
    mulJ c rm (getN one B 4) B4I = one ∧
    (∀ k < 15, getN one X k = xw c rm one B [one, one, one, B3I, B4I] X k) ∧
    (∀ i < 60, getN one T i = wordJ c rm one B [one, one, one, B3I, B4I] (tW.getD i [])) := by
  simp only [baseOK, Bool.and_eq_true, List.all_eq_true, List.mem_range, Nat.beq_eq] at h
  obtain ⟨⟨⟨⟨⟨⟨h1, h2⟩, h3⟩, h4⟩, h5⟩, h6⟩, h7⟩ := h
  exact ⟨h1, h2, h3, h4, h5, h6, h7⟩

end CFSG.KC.J4R0
