module

public import Certificates.Data.Kernel.SmithD6.WtCheck
public import CFSG.Certificates.Kernel.KeyTreeChunksSound

public section

namespace CFSG.KD.SmithD6

open CFSG.SmithD6 CFSG.KC.KeyTree

theorem isNilB_eq {α : Type} : ∀ l : List α, isNilB l = true ↔ l = []
  | [] => by simp [isNilB]
  | _ :: _ => by simp [isNilB]

theorem exPinGo_sound : ∀ (a b : List Nat), exPinGo a b = true →
    b = a.map exC ∧ ∀ x ∈ a, x < 4294967296
  | [], b, h => by
    have e : exPinGo [] b = isNilB b := rfl
    rw [e, isNilB_eq] at h
    simp [h]
  | _ :: _, [], h => absurd h (by simp [exPinGo])
  | x :: a, y :: b, h => by
    have e : exPinGo (x :: a) (y :: b) =
        bAnd(Nat.blt x 4294967296, bAnd(Nat.beq (exC x) y, exPinGo a b)) := rfl
    rw [e] at h
    obtain ⟨h1, h2⟩ := band_true h
    obtain ⟨h2, h3⟩ := band_true h2
    obtain ⟨ih1, ih2⟩ := exPinGo_sound a b h3
    refine ⟨?_, ?_⟩
    · rw [List.map_cons, ← ih1, Nat.eq_of_beq_eq_true h2]
    · intro z hz
      rcases List.mem_cons.1 hz with rfl | hz
      · exact Nat.le_of_ble_eq_true h1
      · exact ih2 z hz

theorem closeGo_sound {t : KT} {ts : List (Nat × Nat × Bool)} :
    ∀ l : List Nat, closeGo t ts l = true → ∀ s ∈ l, t.memB (liftT ts s) = true
  | [], _, s, hs => absurd hs (List.not_mem_nil)
  | x :: l, h, s, hs => by
    have e : closeGo t ts (x :: l) = bAnd(KT.memB (liftT ts x) t, closeGo t ts l) := rfl
    rw [e] at h
    obtain ⟨h1, h2⟩ := band_true h
    rcases List.mem_cons.1 hs with rfl | hs
    · exact h1
    · exact closeGo_sound l h2 s hs

theorem lenN_eq : ∀ l : List Nat, lenN l = l.length
  | [] => rfl
  | _ :: l => by
    change Nat.succ (lenN l) = _
    rw [lenN_eq l]
    rfl

theorem fld_one_eq (x i : Nat) : Nat.land (Nat.shiftRight x i) 1 = bif x.testBit i then 1 else 0 := by
  simp only [Nat.land_eq, Nat.shiftRight_eq', Nat.and_one_is_mod]
  rcases Nat.mod_two_eq_zero_or_one (x >>> i) with h | h <;>
    simp [Nat.testBit, Nat.and_comm 1, Nat.and_one_is_mod, h]

theorem testBit_bitShift (c : Bool) (k j : Nat) :
    (Nat.shiftLeft (bif c then 1 else 0) k).testBit j = (c && j == k) := by
  by_cases h : j = k
  · subst h
    cases c <;> simp [Nat.one_shiftLeft, Nat.testBit_two_pow]
  · have h' : k ≠ j := fun e => h e.symm
    cases c <;> simp [h, h', Nat.one_shiftLeft, Nat.testBit_two_pow]

theorem bit_mul_eq (x i a : Nat) :
    (bif x.testBit i then a else 0) = Nat.mul a (fld(x, i, 1)) := by
  rw [fld_one_eq]
  cases x.testBit i <;> simp

theorem rhoK_eq (x s : Nat) : rhoK x s = rhoC x s := by
  simp only [rhoC, xorFold, List.range_succ, List.range_zero, List.nil_append,
    List.foldl_append, List.foldl_cons, List.foldl_nil, bit_mul_eq]
  rfl

theorem annGo_sound {s : Nat} : ∀ bs : List Nat, annGo s bs = true →
    ∀ b ∈ bs, b < 4096 ∧ rhoC b s = 0
  | [], _, b, hb => absurd hb (List.not_mem_nil)
  | x :: bs, h, b, hb => by
    have e : annGo s (x :: bs) =
        bAnd(Nat.blt x 4096, bAnd(Nat.beq (rhoK x s) 0, annGo s bs)) := rfl
    rw [e] at h
    obtain ⟨h1, h2⟩ := band_true h
    obtain ⟨h2, h3⟩ := band_true h2
    rcases List.mem_cons.1 hb with rfl | hb
    · exact ⟨Nat.le_of_ble_eq_true h1, by rw [← rhoK_eq]; exact Nat.eq_of_beq_eq_true h2⟩
    · exact annGo_sound bs h3 b hb

theorem testBit_colGo (p : Nat) : ∀ (bs : List Nat) (k j : Nat),
    (colGo p bs k).testBit j = (decide (k ≤ j) && (bs.getD (j - k) 0).testBit p)
  | [], k, j => by
    change (0 : Nat).testBit j = _
    simp
  | b :: bs, k, j => by
    change (Nat.lor (Nat.shiftLeft (Nat.land (Nat.shiftRight b p) 1) k)
      (colGo p bs (Nat.succ k))).testBit j = _
    rw [fld_one_eq, Nat.lor_eq, Nat.testBit_or, testBit_bitShift, testBit_colGo p bs]
    rcases Nat.lt_trichotomy j k with hj | rfl | hj
    · simp [Nat.ne_of_lt hj, Nat.not_le.2 hj, show ¬ k + 1 ≤ j by omega]
    · simp [Nat.not_succ_le_self]
    · have h2 : j - k = (j - (k + 1)) + 1 := by omega
      simp [Nat.ne_of_gt hj, Nat.le_of_lt hj, show k + 1 ≤ j by omega, h2, List.getD_cons_succ]

theorem pivGo_sound (bs : List Nat) : ∀ (ps : List Nat) (m : Nat), pivGo bs ps m = true →
    ∀ j < ps.length, ∀ k < bs.length, (bs.getD k 0).testBit (ps.getD j 0) = (k == m + j)
  | [], _, _, j, hj, _, _ => absurd hj (Nat.not_lt_zero _)
  | p :: ps, m, h, j, hj, k, hk => by
    have e : pivGo bs (p :: ps) m =
        bAnd(Nat.beq (colGo p bs 0) (Nat.shiftLeft 1 m), pivGo bs ps (Nat.succ m)) := rfl
    rw [e] at h
    obtain ⟨h1, h2⟩ := band_true h
    rcases j with _ | j
    · have hc := congrArg (fun x => Nat.testBit x k) (Nat.eq_of_beq_eq_true h1)
      simp only [testBit_colGo, Nat.zero_le, decide_true, Bool.true_and, Nat.sub_zero,
        Nat.shiftLeft_eq', Nat.one_shiftLeft, Nat.testBit_two_pow] at hc
      rw [List.getD_cons_zero, hc, Nat.add_zero]
      by_cases hkm : k = m
      · simp [hkm]
      · simp [hkm, Ne.symm hkm]
    · rw [List.getD_cons_succ, pivGo_sound bs ps (m + 1) h2 j (by simpa using hj) k hk]
      congr 1
      omega

theorem planeL_sound {s : Nat} {bs ps : List Nat} (h : planeL s bs ps = true) :
    0 < s ∧ bs.length = 6 ∧ ps.length = 6 ∧ (∀ b ∈ bs, b < 4096 ∧ rhoC b s = 0) ∧
      ∀ j < 6, ∀ k < 6, (bs.getD k 0).testBit (ps.getD j 0) = (k == j) := by
  obtain ⟨h1, h⟩ := band_true h
  obtain ⟨h2, h⟩ := band_true h
  obtain ⟨h3, h⟩ := band_true h
  obtain ⟨h4, h5⟩ := band_true h
  have l1 : bs.length = 6 := by rw [← lenN_eq]; exact Nat.eq_of_beq_eq_true h2
  have l2 : ps.length = 6 := by rw [← lenN_eq]; exact Nat.eq_of_beq_eq_true h3
  refine ⟨Nat.le_of_ble_eq_true h1, l1, l2, annGo_sound bs h4, fun j hj k hk => ?_⟩
  rw [pivGo_sound bs ps 0 h5 j (by omega) k (by omega), Nat.zero_add]

theorem planeGo_sound : ∀ (ss : List Nat) (Bs Ps : List (Array Nat)), planeGo ss Bs Ps = true →
    Bs.length = ss.length ∧ Ps.length = ss.length ∧
      ∀ i < ss.length, planeL (ss.getD i 0) (Bs.getD i #[]).toList (Ps.getD i #[]).toList = true
  | [], Bs, Ps, h => by
    obtain ⟨h1, h2⟩ := band_true h
    rw [isNilB_eq] at h1 h2
    simp [h1, h2]
  | _ :: _, [], _, h => absurd h (by simp [planeGo])
  | _ :: _, _ :: _, [], h => absurd h (by simp [planeGo])
  | s :: ss, ⟨bs⟩ :: Bs, ⟨ps⟩ :: Ps, h => by
    have e : planeGo (s :: ss) (⟨bs⟩ :: Bs) (⟨ps⟩ :: Ps) =
        bAnd(planeL s bs ps, planeGo ss Bs Ps) := rfl
    rw [e] at h
    obtain ⟨h1, h2⟩ := band_true h
    obtain ⟨ih1, ih2, ih3⟩ := planeGo_sound ss Bs Ps h2
    refine ⟨by simp [ih1], by simp [ih2], fun i hi => ?_⟩
    rcases i with _ | i
    · exact h1
    · simpa [List.getD_cons_succ] using ih3 i (by simpa using hi)

theorem nthA_eq : ∀ (cs : List (List (Array Nat))) (c : Nat), nthA cs c = cs.getD c []
  | [], _ => by
    change [] = _
    simp
  | _ :: _, 0 => rfl
  | _ :: cs, c + 1 => by
    rw [List.getD_cons_succ]
    exact nthA_eq cs c

theorem testBit_exGo (s : Nat) : ∀ (es : List Nat) (k T : Nat), (exGo s es k).testBit T =
    (List.range es.length).any fun j => es.getD j 0 == T && s.testBit (k + j)
  | [], k, T => by
    change (0 : Nat).testBit T = _
    simp
  | e :: es, k, T => by
    change (Nat.lor (Nat.shiftLeft (Nat.land (Nat.shiftRight s k) 1) e)
      (exGo s es (Nat.succ k))).testBit T = _
    rw [fld_one_eq, Nat.lor_eq, Nat.testBit_or, testBit_bitShift, testBit_exGo s es,
      List.length_cons, List.range_succ_eq_map, List.any_cons, List.any_map]
    congr 1
    · by_cases h : e = T
      · subst h
        cases s.testBit k <;> simp
      · have h' : T ≠ e := fun x => h x.symm
        cases s.testBit k <;> simp [h, h', beq_false_of_ne h, beq_false_of_ne h']
    · congr 1
      funext j
      simp [List.getD_cons_succ, Nat.add_assoc, Nat.add_comm 1 j]

end CFSG.KD.SmithD6

end
