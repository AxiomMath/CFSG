module

public import Certificates.Data.Kernel.HMathieu.PickE
public import CFSG.Certificates.Kernel.HMathieu.PickKSound
public import CFSG.Certificates.Kernel.HMathieu.GreedyPSound
public import CFSG.Certificates.Kernel.HMathieu.FixTabSound

public section

namespace CFSG.KC.HMathieu

open CFSG.Quasithin.H.Mathieu CFSG.QuasithinUnique.Setup.X1

theorem testBit_of_two_pow_le {k y : Nat} (h1 : 2 ^ k ≤ y) (h2 : y < 2 ^ (k + 1)) :
    y.testBit k = true := by
  have hy : y = 2 ^ k + (y - 2 ^ k) := by omega
  have hlt : y - 2 ^ k < 2 ^ k := by
    rw [Nat.pow_succ] at h2
    omega
  rw [hy, Nat.testBit_two_pow_add_eq, Nat.testBit_lt_two_pow hlt]
  rfl

theorem xor_lt_of_two_pow_le {k x b : Nat} (hx1 : 2 ^ k ≤ x) (hx2 : x < 2 ^ (k + 1))
    (hb1 : 2 ^ k ≤ b) (hb2 : b < 2 ^ (k + 1)) : x ^^^ b < 2 ^ k := by
  apply Nat.lt_pow_two_of_testBit
  intro i hi
  rw [Nat.testBit_xor]
  rcases Nat.eq_or_lt_of_le hi with rfl | hi
  · rw [testBit_of_two_pow_le hx1 hx2, testBit_of_two_pow_le hb1 hb2]
    rfl
  · have hp : 2 ^ (k + 1) ≤ 2 ^ i := Nat.pow_le_pow_right (by norm_num) hi
    rw [Nat.testBit_lt_two_pow (lt_of_lt_of_le hx2 hp),
      Nat.testBit_lt_two_pow (lt_of_lt_of_le hb2 hp)]
    rfl

theorem reduceBy_ladder : ∀ (n : Nat) (bs : List Nat) (x : Nat), ladderB n bs = true →
    x < 2 ^ n → reduceBy bs x = 0
  | 0, [], x, _, hx => by
    simp only [reduceBy, List.foldl_nil]
    simpa using hx
  | n + 1, b :: bs, x, h, hx => by
    simp only [ladderB, Bool.and_eq_true, Nat.ble_eq, Nat.blt_eq] at h
    have e : reduceBy (b :: bs) x = reduceBy bs (min x (x ^^^ b)) := by
      simp only [reduceBy, List.foldl_cons]
    rw [e]
    refine reduceBy_ladder n bs _ h.2 ?_
    by_cases hx' : x < 2 ^ n
    · exact lt_of_le_of_lt (min_le_left _ _) hx'
    · exact lt_of_le_of_lt (min_le_right _ _)
        (xor_lt_of_two_pow_le (Nat.le_of_not_lt hx') hx h.1.1 h.1.2)
  | 0, _ :: _, _, h, _ => by simp [ladderB] at h
  | _ + 1, [], _, h, _ => by simp [ladderB] at h

theorem reduceK_ladder {n : Nat} {bs : List Nat} (h : ladderB n bs = true) {x : Nat}
    (hx : x < 2 ^ n) : reduceK bs x = 0 := by
  rw [reduceK_eq]
  exact reduceBy_ladder n bs x h hx

theorem stepK_ladder {n : Nat} {st : List Nat × List Nat} (h : ladderB n st.1 = true) {v : Nat}
    (hv : v < 2 ^ n) : stepK st v = st := by
  unfold stepK
  rw [reduceK_ladder h hv]
  rfl

theorem foldl_stepK_ladder {n : Nat} : ∀ (vs : List Nat) (st : List Nat × List Nat),
    ladderB n st.1 = true → (∀ v ∈ vs, v < 2 ^ n) → vs.foldl stepK st = st
  | [], _, _, _ => rfl
  | v :: vs, st, h, hv => by
    rw [List.foldl_cons, stepK_ladder h (hv v List.mem_cons_self)]
    exact foldl_stepK_ladder vs st h fun w hw => hv w (List.mem_cons_of_mem v hw)

theorem pickEFrom_cons (n v : Nat) (vs : List Nat) (st : List Nat × List Nat) :
    pickEFrom n (v :: vs) st =
      bif Nat.beq st.1.length n then st else pickEFrom n vs (stepK st v) := rfl

theorem foldl_eq_pickEFrom {n : Nat} : ∀ (vs : List Nat) (st : List Nat × List Nat),
    (∀ v ∈ vs, v < 2 ^ n) →
    ((pickEFrom n vs st).1.length = n → ladderB n (pickEFrom n vs st).1 = true) →
    vs.foldl stepK st = pickEFrom n vs st
  | [], _, _, _ => rfl
  | v :: vs, st, hv, h => by
    rw [List.foldl_cons]
    rw [pickEFrom_cons] at h ⊢
    cases hb : Nat.beq st.1.length n
    · rw [hb, cond_false] at h
      rw [cond_false]
      exact foldl_eq_pickEFrom vs _ (fun w hw => hv w (List.mem_cons_of_mem v hw)) h
    · rw [hb, cond_true] at h
      rw [cond_true]
      have hl := h (Nat.eq_of_beq_eq_true hb)
      rw [stepK_ladder hl (hv v List.mem_cons_self)]
      exact foldl_stepK_ladder vs st hl fun w hw => hv w (List.mem_cons_of_mem v hw)

theorem pickE_eq {n r : Nat} {vs : List Nat} (hv : ∀ v ∈ vs, v < 2 ^ n)
    (h : testE n r vs = true) : indepCheck r vs (pickBasis vs) = true := by
  unfold testE at h
  rw [Bool.and_eq_true] at h
  obtain ⟨h1, h2⟩ := h
  have e : pickBasis vs = (pickE n vs).2 := by
    rw [← pickK_eq]
    change (vs.foldl stepK ([], [])).2 = (pickEFrom n vs ([], [])).2
    rw [foldl_eq_pickEFrom vs _ hv fun hl => ?_]
    change (pickE n vs).1.length = n at hl
    rw [hl, Nat.beq_refl] at h1
    simp only [Bool.not_true, Bool.false_or] at h1
    exact h1
  rw [e]
  exact indepCheck_of_indepK h2

variable {P : Type*} [Group P] [DecidableEq P]

theorem xiCands_lt {n : Nat} {act : P → Nat → Nat} {l : List P} :
    ∀ v ∈ xiCands n act l, v < 2 ^ n := by
  intro v hv
  simp only [xiCands, List.mem_flatMap] at hv
  obtain ⟨_, _, hv⟩ := hv
  exact (mem_fixMasks.1 hv).1

theorem pairCands_lt {n : Nat} {act : P → Nat → Nat} {l : List P} :
    ∀ v ∈ pairCands n act l, v < 2 ^ n := by
  intro v hv
  simp only [pairCands, List.mem_flatMap] at hv
  obtain ⟨_, _, _, _, hv⟩ := hv
  exact (mem_fixMasks.1 hv).1

theorem xiCheck_of_testE {n r : Nat} {act : P → Nat → Nat} {l : List P}
    (h : testE n r (xiCands n act l) = true) : xiCheck n r act l = true :=
  pickE_eq xiCands_lt h

theorem pairCheck_of_testE {n r : Nat} {act : P → Nat → Nat} {l : List P}
    (h : testE n r (pairCands n act l) = true) : pairCheck n r act l = true :=
  pickE_eq pairCands_lt h

omit [Group P] [DecidableEq P] in
theorem fixMasks_pair (n : Nat) (act : P → Nat → Nat) (s t : P) :
    fixMasks n act [s, t] = (fixMasks n act [s]).filter fun m => act t m == m := by
  unfold fixMasks
  rw [List.filter_filter]
  refine List.filter_congr fun m _ => ?_
  simp only [List.all_cons, List.all_nil, Bool.and_true]
  exact Bool.and_comm _ _

theorem flatMap_congr_of_mem {α β : Type*} {f g : α → List β} :
    ∀ {l : List α}, (∀ a ∈ l, f a = g a) → l.flatMap f = l.flatMap g
  | [], _ => rfl
  | a :: l, h => by
    rw [List.flatMap_cons, List.flatMap_cons, h a List.mem_cons_self,
      flatMap_congr_of_mem fun b hb => h b (List.mem_cons_of_mem a hb)]

theorem pairCands_eq {R : List P} {cmR mkR : Nat → Nat} (T : GTabs R cmR mkR) {l : List P}
    (hci : IsCommInvol l) {F Mc : List (List Nat)} {n : Nat} {act : P → Nat → Nat}
    (hF : ∀ s ∈ R, F.getD (R.idxOf s) [] = fixMasks n act [s])
    (hM : ∀ t ∈ R, act t = actM (Mc.getD (R.idxOf t) [])) :
    pairCands n act l = pairCandsT Mc F R.length ((subprods l).map R.idxOf) := by
  have hfilt : ∀ (A : List P), (∀ a ∈ A, a ∈ R ∨ a = 1) → ∀ u : P, (u ∈ R ∨ u = 1) →
      (A.map R.idxOf).filter (· != R.idxOf u) = (A.filter (· ≠ u)).map R.idxOf := by
    intro A hA u hu
    rw [List.filter_map]
    congr 1
    refine List.filter_congr fun a ha => ?_
    rw [Bool.eq_iff_iff]
    simp only [Function.comp_apply, bne_iff_ne, ne_eq, decide_eq_true_eq]
    exact ⟨fun h e => h (by rw [e]), fun h e => h (idxOf_inj T (hA a ha) hu e)⟩
  have hS : ∀ s ∈ subprods l, s ∈ R ∨ s = 1 := fun s hs => mem_or_one_of_subprods T hci hs
  have h1 : R.idxOf (1 : P) = R.length := List.idxOf_eq_length (one_notMem T)
  unfold pairCands pairCandsT pairCandsL
  dsimp only
  rw [← h1, hfilt _ hS 1 (Or.inr rfl), List.flatMap_map]
  set S1 := (subprods l).filter (· ≠ 1)
  have hS1 : ∀ s ∈ S1, s ∈ R := fun s hs => by
    rw [List.mem_filter, decide_eq_true_eq] at hs
    exact (hS s hs.1).resolve_right hs.2
  refine flatMap_congr_of_mem fun s hs => ?_
  rw [hfilt S1 (fun a ha => Or.inl (hS1 a ha)) s (Or.inl (hS1 s hs)), List.flatMap_map]
  refine flatMap_congr_of_mem fun t ht => ?_
  have ht' : t ∈ S1 := List.mem_of_mem_filter ht
  rw [fixMasks_pair, hF s (hS1 s hs), hM t (hS1 t ht'), actK_fun]

end CFSG.KC.HMathieu

end
