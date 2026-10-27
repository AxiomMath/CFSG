module

public import CFSG.Certificates.Kernel.Misc.HypSoundLine
public import Certificates.Data.Kernel.Misc.Hyp

public section

set_option exponentiation.threshold 10000

namespace CFSG.KC.Misc.Hyp

open CFSG.F4.Native CFSG.Sporadic.Th.Native CFSG.Fischer.Native CFSG.KC.Misc.T46
  CFSG.KC.Misc.Lines CFSG.KC.Misc.Xi CFSG.KS.PK CFSG.KC.Ord CFSG.KC.LQT.P CFSG.KC.Misc
  CFSG.KC.Misc.O73 CFSG.KS.TW

private lemma testBit_recLor_base (g : Nat → Nat) (b n j : Nat) :
    (Nat.rec (motive := fun _ => Nat) b (fun i acc => Nat.lor acc (Nat.shiftLeft 1 (g i)))
      n).testBit j = (b.testBit j || (List.range n).any (fun i => decide (g i = j))) := by
  induction n with
  | zero => simp
  | succ n ih =>
    show (Nat.lor (Nat.rec (motive := fun _ => Nat) b (fun i acc => Nat.lor acc
      (Nat.shiftLeft 1 (g i))) n) (Nat.shiftLeft 1 (g n))).testBit j = _
    rw [Nat.lor_eq, Nat.testBit_or, ih,
      show Nat.shiftLeft 1 (g n) = 2 ^ g n from Nat.one_shiftLeft _, Nat.testBit_two_pow,
      List.range_succ, List.any_append, List.any_cons, List.any_nil, Bool.or_false, Bool.or_assoc]

private lemma testBit_recLor (g : Nat → Nat) (l : List Nat) (acc j : Nat) :
    (List.rec (motive := fun _ => Nat) acc (fun v _ ih => Nat.lor ih
      (Nat.shiftLeft 1 (g v))) l).testBit j =
      (acc.testBit j || l.any (fun v => decide (g v = j))) := by
  induction l with
  | nil => simp
  | cons v t ih =>
    show (Nat.lor (List.rec (motive := fun _ => Nat) acc (fun v _ ih => Nat.lor ih
      (Nat.shiftLeft 1 (g v))) t) (Nat.shiftLeft 1 (g v))).testBit j = _
    rw [Nat.lor_eq, Nat.testBit_or, ih,
      show Nat.shiftLeft 1 (g v) = 2 ^ g v from Nat.one_shiftLeft _, Nat.testBit_two_pow,
      List.any_cons, Bool.or_assoc]
    exact congrArg (fun x => acc.testBit j || x)
      (Bool.or_comm (t.any (fun x => decide (g x = j))) (decide (g v = j)))

private lemma testBit_clStepK_aux (TP : Nat → Nat) (M N : List Nat) (F j : Nat) :
    (List.rec (motive := fun _ => Nat) F (fun u _ ih => List.rec (motive := fun _ => Nat) ih
      (fun v _ ih2 => Nat.lor ih2 (Nat.shiftLeft 1 (fd 10 (TP u) v))) N) M).testBit j =
      (F.testBit j || M.any (fun u => N.any (fun v => decide (fd 10 (TP u) v = j)))) := by
  induction M generalizing F with
  | nil => simp
  | cons a t ih =>
    show (List.rec (motive := fun _ => Nat) (List.rec (motive := fun _ => Nat) F
      (fun u _ ih => List.rec (motive := fun _ => Nat) ih
        (fun v _ ih2 => Nat.lor ih2 (Nat.shiftLeft 1 (fd 10 (TP u) v))) N) t)
      (fun v _ ih2 => Nat.lor ih2 (Nat.shiftLeft 1 (fd 10 (TP a) v))) N).testBit j = _
    rw [testBit_recLor, ih, List.any_cons, Bool.or_assoc]
    exact congrArg (fun x => F.testBit j || x)
      (Bool.or_comm (t.any (fun u => N.any (fun v => decide (fd 10 (TP u) v = j))))
        (N.any (fun v => decide (fd 10 (TP a) v = j))))

private lemma letB'_gen (k : List Nat → Nat) (l : List Nat) : ∀ acc : List Nat,
    (List.rec (motive := fun _ => List Nat → Nat) (fun acc => k acc.reverse)
      (fun x _ ih acc => letN x fun x => ih (List.cons x acc)) l) acc = k (acc.reverse ++ l) := by
  induction l with
  | nil => intro acc; simp
  | cons x l ih =>
    intro acc
    refine (letN_eq _ _).trans ?_
    rw [ih (List.cons x acc)]
    simp

private lemma letB'_eq (l : List Nat) (k : List Nat → Nat) : clStepK.letB' l k = k l := by
  unfold clStepK.letB'
  have := letB'_gen k l []
  simpa using this

private lemma testBit_clStepK (TP : Nat → Nat) (F j : Nat) :
    (clStepK TP F).testBit j =
      (F.testBit j || (membersK F).any (fun u =>
        (membersK F).any (fun v => decide (fd 10 (TP u) v = j)))) := by
  rw [clStepK.eq_1, letB'_eq]
  simp only [letN_eq, at'_eq]
  exact testBit_clStepK_aux TP (membersK F) (membersK F) F j

private lemma mem_membersK_aux (S n p : Nat) :
    p ∈ Nat.rec (motive := fun _ => List Nat) []
      (fun q acc => Bool.rec (motive := fun _ => List Nat) acc (q :: acc) (bitK S q)) n ↔
      p < n ∧ bitK S p = true := by
  induction n generalizing p with
  | zero => simp
  | succ n ih =>
    show p ∈ Bool.rec (motive := fun _ => List Nat)
      (Nat.rec (motive := fun _ => List Nat) [] (fun q acc => Bool.rec (motive := fun _ => List Nat)
        acc (q :: acc) (bitK S q)) n)
      (n :: Nat.rec (motive := fun _ => List Nat) [] (fun q acc => Bool.rec
        (motive := fun _ => List Nat) acc (q :: acc) (bitK S q)) n) (bitK S n) ↔
      p < n + 1 ∧ bitK S p = true
    rw [Bool.rec_eq]
    by_cases hb : bitK S n = true
    · rw [if_pos hb, List.mem_cons, ih]
      constructor
      · rintro (rfl | ⟨h1, h2⟩)
        · exact ⟨by omega, hb⟩
        · exact ⟨by omega, h2⟩
      · rintro ⟨h1, h2⟩
        rcases Nat.lt_succ_iff_lt_or_eq.1 h1 with h1 | rfl
        · exact Or.inr ⟨h1, h2⟩
        · exact Or.inl rfl
    · rw [if_neg hb, ih]
      have hb' : bitK S n = false := by simpa using hb
      constructor
      · intro h
        exact ⟨by omega, h.2⟩
      · rintro ⟨h1, h2⟩
        rcases Nat.lt_succ_iff_lt_or_eq.1 h1 with h1 | rfl
        · exact ⟨h1, h2⟩
        · rw [hb'] at h2
          exact absurd h2 (by simp)

private lemma mem_membersK {S p : Nat} :
    p ∈ membersK S ↔ p < 693 ∧ S.testBit p = true := by
  unfold membersK
  rw [mem_membersK_aux, bitK_eq_testBit]

private lemma foldl_setB_size (P : List Nat) (g : Nat → Nat) (F : Flags) :
    (P.foldl (fun a p => a.set! (g p) true) F).size = F.size := by
  induction P generalizing F with
  | nil => rfl
  | cons p t ih => rw [List.foldl_cons, ih, Array.size_set!]

private lemma foldl_setB_get (P : List Nat) :
    ∀ (F : Flags), (∀ p ∈ P, p < 693) → F.size = 693 → ∀ {j : Nat}, j < 693 →
      (P.foldl (fun a p => a.set! p true) F)[j]! = (F[j]! || decide (j ∈ P)) := by
  induction P with
  | nil => intro F _ _ j _; simp
  | cons p t ih =>
    intro F hP hF j hj
    rw [List.foldl_cons,
      ih (F.set! p true) (fun q hq => hP q (List.mem_cons_of_mem _ hq))
        (by rw [Array.size_set!, hF]) hj]
    have hp : p < 693 := hP p List.mem_cons_self
    have hset : (F.set! p true)[j]! = (F[j]! || decide (j = p)) := by
      by_cases hjp : j = p
      · rw [hjp, Array.getElem!_set!_self F p true (by rw [hF]; exact hp)]
        simp
      · rw [Array.getElem!_set!_ne F p j true (fun h => hjp h.symm)]
        have : decide (j = p) = false := by simp [hjp]
        rw [this, Bool.or_false]
    simp only [hset, List.mem_cons, Bool.decide_or, Bool.or_assoc]

private lemma foldl_map_set (N : List Nat) (f : Nat → Nat) (F : Flags) :
    N.foldl (fun a v => a.set! (f v) true) F = (N.map f).foldl (fun a p => a.set! p true) F := by
  rw [List.foldl_map]

private lemma any_eq_decide_mem (l : List Nat) (f : Nat → Nat) (j : Nat) :
    l.any (fun v => decide (f v = j)) = decide (j ∈ l.map f) := by
  rw [Bool.eq_iff_iff, List.any_eq_true, decide_eq_true_iff, List.mem_map]
  simp only [decide_eq_true_iff]

private lemma any_range_map_eq (z x : Nat → Nat) (p : Nat) (h : ∀ i < 5, z i = x i) :
    (List.range 5).any (fun i => p == z i) = (List.range 5).any (fun i => decide (x i = p)) := by
  rw [Bool.eq_iff_iff, List.any_eq_true, List.any_eq_true]
  constructor
  · rintro ⟨i, hi, hq⟩
    rw [List.mem_range] at hi
    simp only [beq_iff_eq] at hq
    exact ⟨i, List.mem_range.2 hi, decide_eq_true_iff.2 (by rw [← h i hi]; exact hq.symm)⟩
  · rintro ⟨i, hi, hq⟩
    rw [List.mem_range] at hi
    simp only [decide_eq_true_iff] at hq
    exact ⟨i, List.mem_range.2 hi, beq_iff_eq.2 (by rw [h i hi]; exact hq.symm)⟩

private lemma clStepG_M_get (U : Array Nat) :
    ∀ (M N : List Nat) (F : Flags), (∀ p ∈ M, p < 693) → (∀ p ∈ N, p < 693) →
      (∀ u ∈ M, ∀ v ∈ N, ap ((tvTabsG U)[u]!) v < 693) → F.size = 693 →
      ∀ {j : Nat}, j < 693 →
      (M.foldl (fun a u => N.foldl (fun a v => a.set! (ap ((tvTabsG U)[u]!) v) true) a)
        F)[j]! =
      (F[j]! || M.any (fun u => N.any (fun v => decide (ap ((tvTabsG U)[u]!) v = j)))) := by
  intro M
  induction M with
  | nil => intro N F _ _ _ _ j _; simp
  | cons a t ih =>
    intro N F hM hN hT hF j hj
    rw [List.foldl_cons]
    have hsize : (N.foldl (fun acc v => acc.set! (ap ((tvTabsG U)[a]!) v) true) F).size = 693 := by
      rw [foldl_setB_size, hF]
    rw [ih N (N.foldl (fun acc v => acc.set! (ap ((tvTabsG U)[a]!) v) true) F)
      (fun q hq => hM q (List.mem_cons_of_mem a hq)) hN
      (fun u hu v hv => hT u (List.mem_cons_of_mem a hu) v hv) hsize hj]
    have hinner : (N.foldl (fun acc v => acc.set! (ap ((tvTabsG U)[a]!) v) true) F)[j]! =
        (F[j]! || N.any (fun v => decide (ap ((tvTabsG U)[a]!) v = j))) := by
      rw [foldl_map_set N (fun v => ap ((tvTabsG U)[a]!) v) F]
      rw [foldl_setB_get (N.map (fun v => ap ((tvTabsG U)[a]!) v)) F
        (fun q hq => by
          obtain ⟨v, hv, rfl⟩ := List.mem_map.1 hq
          exact hT a List.mem_cons_self v hv)
        hF hj, ← any_eq_decide_mem]
    rw [hinner, List.any_cons, Bool.or_assoc]

private lemma clStepG_M_size (U : Array Nat) :
    ∀ (M N : List Nat) (F : Flags),
      (M.foldl (fun a u => N.foldl (fun a v => a.set! (ap ((tvTabsG U)[u]!) v) true) a)
        F).size = F.size := by
  intro M
  induction M with
  | nil => intro N F; rfl
  | cons a t ih =>
    intro N F
    rw [List.foldl_cons, ih N]
    exact foldl_setB_size N (fun v => ap ((tvTabsG U)[a]!) v) F

private lemma clStepG_size (U : Array Nat) (F : Flags) : (clStepG U F).size = F.size := by
  unfold clStepG
  dsimp only
  exact clStepG_M_size U (members F) (members F) F

private lemma clStepG_get {UL : List Nat} {TP : Nat → Nat}
    (hTR : ∀ f < 693, TR 693 ((tvTabsG UL.toArray)[f]!) (fd 10 (TP f)))
    (F : Flags) (hF : F.size = 693) {j : Nat} (hj : j < 693) :
    (clStepG UL.toArray F)[j]! =
      (F[j]! || (members F).any (fun u =>
        (members F).any (fun v => decide (ap ((tvTabsG UL.toArray)[u]!) v = j)))) := by
  unfold clStepG
  dsimp only
  refine clStepG_M_get UL.toArray (members F) (members F) F ?_ ?_ ?_ hF hj
  · intro p hp
    exact (mem_members.1 hp).1
  · intro p hp
    exact (mem_members.1 hp).1
  · intro u hu v hv
    have hu693 : u < 693 := (mem_members.1 hu).1
    have hv693 : v < 693 := (mem_members.1 hv).1
    rw [((hTR u hu693).2 v hv693).1]
    exact ((hTR u hu693).2 v hv693).2

private lemma fl_clStepK {UL : List Nat} {TP : Nat → Nat}
    (hTR : ∀ f < 693, TR 693 ((tvTabsG UL.toArray)[f]!) (fd 10 (TP f))) (F : Nat) :
    fl (clStepK TP F) = clStepG UL.toArray (fl F) := by
  symm
  refine flags_eq ?_ ?_
  · rw [clStepG_size, fl_size]
  · intro j hj
    have hinner : ∀ u < 693, (membersK F).any (fun v => decide (fd 10 (TP u) v = j)) =
        (members (fl F)).any (fun v => decide (ap ((tvTabsG UL.toArray)[u]!) v = j)) := by
      intro u hu
      rw [Bool.eq_iff_iff, List.any_eq_true, List.any_eq_true]
      constructor
      · rintro ⟨v, hv, hq⟩
        exact ⟨v, mem_members_fl.2 (mem_membersK.1 hv),
          by rw [((hTR u hu).2 v (mem_membersK.1 hv).1).1]; exact hq⟩
      · rintro ⟨v, hv, hq⟩
        exact ⟨v, mem_membersK.2 (mem_members_fl.1 hv),
          by rw [← ((hTR u hu).2 v (mem_members_fl.1 hv).1).1]; exact hq⟩
    have houter : (membersK F).any (fun u => (membersK F).any
          (fun v => decide (fd 10 (TP u) v = j))) =
        (members (fl F)).any (fun u => (members (fl F)).any
          (fun v => decide (ap ((tvTabsG UL.toArray)[u]!) v = j))) := by
      rw [Bool.eq_iff_iff, List.any_eq_true, List.any_eq_true]
      constructor
      · rintro ⟨u, hu, hq⟩
        refine ⟨u, mem_members_fl.2 (mem_membersK.1 hu), ?_⟩
        rw [← hinner u (mem_membersK.1 hu).1]
        exact hq
      · rintro ⟨u, hu, hq⟩
        refine ⟨u, mem_membersK.2 (mem_members_fl.1 hu), ?_⟩
        rw [hinner u (mem_members_fl.1 hu).1]
        exact hq
    rw [clStepG_get hTR (fl F) (fl_size F) hj, testBit_clStepK, fl_get F hj, houter]

private lemma step_getD (UP PP j i s : Nat) :
    Bool.rec (Bool.rec (Bool.rec (Nat.div (line3 UP PP 0 s) 1048576)
        (Nat.mod (Nat.div (line3 UP PP 0 s) 1024) 1024) (((j.div (Nat.pow 4 i)).mod 4).beq 2))
      (Nat.mod (line3 UP PP 0 s) 1024) (((j.div (Nat.pow 4 i)).mod 4).beq 1)) s
      (((j.div (Nat.pow 4 i)).mod 4).beq 0) =
      (lineL UP PP 0 s).getD (1 + j / 4 ^ i % 4) 0 := by
  set d := (j.div (Nat.pow 4 i)).mod 4 with hd
  have hd' : j / 4 ^ i % 4 = d := by
    rw [hd]
    rfl
  rw [hd']
  have hd4 : d < 4 := by rw [hd]; exact Nat.mod_lt _ (by norm_num)
  interval_cases d <;> simp [lineL, line3_a, line3_b, line3_c]

private lemma startK_testBit {selL : List Nat} {UP PP : Nat} (j p : Nat) :
    (startK UP PP selL j).testBit p =
      (decide (p = 0) || (List.range 5).any (fun i => decide
        ((lineL UP PP 0 (selL.getD i 0)).getD (1 + j / 4 ^ i % 4) 0 = p))) := by
  rw [startK.eq_1]
  simp only [letN_eq, nthN_eq]
  rw [testBit_recLor_base]
  have h1 : (1 : Nat).testBit p = decide (p = 0) := by
    rw [show (1 : Nat) = 2 ^ 0 from rfl, Nat.testBit_two_pow]
    exact decide_eq_decide.2 eq_comm
  rw [h1]
  congr 1
  apply List.any_congr rfl
  intro i
  rw [step_getD UP PP j i (selL.getD i 0)]

private lemma getElem!_map {α β : Type} [Inhabited α] [Inhabited β] (f : α → β) (a : Array α)
    (i : Nat) (h : i < a.size) : (a.map f)[i]! = f a[i]! := by
  have h' : i < (a.map f).size := by rw [Array.size_map]; exact h
  rw [getElem!_pos (a.map f) i h', getElem!_pos a i h, Array.getElem_map f h']

private lemma startK_fl {UL selL : List Nat} {UP PP : Nat} (H : Pts UL UP PP)
    (hlen : selL.length = 5) (hsel : ∀ s ∈ selL, s < 693) (j : Nat) :
    fl (startK UP PP selL j) = lamStart (selL.toArray.map (lineCG UL.toArray 0)) j := by
  symm
  refine flags_eq (by simp [lamStart]) ?_
  intro p hp
  rw [startK_testBit j p]
  unfold lamStart
  rw [getElem!_pos _ _ (by simpa using hp), Array.getElem_ofFn]
  dsimp only
  have hmap : ∀ i < 5,
      ((selL.toArray.map (lineCG UL.toArray 0))[i]!)[1 + j / 4 ^ i % 4]! =
      (lineL UP PP 0 (selL.getD i 0)).getD (1 + j / 4 ^ i % 4) 0 := by
    intro i hi
    have hi5 : i < selL.length := by omega
    have hy : selL.getD i 0 < 693 := by
      rw [List.getD_eq_getElem _ _ hi5]
      exact hsel _ (List.getElem_mem hi5)
    have h1 : (selL.toArray.map (lineCG UL.toArray 0))[i]! =
        lineCG UL.toArray 0 (selL.getD i 0) := by
      rw [getElem!_map (lineCG UL.toArray 0) selL.toArray i
        (by rw [List.size_toArray]; omega), list_toArray_getElem!]
    rw [h1, lineCG_eq H (by norm_num) hy, list_toArray_getElem!]
  have h0 : (p == 0) = decide (p = 0) := by
    by_cases h : p = 0 <;> simp [h, beq_iff_eq]
  rw [h0]
  congr 1
  exact any_range_map_eq (fun i =>
      ((selL.toArray.map (lineCG UL.toArray 0))[i]!)[1 + j / 4 ^ i % 4]!)
    (fun i => (lineL UP PP 0 (selL.getD i 0)).getD (1 + j / 4 ^ i % 4) 0) p hmap

theorem lamTabG_eq {UL selL : List Nat} {UP PP : Nat} {TP LB : Nat → Nat} (H : Pts UL UP PP)
    (hTR : ∀ f < 693, TR 693 ((tvTabsG UL.toArray)[f]!) (fd 10 (TP f)))
    (hlen : selL.length = 5) (hsel : ∀ s ∈ selL, s < 693)
    (hlam : ∀ k < 32, lamK UP PP TP LB selL (32 * k) 32 = true) :
    lamTabG UL.toArray selL.toArray = Array.ofFn (n := 1024) fun j => fl (LB j) := by
  apply Array.ext
  · simp [lamTabG]
  · intro j hj1 hj2
    have hj : j < 1024 := by simpa using hj2
    simp only [lamTabG, Array.getElem_ofFn]
    have hLB : LB j = clStepK TP (clStepK TP (clStepK TP (startK UP PP selL j))) := by
      have h1 := hlam (j / 32) (by omega)
      unfold lamK at h1
      rw [allN_lqt_iff] at h1
      have h2 := h1 (j % 32) (by omega)
      rw [letB_eq] at h2
      have e : Nat.add (32 * (j / 32)) (j % 32) = j := by
        rw [show Nat.add (32 * (j / 32)) (j % 32) = 32 * (j / 32) + j % 32 from rfl,
          Nat.add_comm]
        exact Nat.mod_add_div j 32
      rw [e] at h2
      rw [impB_eq, Nat.blt_eq.mpr (by omega : j < 1024)] at h2
      simp only [Bool.not_true, Bool.false_or] at h2
      rw [Nat.beq_eq] at h2
      exact h2
    rw [hLB, fl_clStepK hTR, fl_clStepK hTR, fl_clStepK hTR, startK_fl H hlen hsel j]
    rfl

end CFSG.KC.Misc.Hyp

end
